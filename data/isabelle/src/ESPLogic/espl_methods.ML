(*****************************************************************************
 * ESPL --- an embedded security protocol logic
 *          http://people.inf.ethz.ch/meiersi/espl/
 *
 *   Copyright (c) 2009-2011, Simon Meier, ETH Zurich, Switzerland
 *
 * Extension to compromising adversaries:
 *
 *   Copyright (c) 2010-2011, Martin Schaub, ETH Zurich, Switzerland
 *
 * All rights reserved. See file LICENCE for more information.
 ******************************************************************************)
(* Attributes and proof methods supporting decryption chain reasoning.
   Side effect: Registers the "prefix_close" and "note_prefix_closed" commands. *)

signature ESPL_METHODS =
sig
  (* "sources" proof method *)
  val sources_tac
     : Proof.context -> bool -> term ->
       thm option -> thm list -> int -> thm -> (cases * thm) Seq.seq
  val sourcesP
     : Context.generic * Token.T list ->
       ((bool * term) * thm option) * (Context.generic * Token.T list)

  (* "prefix_close" proof state transformation *)
  val prefix_close_thms: string -> Proof.context -> thm list -> thm list
  val prefix_close_cmd: Proof.state -> Proof.state
  val note_prefix_closed_cmd: Proof.state -> Proof.state

  (* "completeness_cases_rule" attribute *)
  val completeness_cases_attrib: Context.generic -> thm -> thm
end;

structure ESPL_Methods: ESPL_METHODS =
struct

open ESPL_Utils;



(******************************************************************************
**  "sources" proof method
******************************************************************************)

(* Pretty print resolution failure *)
fun err_no_matching_rule ctxt raw_rules knows_thm =
  error (Pretty.string_of (Pretty.block (Pretty.fbreaks
            [ Pretty.str "none of the rules:"
            , Pretty.indent 2 (Proof_Context.pretty_fact ctxt ("", raw_rules))
            , Pretty.str "resolved against:"
            , Pretty.indent 2 (Display.pretty_thm ctxt knows_thm)
            ])))

(* Remove trivial cases,
   insert known facts (except case names), and
   attach case names using Rule_Cases
   to a specialized knows_cases_XXX rule.
*)
fun finalize_knows_cases ctxt minimal facts case_th =
  let
    val is_hint_thm = 
      can (Hints.dest_hint o HOLogic.dest_Trueprop o Thm.prop_of);

    val facts'    = filter (not o is_hint_thm) facts;
    val final_tac = ALLGOALS (
          (if minimal then 
             TRY o Simplifier.full_simp_tac ctxt
           else
             TRY o Method.insert_tac facts' THEN'
             TRY o (
                Clasimp.clarsimp_tac ctxt THEN'
                TRY o Orders.order_tac ctxt []
             )
          )
        );
    fun mk_Rule_Cases_cases th =
      Rule_Cases.get (Rule_Cases.name 
        (ESPL_Definitions.source_case_names th) th)
  in
    case_th
    |> HOL_Ext.refine_rule ctxt (K final_tac)
    |> ` mk_Rule_Cases_cases
  end;

(* The tactic underlying the "sources" proof method *)
fun sources_tac _ _ _ _ [] = (fn _ => fn _ => Seq.empty) (* fail when no facts are chained in *)
 | sources_tac ctxt minimal msg_t opt_raw_rule facts =
  let
    val thy = Proof_Context.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    val raw_rules = case opt_raw_rule of
        SOME th => [th]
      | NONE    => ESPL_Definitions.KnowsCasesCache.get ctxt;

    val _ =
      if null raw_rules then error "no source elimination rules given" else ();

    (* we assume the first premise of every rule is the knows predicate *)
    val knows_ct = 
      hd raw_rules
      |> Thm.prop_of
      |> hd o Logic.strip_imp_prems 
      |> HOLogic.dest_mem o HOLogic.dest_Trueprop
      |> apfst (K msg_t)
      |> HOLogic.mk_Trueprop o HOLogic.mk_mem
      |> cert;

    val predOrd_elim_ths = @{thms in_knows_predOrd1 in_knows_predOrd2}
    val knows_thm = 
      Goal.prove_internal ctxt [] knows_ct 
        (fn facts' => 
        ALLGOALS (Method.insert_tac (facts' @ facts)) THEN
        (ALLGOALS (assume_tac ORELSE' eresolve_tac predOrd_elim_ths)
         ORELSE auto_tac (ctxt addIs predOrd_elim_ths))
        )
      |> simplify ctxt

    val (cases, rule) = 
      case get_first (try (curry (op RS) knows_thm)) raw_rules of
        NONE    => err_no_matching_rule ctxt raw_rules knows_thm
      | SOME th => finalize_knows_cases ctxt minimal facts th
  in
    fn i => fn st =>
      CASES (Rule_Cases.make_common (thy, Thm.prop_of rule) (fst cases)
            )
            (Tactic.rtac rule i) st
  end;

(* Parser for the sources proof method:

     BNF: sources["!"] term ["rule" thm]

   The ! means that a strict mode should be used, where the surrounding facts
   are not passed through automatically.

   The optional theorem can be used to state the rule for the case distinction
   explicitly.
*)
local
  val ruleN = "rule";
  val rule = Scan.lift (Args.$$$ ruleN -- Args.colon) |-- Attrib.thm;
  val opt_bang = Scan.lift (Scan.optional (Parse.$$$ "!" >> K true) false);
in
  val sourcesP = opt_bang -- Args.term -- Scan.option rule;
end;


(******************************************************************************
**  "prefix_close" proof state transformation
******************************************************************************)


fun dest_roleMap_eq t = 
  case HOLogic.dest_eq t of
    (Const (@{const_name roleMap},_) $ r $ i, 
       Const (@{const_name Some},_) $ R) => (r, (i, R))
  | _ => raise TERM ("dest_roleMap_eq", [t])
    

fun dest_in_steps t = 
  case HOLogic.dest_mem t of
    (estep, Const (@{const_name steps}, _) $ t) => 
      (case HOLogic.strip_tuple estep of
        i :: step :: _ => (i, step, t)
      | _ => raise TERM ("dest_MkStep_in_steps",[t]))
  | _ => raise TERM ("dest_MkStep_in_steps",[t])

fun split_conj_thm th =
  (split_conj_thm (th RS @{thm conjunct1}) @
  (split_conj_thm (th RS @{thm conjunct2}))) 
  handle THM _ => [th];

fun derive_step_thms th = map_filter (try (fn rule => th RS rule)) 
  @{thms in_steps_predOrd1 in_steps_predOrd2 steps_in_steps}


(* NOTE: this works only correctly in the context of a reachable_state locale
   as the theorem ext_prefixClose is dependent on this locale.
*)
fun prefix_close_thms qualifier ctxt facts =
  let
    val prefixClose_th = Proof_Context.get_thm ctxt (Long_Name.qualify qualifier "ext_prefixClose");
    fun close step roleMap = [step, roleMap] MRS prefixClose_th;
    val expand = Simplifier.simplify (ctxt addsimps @{thms exec_match_def});
    val distinct_prop = distinct (Thm.eq_thm);
    (* fun new_fact th = 
        forall (not_equal (Thm.prop_of th) o Thm.prop_of) facts; *)
  in
    facts
    |> maps split_conj_thm
    |> maps derive_step_thms
    |> distinct_prop
    |> maps (fn step_th => map_filter (try (close step_th)) facts)
    |> maps (split_conj_thm o expand)
    |> curry (op @) facts
    |> distinct_prop
     (* |> filter new_fact *)
  end;

(* Note all facts derivable from the given theorems using all rules from the
   decryption chain calculus except the chain rule
*)
fun note_prefix_closed_cmd state =
  let val ctxt  = Proof.context_of state;
      val facts = Proof.the_facts state;
      val facts' = facts @ prefix_close_thms "" ctxt facts
  in Proof.set_facts facts' state end

(* A proof state transformation implementing prefix closing of
   the currently used facts.
*)
fun prefix_close_cmd state = 
  let
    val using = state 
      |> Proof.goal
      |> (fn {context = ctxt, facts=using, goal=_} => 
           prefix_close_thms "" ctxt using)

  in Proof.using [[(using,[])]] state end;

(* registering the prefix_close command *)
val _ =
  Outer_Syntax.command @{command_spec "prefix_close"} "prefix close facts being used"
    (Scan.succeed (Toplevel.proof prefix_close_cmd));


(******************************************************************************
**  "completeness_cases" attribute
******************************************************************************)

(* Extract the case name of the premise by checking for the corresponding hint *)
fun extract_completeness_case_name prems = 
  case Hints.gather_by_name "completenessCase" prems of
    (data :: _) => 
      (case HOLogic.strip_tuple data of
        (Const (step_name,_) :: v :: _) => 
          List.last (space_explode "." step_name) ^ "_" ^ HOLogic.dest_string v
       | _ => raise TERM ("extract_completeness_case_name", prems)
       )
  | [] => raise TERM ("extract_completeness_case_name", prems)


(* Return the case names according to the hints *)
fun completeness_case_names th =
  let
    val extract = 
      extract_completeness_case_name o 
      Logic.strip_imp_prems o Term.strip_all_body;
    fun name_of prem = 
      case try extract prem of
        SOME name => name
      | NONE => ESPL_Definitions.unnamed_caseN
  in
    th 
     |> Thm.prop_of
     |> Logic.strip_imp_prems
     |> map name_of
     |> blank_zero_numbers (op =)
     |> map (append_optional_number "_")
  end;

(* Convert the conclusion of a completeness induction rule into elimination
   form and name all the different cases according to the hints. 
*)
fun completeness_cases_attrib ctxt th =
  let
    val ss = Context.proof_of ctxt addsimps @{thms finite_setdiff_compute exec_match_def};
    fun add_case_info th = th
      |> Rule_Cases.add_consumes 0
      |> Rule_Cases.name (completeness_case_names th)

  in 
    th
    |> SINGLE (REPEAT (safe_tac (Context.proof_of ctxt) THEN (TRYALL (full_simp_tac ss))))    
    |> the
    |> add_case_info
  end

end
