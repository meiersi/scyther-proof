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
(*
Commands for role and protocols definitions in the ESPLogic.

Side effect: registers the two definitional commands "role" and "protocol".
*)

signature ESPL_DEFINITIONS =
sig
  (* Additional Utilities *)
  val unnamed_caseN: string

  datatype steptyp = Recv | Send | Note of term
  val mk_rolestep: steptyp * term * term -> term
  val dest_rolestep: term -> steptyp * term * term
  val dest_role: term -> (steptyp * term * term) list
  val dest_variable_store_lookup: term -> term * (term * term)
  val dest_non_refl_eq: typ -> term -> term * term

  val get_unfold_thms: Proof.context -> term -> thm list
  val get_rolestep_msg: Proof.context -> string -> term

  (* Role Definitions *)
 val define_rolestep_cmd
   : string -> Args.src list -> steptyp * term * term -> local_theory -> 
     ((term * thm) * (term * thm)) * local_theory
 
  val define_role_cmd
   : binding * ((binding * Args.src list) * string) -> local_theory ->
     ((term * thm) * ((term * thm) * (term * thm)) list) * local_theory

  (* Protocol Definitions *)
  val define_proto_cmd
   : binding * ((binding * Args.src list) * string) -> local_theory -> 
     (term * thm) * local_theory

  (* Managing the Chain Rule and Its Expansion with Named Cases *)
  structure TypeElimRulesData : GENERIC_DATA
  val lookup_type_elim_rules: Proof.context -> TypeElimRulesData.T

  val insert_case_names: Proof.context -> thm -> thm
  val source_case_names: thm -> string list

  val refine_knows_cases
     : Proof.context -> term option -> thm -> thm
  val prepare_sources_elim: Proof.context -> thm -> term -> thm

  structure KnowsCasesCache : NAMED_THMS
  val precompute_source_elim_rules
     : thm -> Proof.context -> (string * thm list) list * local_theory

  (* Type Invariant Definitions Combined With Chain Rule Expansion *)
  val type_invariant_cmd
   : (binding * string) * ((binding * Args.src list) * string) ->
     local_theory -> local_theory
end;

structure ESPL_Definitions: ESPL_DEFINITIONS =
struct

open ESPL_Utils;

(******************************************************************************
**  Additional Utilities
******************************************************************************)


datatype steptyp = Recv | Send | Note of term;

fun mk_rolestep (Send, lbl, msg) = @{const Send} $ lbl $ msg
  | mk_rolestep (Recv, lbl, msg) = @{const Recv} $ lbl $ msg
  | mk_rolestep (Note nTy, lbl, msg) = @{const Note} $ lbl $ nTy $ msg

fun dest_rolestep (Const (@{const_name Send},_) $ lbl $ msg)       = (Send,     lbl, msg)
  | dest_rolestep (Const (@{const_name Recv},_) $ lbl $ msg)       = (Recv,     lbl, msg)
  | dest_rolestep (Const (@{const_name Note},_) $ lbl $ nTy $ msg) = (Note nTy, lbl, msg)
  | dest_rolestep t = raise TERM ("dest_rolestep", [t])

val dest_role = map dest_rolestep o HOLogic.dest_list

(* Destruct a symbolic representation of the contents
   of a protocol variable. 
*)
fun dest_variable_store_lookup (t as (s $ lv)) =
      if (Term.fastype_of s = @{typ "store"})
      then (case HOLogic.strip_tuple lv of
             [v,tid] => (s, (v,tid))
           | _       => 
             raise TERM ("dest_variable_store_lookup: wrong arity",[t]))
      else raise TERM ("dest_variable_store_lookup: wrong type",[t])
  | dest_variable_store_lookup t = 
      raise TERM ("dest_variable_store_lookup",[t]);


(* Destruct an non-reflexive equality *)
fun dest_non_refl_eq ty t = 
  case HOLogic.dest_eq t of
    eq as (lhs,rhs) => 
      if   lhs = rhs
      then raise TERM ("dest_non_refl_eq: reflexive",[t])
      else 
        if   Term.fastype_of lhs = ty
        then eq
        else raise TYPE ("dest_non_refl_eq:",[ty],[t]);


(* Retrieves the unfold theorems for a constent that were previously stored as
   const_name.unfold. This is not very stable but works for our defintions.

   TODO: Check if there is a more stable machinery for that purpose.
*)
fun get_unfold_thms ctxt (Const (c,_)) = Proof_Context.get_thms ctxt (c ^ ".unfold")
  | get_unfold_thms ctxt (Free  (c,_)) = Proof_Context.get_thms ctxt (c ^ ".unfold")
  | get_unfold_thms _ t = raise TERM ("get_unfold_thms", [t])

(* Lookup the term of the message of a role step *)
fun get_rolestep_msg ctxt step_name = 
  Proof_Context.get_thm ctxt (Thm.def_name (step_name ^ "_pt"))
  |> Thm.prop_of
  |> dest_HOL_def
  |> snd

(* Extract identifiers of message variables in a pattern *)
fun pat_msgvars (Const (@{const_name "PEnc"},_) $ m $ k)  = 
      Ord_List.union fast_string_ord (pat_msgvars m) (pat_msgvars k)
  | pat_msgvars (Const (@{const_name "PTup"},_) $ x $ y)  = 
      Ord_List.union fast_string_ord (pat_msgvars x) (pat_msgvars y)
  | pat_msgvars (Const (@{const_name "PHash"},_) $ x)     = 
      pat_msgvars x
  | pat_msgvars (Const (@{const_name "PSymK"},_) $ a $ b) = 
      Ord_List.union fast_string_ord (pat_msgvars a) (pat_msgvars b)
  | pat_msgvars (Const (@{const_name "PAsymPK"},_) $ a)   =
      pat_msgvars a
  | pat_msgvars (Const (@{const_name "PAsymSK"},_) $ a)   =
      pat_msgvars a
  | pat_msgvars (Const (@{const_name "PFresh"},_) $ _)    = 
      []
  | pat_msgvars (Const (@{const_name "PConst"},_) $ _)    = 
      []
  | pat_msgvars (Const (@{const_name "PVar"},_) $ v)      = 
      (case v of
        (Const (@{const_name AVar},_) $ _) => []
      | (Const (@{const_name MVar},_) $ i) => [HOLogic.dest_string i]
      | _ => []
      )
  | pat_msgvars _ = []


(******************************************************************************
**  Role Definitions
******************************************************************************)

(*
  The "role" definition command defines constants for every message and step of
  the role specification and the role specification itself. Furthermore
  wellformedness of the role and several expansion theorems are proven
  automatically. The theorems "role.unfold" can be used if all these
  intermediate definitions need to be simplified away.
*)

(* proves and notes all the theorems associated to a rolestep *)
fun setup_rolestep mk_binding ann_defs lthy =
  let
    val ((msg_const,msg_def),(step_const,step_def)) = ann_defs;

    val ss_step = lthy addsimps [step_def] |> simpset_of;
    val ss_full = lthy addsimps [step_def, msg_def] |> simpset_of;

    val sendStep_t = @{const sendStep} $ step_const;
    val noteStep_t = @{const noteStep} $ step_const;
    val stepPat_t = @{const stepPat} $ step_const;
    val noteType_t = @{const noteType} $ step_const;

    val inst_t = @{term "inst s i"} $ msg_const;
    val FV_t = @{term "FV"} $ msg_const;
    val FMV_t = @{term "FMV"} $ msg_const;
    val FAV_t = @{term "FAV"} $ msg_const;
  in
   lthy
   (* unfold theorems *)
     |> #2 o Local_Theory.note (mk_binding "unfold", [msg_def,step_def])
   (* step expansions *)
     |> #2 o notes_expansion ss_step
       [ (mk_binding "sendStep_conv", [([sendStep_t],[att_iff_add])]) 
       , (mk_binding "noteStep_conv", [([noteStep_t],[att_iff_add])]) 
       , (mk_binding "stepPat_conv",  [([stepPat_t],[att_simp_add])]) 
       , (mk_binding "noteType_conv",  [([noteType_t],[att_simp_add])])
       ]
   (* full expansions *)
     |> notes_expansion ss_full
       [ (mk_binding "inst_conv", [([inst_t], [att_simp_add])])
       , (mk_binding "FV_conv",   [([FV_t],   [att_simp_add])])
       , (mk_binding "FMV_conv",  [([FMV_t],  [att_simp_add])])
       , (mk_binding "FAV_conv",  [([FAV_t],  [att_simp_add])])
       ]
   (* restore original annotated definitions *)
     |>> K ann_defs
  end

(* defines the constants needed for a rolestep and setups the associated
   theorems using setup_rolestep
*)
fun define_rolestep_cmd prefix srcs (stepty, lbl, msg) lthy =
  let
    val lbl_str = HOLogic.dest_string lbl;

    val step_name = prefix ^ "_" ^ lbl_str;
    val step_const_bind = Binding.name step_name;
    val step_def_bind = (Binding.suffix_name "_def" step_const_bind, srcs);

    val msg_name = step_name ^ "_pt";
    val msg_const_bind = Binding.name msg_name;
    val msg_def_bind = (Binding.suffix_name "_def" msg_const_bind, srcs);
    val msg_def_eq   = Logic.mk_equals (Free (msg_name, @{typ pattern}), msg);
  in
    lthy
     |> Specification.definition 
         ( SOME (msg_const_bind, SOME @{typ pattern}, NoSyn)
         , (msg_def_bind, msg_def_eq) )
     |-> (fn (msg_const, (_, msg_def)) =>
           Specification.definition
             ( SOME (step_const_bind, SOME @{typ rolestep}, NoSyn)
             , ( step_def_bind
               , Logic.mk_equals (Free (step_name, @{typ rolestep}), 
                                  mk_rolestep (stepty, lbl, msg_const))
               ) 
             )
           #>> (fn (step_const, (_, step_def)) =>
                 ((msg_const, msg_def), (step_const, step_def))
               )
         )
     |-> setup_rolestep (fn n => (Binding.qualify true step_name (Binding.name n), srcs))
  end

(* proves and notes all theorems associated to a role *)
fun setup_role mk_binding (defs as ((role_const, role_def), steps)) ctxt =
  let
    val in_set_t = HOLogic.mk_mem (@{term "step :: rolestep"}, 
      @{term "set :: role => rolestep set"} $ role_const);
    val zip_t = 
      @{term "zip :: role => 'a list => (rolestep * 'a) list"}
      $ role_const $ @{term "xs :: 'a list"}
    val splits_t =
      @{term "splits :: role => (role * role) list"} $ role_const

    val pat_defs = map (snd o fst) steps;
    val step_defs = map (snd o snd) steps;
    val step_consts = map (fst o snd) steps;

    val ss_role = ctxt addsimps [role_def, @{thm prefixClose_def}] |> simpset_of;
    val ss_full = ctxt addsimps ([role_def, @{thm prefixClose_def}] @ pat_defs @ step_defs @
      @{thms wf_role_def distinct_list_def wf_role_axioms_def}) |> simpset_of

    fun simp_tactic {prems, context} = FIRSTGOAL (Simplifier.full_simp_tac (put_simpset ss_full context));

    val distinct_steps_thms = prove_distinctness ctxt simp_tactic step_consts;

    val ss_prefixClose = ctxt addsimps ([role_def, @{thm prefixClose_def}] @ distinct_steps_thms) |> simpset_of;

    val wf_goal = HOLogic.mk_Trueprop (@{const wf_role} $ role_const);

    val avars_t = @{const aVars}$ role_const;

    val lastComStep_t = @{const lastComStep} $ role_const;
    val firstComStep_t = @{const firstComStep} $ role_const;

    fun mk_prefixClose_thm ctxt step_def =
      let
        val step = step_def |> Thm.prop_of |> dest_HOL_def |> #1;
        val t =  @{const prefixClose} $ (Free ("s", @{typ store})) $
         (Free ("t", @{typ explicit_trace})) $
         role_const $ step $ (Free ("i", @{typ tid}));
      in expand_term ss_prefixClose ctxt t end

    fun pat_def_msgvars pat_def =
      pat_def |> Thm.prop_of |> dest_HOL_def |> #2 |> pat_msgvars;

    val msgvars = Library.foldl 
      (fn (vs,def) => Ord_List.union fast_string_ord vs (pat_def_msgvars def)) 
      ([],pat_defs);

  in
    ctxt
    (* unfold theorems *)
      |> #2 o Local_Theory.note (mk_binding "unfold", role_def :: step_defs @ pat_defs)
    (* wellformed role *)  
      |> #2 o notes_proven simp_tactic
        [ (mk_binding "wf_role",    [([wf_goal],[att_iff_add])]) ]
    (* distinct steps and prefixClose expansions *)
      |> #2 o (fn ctxt => Local_Theory.notes
        [ (mk_binding "distinct_steps",    [(distinct_steps_thms,[att_iff_add])]) 
        , (mk_binding "prefixClose_convs", 
            [(map (mk_prefixClose_thm ctxt) step_defs, [att_iff_add])])
        ] ctxt)
    (* expansions *)  
      |> notes_expansion ss_role
        [ (mk_binding "in_set_conv", [([in_set_t],[att_iff_add])])
        , (mk_binding "zip_conv",    [([zip_t],[att_simp_add])])
        , (mk_binding "splits_conv", [([splits_t],[att_simp_add])])
        , (mk_binding "avars_conv", [([avars_t],[att_simp_add])])
        , (mk_binding "lastComStep_conv", [([lastComStep_t],[att_simp_add])])
        , (mk_binding "firstComStep_conv", [([firstComStep_t],[att_simp_add])])
        ]
    (* restore definitions *)
      |>> K defs
  end

(* defines a role and setups all associated theorems using setup_role *)
fun define_role_cmd (raw_bind, raw_spec as ((_,srcs),_)) params_ctxt =
  let
    val (([((_,role_ty),_)],[(role_def_bind, role_eq)]), _) =
      Specification.read_free_spec [(raw_bind, SOME "Protocol.role", NoSyn)] 
        [raw_spec] params_ctxt;
    val steps = role_eq |> dest_HOL_def |> #2 |> dest_role;

    fun mk_definition ann_step_defs =
      let
        val role_eq = Logic.mk_equals (role_eq |> dest_HOL_def |> #1,
          HOLogic.mk_list @{typ rolestep} (map (fst o snd) ann_step_defs));
      in
        Specification.definition 
          ( SOME (raw_bind, SOME role_ty, NoSyn)
          , (role_def_bind, role_eq) )
        #>> (fn (role_const,(_,role_def)) => ((role_const,role_def),ann_step_defs))
      end

    val prefix = Binding.name_of raw_bind;
    fun mk_rel_binding name = (Binding.qualify true prefix (Binding.name name), srcs);
  in
    params_ctxt
      |> fold_map (define_rolestep_cmd prefix srcs) steps
      |-> mk_definition
      |-> setup_role mk_rel_binding
  end

(* registering the role definition command as an outer keyword *)
val roledef_parser = 
  Parse.binding --| Parse.where_ -- (Parse_Spec.opt_thm_name ":" -- Parse.prop);

val _ =
  Outer_Syntax.local_theory @{command_spec "role"} "security protocol role definition" 
    (roledef_parser >> (fn spec => define_role_cmd spec #> snd));

(******************************************************************************
**  Protocol Definitions
******************************************************************************)

(* proves and notes all theorems associated to a protocol definition *)
fun setup_proto mk_binding (ann_def as (proto_const, proto_def)) ctxt = 
  let
    val role_consts = proto_def |> Thm.prop_of 
      |> dest_HOL_def |> #2 |> HOLogic.dest_set;
    val role_unfolds = flat (map (get_unfold_thms ctxt) role_consts);

    val proto_ss = ctxt addsimps (proto_def :: @{thms wf_proto_def});
    val full_ss = proto_ss addsimps role_unfolds;

    fun simp_tactic ss = K (FIRSTGOAL (Simplifier.full_simp_tac ss));

    val wf_proto_thm = prove_prop ctxt (simp_tactic proto_ss)
      (HOLogic.mk_Trueprop (@{const wf_proto} $ proto_const));

    val distinct_roles_thms = 
      prove_distinctness ctxt (simp_tactic full_ss) role_consts;

    val in_set_t = HOLogic.mk_mem (@{term "R :: role"}, proto_const);

  in 
    ctxt 
    (* unfolds, distinct roles, and wf_proto *)
      |> #2 o Local_Theory.notes
        [ (mk_binding "unfold",         [(proto_def :: role_unfolds, [])]) 
        , (mk_binding "distinct_roles", [(distinct_roles_thms,[att_iff_add])]) 
        , (mk_binding "wf_proto",       [([wf_proto_thm], [att_iff_add])])
        ]
    (* expansions *)  
      |> #2 o notes_expansion (proto_ss |> simpset_of)
        [ (mk_binding "in_set_conv",    [([in_set_t],[att_iff_add])])
        ]
    (* restore annotated definition *)
      |> pair ann_def
  end;

fun define_proto_cmd (raw_bind, raw_spec as ((_,srcs),_)) params_ctxt =
  let
    val ((proto_const, (_, proto_def)), spec_ctxt) = params_ctxt 
      |> Specification.definition_cmd 
        (SOME (raw_bind, SOME "Protocol.proto", NoSyn), raw_spec) true;

    val proto_name          = Binding.name_of raw_bind;
    fun mk_rel_binding name = 
      (Binding.qualify true proto_name (Binding.name name), srcs);
  in
    setup_proto mk_rel_binding (proto_const, proto_def) spec_ctxt
    |> apsnd (Local_Theory.raw_theory (fn thy =>
        let
          val locale_b = Binding.name (proto_name ^ "_state");
          val _ = Output.writeln ("\nlocale\n  " ^ (Binding.name_of locale_b));
          
          (* HACK as I didn't know how to get a hand of the right constant *)
          val proto_t = Syntax.read_term_global thy proto_name;
          val (_,lthy) = 
            add_simple_locale locale_b "reachable_state" [SOME proto_t] thy;
        in
          lthy |> Local_Theory.exit_global
        end))
  end;

(* registering the protocol definition command *)
val protodef_parser = 
  Parse.binding --| Parse.where_ -- (Parse_Spec.opt_thm_name ":" -- Parse.prop);

val _ =
  Outer_Syntax.local_theory @{command_spec "protocol"} "security protocol definition" 
    (protodef_parser >> (fn spec => define_proto_cmd spec #> #2));


(******************************************************************************
**  Sources Case Name Computation
******************************************************************************)


val unnamed_caseN = "unnamed"

(* Given a list of premises, it extracts the content of the first premise being
   a "case_name" hint.
*)
fun extract_case_name prems = 
  case Hints.gather_by_name "case_name" prems of
    (name :: _) => HOLogic.dest_string name
  | [] => raise TERM ("extract_case_name", prems);


(* Given a list of case premises, it extracts the rolestep constant name
   whose specification message was the start for this case.
*)
fun extract_rolestep_name prems = 
  case Hints.gather_by_name "decrChainFrom" prems of
    (data :: _) => 
      (case HOLogic.strip_tuple data of
        (_ :: _ :: Const (step_name,_) :: _) => step_name
      | _ => raise TERM ("extract_rolestep_name", prems)
      )
  | _ => raise TERM ("extract_rolestep_name", prems)


(* Name the variable constructors *)
fun var_name (Const (@{const_name "AVar"},_) $ i) = HOLogic.dest_string i
  | var_name (Const (@{const_name "MVar"},_) $ i) = HOLogic.dest_string i
  | var_name _                                    = "var"

(* Name the execution literal constructors *)
fun msg_lit_name (Const (@{const_name "ENonce"},_) $ n $ _) = HOLogic.dest_string n
  | msg_lit_name (Const (@{const_name "EConst"},_) $ c)     = HOLogic.dest_string c
  | msg_lit_name _                                          = "lit";


(* Name the pattern constructors *)
fun msg_name (Const (@{const_name "Enc"},_) $ _ $ _)  = "enc"
  | msg_name (Const (@{const_name "Tup"},_) $ _ $ _)  = "tup"
  | msg_name (Const (@{const_name "Hash"},_) $ _)     = "hash"
  | msg_name (Const (@{const_name "K"},_) $ _ $ _)    = "K"
  | msg_name (Const (@{const_name "PK"},_) $ _)       = "PK"
  | msg_name (Const (@{const_name "SK"},_) $ _)       = "SK"
  | msg_name (Const (@{const_name "Lit"},_) $ l)      = msg_lit_name l
  | msg_name _                                        = "msg"


(* extract all non-reflexive equalities,
   if there is a lhs with a substitution then use this name
   else use the name of the first rhs
*)
fun extract_msg_name prems =
  let
    val dest_msg_eq = dest_non_refl_eq @{typ execmsg};
    val subst_var = var_name o 
                    #1 o #2 o dest_variable_store_lookup o 
                    #1 o dest_msg_eq;
    val fixed_msg = msg_name o #2 o dest_msg_eq;

    val subst = try hd (ESPL_Utils.gather_props subst_var prems);
    val fixed = try hd (ESPL_Utils.gather_props fixed_msg prems);
  in
    if is_none subst andalso is_none fixed then 
      NONE
    else
      if subst = fixed then 
        SOME (the_default "" subst)
      else
        SOME (
          (the_default "" subst) ^
          (if is_some subst andalso is_some fixed then "_" else "") ^
          (the_default "" fixed)
        )
  end  

(* get the case name from a term representing an implication *)
fun get_case_name t =
  let
    val prems = Logic.strip_imp_prems (Term.strip_all_body t);
  in
    case try extract_case_name prems of
      SOME "decrypt" =>
        (let
          val step_name = extract_rolestep_name prems;          
          val opt_name  = extract_msg_name prems;
        in
          (List.last (space_explode "." step_name)) ^
          (case opt_name of
            SOME m => "_" ^  m
          | NONE   => "")
        end
        handle _ => "decrypt")
    | SOME name => name
    | NONE => unnamed_caseN
  end;

(* Compute the case names for the given theorem being a case distinction in
   eleminitation form gained from spezializing the knows_cases theorem. 
*)
fun source_case_names th =
  th |> Thm.prop_of
     |> Logic.strip_imp_prems
     |> map get_case_name
     |> blank_zero_numbers (op =)
     |> map (append_optional_number "_")


fun mk_case_name_hint thy name =
  Hints.mk_hint_thm thy "case_name" (HOLogic.mk_string name);

(* Insert the case names into a theorem *)
fun insert_case_names ctxt th =
  let
    val cases         = source_case_names th;
    val case_hint     = Hints.mk_hint_thm ctxt "case_name" o HOLogic.mk_string o nth cases;
    fun ins_tac (_,i) = Method.insert_tac [case_hint (i-1)] i;
  in
    HOL_Ext.refine_rule ctxt 
      (K (ALLGOALS (Hints.remove_all_hints_tac ctxt THEN' SUBGOAL ins_tac))) th
  end


(******************************************************************************
**  Chain Rule Expansion
******************************************************************************)

(* FIXME: Not sure if there isn't some additional setup needed.
          For NamedThms it is..
*)

(* Storing the rules used for eliminating the type information *)
structure TypeElimRulesData = Generic_Data
(
  type T = Thm.thm list;
  val empty = [];
  val extend = I;
  fun merge (ths1, ths2) = distinct Thm.eq_thm (ths1 @ ths2)
);

val lookup_type_elim_rules = TypeElimRulesData.get o Context.Proof;


(* Reorder the bound variables introduced by the expansion of a ticket.

   The argument is premise of the form !! x1..xn. A1 ==> ... An ==> B
   The result is a conversion justifying the permutation of x1...xn
   according to their left-to-right occurrence in the first equality 
   of the form

     s(MV v tid) = msg
*)
fun reorder_bound_conv ctxt ct = 
  let
    val t = Thm.term_of ct;
    val dest_subst_eq =
      apfst (dest_variable_store_lookup) o dest_non_refl_eq @{typ execmsg};
  in
    case 
      t |> Term.strip_all_body 
        |> Logic.strip_imp_prems
        |> ESPL_Utils.gather_props dest_subst_eq
        |> try hd
    of
      SOME ((_, (_, tidt)), rhst) => 
        let
          val n = length (Term.strip_all_vars t);
          val p = [] |> fold HOL_Ext.add_bound_list [tidt, rhst] 
                     |> distinct (op =)
                     |> map (fn i => n - i - 1);
        in
          HOL_Ext.forall_permute_conv ctxt p ct
        end
    | NONE    => Conv.all_conv ct
  end;


(* reorders the bound variables of the premises according to
   reorder_bound_conv
*)
fun reorder_bound_vars ctxt th =
  HOL_Ext.lift_ground_thm_mod ctxt
    (Conv.fconv_rule o 
     Conv.prems_conv (Thm.nprems_of th) o reorder_bound_conv)
    th;

(* Eliminates the remaining decryption chains starting from symbolically
   instantiated protocol variables using their type assertions.
*)
fun type_elim_tac ctxt ty_elim_ths = 
  let
    fun mk_elim_tac ty_elim_th =
      EVERY'
        [ etac ty_elim_th
        , assume_tac
        , TRY o full_simp_tac ctxt
        , TRY o (REPEAT o etac @{thm conjE})
        , TRY o Orders.order_tac ctxt []
        ]
  in
    (FIRST' (map mk_elim_tac ty_elim_ths)) THEN'
    (TRY o Clasimp.clarsimp_tac ctxt)
  end;


fun expand_knows_cases_tac ctxt ty_elim_ths =
  REPEAT_DETERM1 (
    FIRST [ safe_tac ctxt
          , CHANGED_PROP (TRYALL (full_simp_tac ctxt))
          , CHANGED_PROP (TRYALL (type_elim_tac ctxt ty_elim_ths))
          ] 
  );

(* Convert a knows_cases theorem to its elimination form with
   all premises named with the corresponding case name.

   Optionally, changes to the given message term are traced.
*)
fun refine_knows_cases ctxt opt_msg_t case_th =
  let  
    (* don't track changes to first subgoal "m : knows t" *)
    fun mk_track_tac th (_,i) = Method.insert_tac [th] i;

    val ((track_tac, untrack), ctxt') = 
      case opt_msg_t of
        SOME msg_t => apfst (apfst mk_track_tac) 
                        (HOL_Ext.track_HOL_term ctxt msg_t)
      | NONE       => ((K all_tac, I), ctxt);

    val ty_elim_ths = lookup_type_elim_rules ctxt';

    fun tac  lthy   = 
      (ALLGOALS (SUBGOAL track_tac) THEN 
       expand_knows_cases_tac lthy ty_elim_ths);
  in
    HOL_Ext.refine_rule ctxt' tac case_th
    |> untrack
    |> insert_case_names ctxt
    |> reorder_bound_vars ctxt
  end;


(* A more convenient interface to refine_knows_cases

   FIXME: Why can't it be merged with refine_knows_cases?
*)
fun prepare_sources_elim ctxt case_th msg_t =
  let
    val lthy = Variable.auto_fixes msg_t ctxt;

    val knows_ct = 
      HOLogic.mk_mem (msg_t, @{term "knows t"})
      |> HOLogic.mk_Trueprop
      |> Thm.cterm_of (Proof_Context.theory_of lthy);

    val knows_th = Thm.assume knows_ct;
  in 
    (knows_th RS case_th)
    |> HOL_Ext.make_HOL_elim
    |> refine_knows_cases lthy (SOME msg_t)
    |> Thm.implies_intr knows_ct
    |> singleton (Proof_Context.export lthy ctxt) 
    |> Drule.zero_var_indexes
  end;


(*** Precomputing and storing chain rule expansion in the actual theory ***)

structure KnowsCasesCache = Named_Thms
  (val name = @{binding "knows_cases_cache"}
   val description = "Cache of protocol and message specific specializations of the knows_cases theorem")

(* shorthand for attributes modifying the knowledge cases *)
val att_knows_cases_cache_add = Attrib.internal (K KnowsCasesCache.add);
val att_knows_cases_cache_del = Attrib.internal (K KnowsCasesCache.del);

(* Precompute and register the standard chain rule expansions 
*)
fun precompute_source_elim_rules case_th ctxt =
  let
    val _ = Output.writeln "\n  precomputed sources for:"

    fun precompute (msg_t, desc) = 
      let
        val b = Binding.name ("knows_cases_" ^ desc)
        val _ = Output.writeln ("    " ^ Binding.name_of b);
      in
        (b, prepare_sources_elim ctxt case_th msg_t)
      end;

    val prec_ths = Par_List.map precompute
      [ (@{term "LN n i   :: execmsg"}, "Nonce")
      , (@{term "Hash m   :: execmsg"}, "Hash")
      , (@{term "Enc m k  :: execmsg"}, "Enc")
      , (@{term "SK a     :: execmsg"}, "SK")
      , (@{term "K a b    :: execmsg"}, "K")
      , (@{term "KShr A   :: execmsg"}, "KShr")
      ] 

    fun prep_note (b,th) = ((b,[]),[([th],[att_knows_cases_cache_add])]);
  in
     ctxt
(*     |> Local_Theory.target (add_sources_rules (map snd prec_ths)) *)
     |> Local_Theory.notes (map prep_note prec_ths)
  end;


(******************************************************************************
**  Type Invariant Definitions
******************************************************************************)

(* Destruct a mk_typing constructor *)
fun dest_mk_typing (Const (@{const_name mk_typing},_) $ typ) = 
      typ |> HOLogic.dest_list |> map HOLogic.dest_prod
  | dest_mk_typing t = raise TERM ("dest_mk_typing", [t]);

(* proves and notes all the theorems associated to a typing *)
fun setup_typing mk_binding ann_def ctxt =
  let
    val (typ_const,typ_def) = ann_def;

    val autom_tac = auto_tac (ctxt addsimps [typ_def])
    val ss_full = ctxt addsimps [typ_def] addsimps @{thms mk_typing_def} |> simpset_of;
    
    val vars = typ_def |> Thm.prop_of 
      |> ESPL_Utils.dest_HOL_def |> snd |> dest_mk_typing |> map fst;

    val typ_calls = map (curry (op $) typ_const) vars;

    val mono_typ_th = (@{const monoTyp} $ typ_const)
      |> HOLogic.mk_Trueprop
      |> Thm.cterm_of (Proof_Context.theory_of ctxt)
      |> (fn ct => Goal.prove_internal [] ct
           (K autom_tac)
         );
  in
   ctxt
   (* expansions for 'calling' the typing with defined variable *)
     |> #2 o ESPL_Utils.notes_expansion ss_full
        [ (mk_binding "defined_vars", [(typ_calls, [att_iff_add])]) ]
   (* monotonicity theorem *)
     |> Local_Theory.note (mk_binding "monoTyp", [mono_typ_th])
   (* restore original annotated definition *)
     |>> K ann_def 
  end;

(* Defines and setups a typing defined using 'mk_typing'. *)
fun define_typing_cmd ((b,proto_name), ((att,srcs),raw_def)) params_ctxt =
  let
    fun mk_rel_binding name = 
      (Binding.qualify true (Binding.name_of b) (Binding.name name), srcs);

    val ((typ_const, (_, typ_def)), spec_ctxt) = params_ctxt 
      |> Specification.definition_cmd
          (SOME (b, SOME "WeakTyping.typing", NoSyn)
          , ((att,srcs), raw_def)) true;
  in
    setup_typing mk_rel_binding (typ_const, typ_def) spec_ctxt
  end;

(* Add the locale corresponding to the type invariant being defined 
*)
fun add_type_invariant_locale (b,(typ_t, proto_t)) =
  add_simple_locale b "typed_state" 
    [SOME proto_t, NONE, NONE, NONE, SOME typ_t];

(* Defines and setups a typing as well as its corresponding 
   chain rule expansions.
*)
fun type_invariant_cmd (spec as ((typing_b,proto_name),_)) lthy =
  lthy
  |> #2 o define_typing_cmd spec
  |> Local_Theory.raw_theory (fn thy =>
      let
        val typ_name = Binding.name_of typing_b;
        val typ_t    = Syntax.read_term_global thy typ_name;
        val proto_t  = Syntax.read_term_global thy proto_name;
        val locale_b = Binding.name (typ_name ^ "_state");
        val _ = Output.writeln ("\nlocale\n  " ^ (Binding.name_of locale_b));

        val (_,lthy) = 
          add_type_invariant_locale (locale_b, (typ_t, proto_t)) thy;
        val case_th  = Proof_Context.get_thm lthy "knows_cases";
      in
        lthy
        |> #2 o precompute_source_elim_rules case_th
        |> Local_Theory.exit_global 
      end
   );

(* register the type invariant definition command *)
local structure P = Parse and K = Keyword in
  val for_proto = P.$$$ "for" |-- P.term;

  val type_invariant_parser = 
    P.binding -- for_proto --| P.where_ -- (Parse_Spec.opt_thm_name ":" -- P.prop);
  val _ =
    Outer_Syntax.local_theory @{command_spec "type_invariant"} "type invariant definition" 
      (type_invariant_parser >> type_invariant_cmd);
end;

end;
