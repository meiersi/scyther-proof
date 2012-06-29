(*****************************************************************************
 * ESPL --- an embedded security protocol logic
 *          http://people.inf.ethz.ch/meiersi/espl/
 *
 *   Copyright (c) 2009-2011, Simon Meier, ETH Zurich, Switzerland
 *
 * All rights reserved. See file LICENCE for more information.
 ******************************************************************************)
(* Various utility functions for working with Pure, HOL, and ESPL related terms. *)

signature ESPL_UTILS =
sig
  (* ML specific functions *)
  val choose2: 'a list -> ('a * 'a) list
  val unique_numbers: int -> ('a * 'a -> bool) -> 'a list -> ('a * int) list
  val optional_numbers: ('a * 'a -> bool) -> 'a list -> ('a * int option) list
  val blank_zero_numbers: ('a * 'a -> bool) -> 'a list -> ('a * int option) list
  val append_optional_number: string -> string * int option -> string

  (* Pure specific functions *)
  val local_standard': thm -> thm
  val expand_term: simpset -> term -> thm
  val thms_to_simpset: Proof.context -> thm list -> simpset
  val prove_prop 
     : Proof.context -> ({prems: thm list, context: Proof.context} -> tactic) -> term -> thm
  val notes_expansion
     : simpset -> (Attrib.binding * (term list * Args.src list) list) list ->
       local_theory -> (string * thm list) list * local_theory
  val note_expansion
     : simpset -> Attrib.binding * term list -> 
       local_theory -> (string * thm list) * local_theory
  val notes_proven
     : ({prems: thm list, context: Proof.context} -> tactic) ->
       (Attrib.binding * (term list * Args.src list) list) list ->
       Proof.context -> (string * thm list) list * local_theory
  val note_proven
     : ({prems: thm list, context: Proof.context} -> tactic) ->
       Attrib.binding * term list ->
       Proof.context -> (string * thm list) * local_theory
  val add_simple_locale
     : binding -> xstring -> term option list -> theory -> string * local_theory
  val add_simple_locale_cmd
     : binding ->
       xstring -> term option list -> Toplevel.transition -> Toplevel.transition

  (* HOL specific functions *)
  val gather_props: (term -> 'a) -> term list -> 'a list
  val dest_HOL_def: term -> term * term
  val symmetric_HOL_def: thm -> thm
  val prove_distinctness: 
    Proof.context -> ({prems: thm list, context: Proof.context} -> tactic) -> term list -> thm list
  val att_iff_add: Args.src
  val att_simp_add: Args.src
end;

structure ESPL_Utils: ESPL_UTILS =
struct

(******************************************************************************
**  ML specific functions
******************************************************************************)

(* all possibilities to choose two elements out of a list *)
fun choose2 []      = []
  | choose2 (x::xs) = map (pair x) xs @ choose2 xs

(* adds numbers to a list of possibly dupliate names such that each of the
   duplicate name gets its own number.
*)
fun unique_numbers start eq (names : 'a list) = 
  let fun add_number (numbered, name) = 
        case AList.lookup eq numbered name of
          SOME i => 
            ((name, i+1)   :: numbered)
        | NONE => 
            ((name, start) :: numbered)
  in  rev (Library.foldl add_number ([],names)) end;

(* like unique numbers but doesn't assign a number to non-duplicate names *)
fun optional_numbers eq =
  let
    fun mk_optional [] = []
      | mk_optional ((n,i)::xs) = 
         (n, if (i > 1) orelse (exists (curry eq n o fst) xs) then SOME i else NONE) 
         :: mk_optional xs
  in mk_optional o unique_numbers 1 eq end;

(* like unique numbers, but blanks out the first occurrences of an element*)
fun blank_zero_numbers eq =
  let fun blank (n,i) = if (equal i 0) then (n,NONE) else (n,SOME i)
  in map blank o unique_numbers 0 eq end;

(* appends an optional number using the given separator *)
fun append_optional_number _   (n,NONE)   = n
  | append_optional_number sep (n,SOME i) = n ^ sep ^ string_of_int i


(******************************************************************************
**  Pure specific functions
******************************************************************************)

(* An adaption of Drule.standard' such that hypotheses are not 'taken down' as
   premises 
*)
val local_standard' =
  forall_intr_frees
  #> `Thm.maxidx_of
  #-> (fn maxidx =>
    Thm.forall_elim_vars (maxidx + 1)
    #> Thm.strip_shyps
    #> zero_var_indexes
    #> Thm.varifyT);

(* Generate the theorem proving the expansion of a term wrto to the given
   simpset and convert it into a rule.
*)
fun expand_term ss t = t
  |> Thm.cterm_of (ProofContext.theory_of (MetaSimplifier.the_context ss))
  |> Simplifier.rewrite ss
  |> (fn conv => conv RS @{thm meta_eq_to_obj_eq}) 
  |> local_standard'

(* Prove the validity of a proposition with a given tactic. *)
fun prove_prop ctxt mk_tactic goal = Goal.prove ctxt [] [] goal mk_tactic;

(* create a simpset consisting only of the given theorems in the given context *)
fun thms_to_simpset ctxt ths = 
  Simplifier.context ctxt (MetaSimplifier.empty_ss addsimps ths);

(* Expand a list of terms and note the resulting theorems. *)
fun notes_expansion ss to_expand = 
  Local_Theory.notes (map (apsnd (map (apfst (map (expand_term ss))))) to_expand);

(* Expand a term and note the resulting theorem. *)
fun note_expansion ss (a, ts) = 
  notes_expansion ss [(a, [(ts, [])])] #>> the_single;

(* Prove a list of propositions and note the resulting theorems *)
fun notes_proven mk_tactic to_prove ctxt = 
  Local_Theory.notes 
  (map (apsnd (map (apfst (map (prove_prop ctxt mk_tactic))))) to_prove) 
  ctxt;

(* Prove a proposition and note the resulting theorem *)
fun note_proven mk_tactic (a, ts) = 
  notes_proven mk_tactic [(a, [(ts, [])])] #>> the_single;


(* A simplified version of the Expression.add_locale command for
   emulating the Isar script "locale b = loc_name inst" where
   inst is a positional instantiation.
*)
fun add_simple_locale b loc_name inst thy =
  Expression.add_locale b (Binding.empty)
  ( [ ( Locale.intern thy loc_name
      , ( ("",false)
        , Expression.Positional inst
        )
      )
    ]
  , [] )
  []
  thy;

fun add_simple_locale_cmd b loc_name inst =
  Toplevel.begin_local_theory false (#2 o add_simple_locale b loc_name inst);


(******************************************************************************
**  HOL specific functions
******************************************************************************)

(* Gathers proposition destructible using the given destructor *)
fun gather_props dest = map_filter (try (dest o HOLogic.dest_Trueprop))

(* destruct a HOL definition; i.e. either "lhs == rhs" or "lhs = rhs" *)
fun dest_HOL_def t = 
  (t |> HOLogic.dest_Trueprop |> HOLogic.dest_eq)
  handle TERM _ => Logic.dest_equals t

(* returns the symmetric variant of a Pure or HOL equality *)
fun symmetric_HOL_def th = 
  Thm.symmetric th
  handle THM ("symmetric", _, _) => th RS sym |> Drule.zero_var_indexes

(* Proves the distinctness of all non-reflexive pairs of the list of terms
   using the given tactic.
*)
fun prove_distinctness ctxt mk_tactic ts =
  let fun mk_ineqs (t1,t2) = 
        let val th = prove_prop ctxt mk_tactic 
              (HOLogic.mk_Trueprop (HOLogic.mk_not( HOLogic.mk_eq (t1,t2))))
        in [th, th RS @{thm not_sym}] end
  in flat (map mk_ineqs (choose2 ts)) end

(* shorthands for common attributes *)
val att_iff_add = Attrib.internal (K Clasimp.iff_add)
val att_simp_add = Attrib.internal (K Simplifier.simp_add)

end;
