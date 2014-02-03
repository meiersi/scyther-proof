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
theory Hints
imports
  Main
begin

ML_file "espl_utils.ML"

section{* A Theory of Hints for Marking Intermediate Results *}


definition hint :: "string \<Rightarrow> 'a \<Rightarrow> bool"
where "hint lbl data = True"

text{* 
  Simplify with the rule below to remove all hints in your 
  current subgoal.
*}
lemmas remove_hints = hint_def

lemma hintI: "hint lbl data"
  by (simp add: remove_hints)


subsection{*ML Interface for working with hints*}

ML{*
signature HINTS =
sig
  val dest_hint: term -> string * term
  val mk_hint: string -> term -> term
  val mk_hint_thm: Proof.context -> string -> term -> thm
  val gather: (string * term -> bool) -> term list -> (string * term) list
  val gather_by_name: string -> term list -> term list
  val remove_all_hints_tac: Proof.context -> int -> tactic
end;

structure Hints: HINTS =
struct 

open ESPL_Utils;

(* Destructs a hint *)
fun dest_hint (Const (@{const_name hint}, _) $ lbl $ data) = (HOLogic.dest_string lbl, data)
  | dest_hint t = raise TERM ("dest_hint", [t]);

(* gather the hints in the premises matching the predicate *)
fun gather p = filter p o gather_props dest_hint
  
(* gather the hints matching the name *) 
fun gather_by_name name = map snd o gather (equal name o fst)

(* A tactic removing all hints in the given subgoal *)
fun remove_all_hints_tac ctxt = full_simp_tac (put_simpset HOL_ss ctxt addsimps @{thms remove_hints})

(* create a hint term *)
fun mk_hint name t =
  let
    val name_t  = HOLogic.mk_string name;
    val hint_ty = @{typ string} --> Term.fastype_of t --> HOLogic.boolT;
  in
    Const (@{const_name hint}, hint_ty) $ name_t $ t
  end;

(* create a hint theorem *)
fun mk_hint_thm ctxt name t =
  let
    val hint_ct = mk_hint name t |> HOLogic.mk_Trueprop
                                 |> Thm.cterm_of (Proof_Context.theory_of ctxt);
  in
    Goal.prove_internal [] hint_ct (K (ALLGOALS (remove_all_hints_tac ctxt)))
  end;

end;

*}

end

