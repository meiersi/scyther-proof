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
theory Unify
imports 
  HOL_ext
  InferenceRules
  WeakTyping
  (* referenced because we use espl_definitions.ML and
     espl_methods.ML. With a uses clause it would be
     loaded twice, which may result in strange effects.
  *)
  Automation
keywords
  "note_prefix_closed" "note_unified" "note_cyclic" :: prf_decl
begin

section{* Explicit unification of sets of equality theorems *}

text{* Specialized to the use cases of our ESPL *}

text{* Additional required lemmas *}
lemma eq_imp_size_eq: "x = y \<Longrightarrow> size x = size y"
  by (rule arg_cong)

ML{*

(*
  Strategy: Per theorem

     1. check that it is an unconditional equality
     2. rewrite using current simpset
     3. if false then stop and return theorem false
        otherwise split conjunctions and add to 
        current simpset

   NOTE: We have to maintain the invariant that the simpset
         is non-looping. Hence, we may have to rebuild it several 
         times. Probably whenever a thread identifier equality 
         occurs.
*)


(* Utilities 
 ************)

(* apply a function 'f' to a list and return the partition of
   all elements left unchanged by 'f' w.r.t. the given order
   and the changed elements.
*)
fun partition_changed ord f xs =
  let
    fun go unchanged changed []      = (rev unchanged, rev changed)
      | go unchanged changed (y::ys) = 
          let 
            val y' = f y
          in 
            case ord (y, y') of
              EQUAL => go (y::unchanged) changed       ys
            | _     => go unchanged      (y'::changed) ys
          end
  in 
    go [] [] xs 
  end

(* Remove an outer Trueprop if there is any *)
fun remove_Trueprop t = 
  the_default t (try HOLogic.dest_Trueprop t)

(* Destruct a symbolic representation of the contents
   of a protocol variable. 
*)
fun dest_MVar_store_lookup t = 
  case ESPL_Definitions.dest_variable_store_lookup t of
    (s, (@{const MVar} $ v, tid)) => (s, (v, tid))
  | _ => raise TERM ("dest_MVar_store_lookup: no MVar",[t])

val is_variable_store_lookup = can ESPL_Definitions.dest_variable_store_lookup
val is_MVar_store_lookup = can dest_MVar_store_lookup 


(* Check if a term is a roleMap application *)
fun is_roleMap (@{const roleMap} $ _ $ _) = true
  | is_roleMap _                          = false

(* Check if a term is a key inversion *)
fun is_key_inversion (@{term "ExecMessage.inv :: execmsg \<Rightarrow> execmsg"} $ _) = true
  | is_key_inversion _ = false


(* If the given theorem is a HOL equality it gets reoriented
   such that the lhs is guaranteed to be smaller than the 
   right-hand side with respect to the given order. Note that
   reflexive equalities are dropped!
*)
fun reorient_HOL_eq ord th =
  (case th |> Thm.concl_of 
           |> HOLogic.dest_Trueprop
           |> HOLogic.dest_eq
           |> ord
   of
     GREATER => SOME (th RS @{thm sym})
   | LESS    => SOME th
   | EQUAL   => NONE
  ) handle 
      TERM _ => SOME th 
    | THM (name,k,info) => 
        raise THM ("reorient_HOL_eq:" ^ name, k,info)

*}

ML{*

(* The term order we use for orienting the unification equalities:
     1. s x    is smaller than any other non-store term
     2. roleMap x y is smaller than any other non-roleMap term
     2. otherwise the standard term order is used.

   TODO: This could possibly be implemented using the
         lexicographic path ordering.

         Moreover, think about situations involving 'inv'.
         (We probably don't want to have 'inv' on the lhs.)
*)
fun unify_term_ord (lhs,rhs) =
  let fun proj t = (not (is_variable_store_lookup t)
                   , (not (is_MVar_store_lookup t)
                     , (not (is_roleMap t), t)
                   ) )

  in (prod_ord bool_ord 
                (prod_ord bool_ord 
                  (prod_ord bool_ord Term_Ord.term_ord)))
     (proj lhs, proj rhs) 
  end

fun old_unify_term_ord (arg as (lhs,rhs)) = 
  if (is_variable_store_lookup lhs) then 
    if (is_variable_store_lookup rhs) then
      Term_Ord.term_ord arg
    else
      LESS
  else
    if (is_variable_store_lookup rhs) then
      GREATER
    else
      if (is_roleMap lhs) then
        if (is_roleMap rhs) then
          Term_Ord.term_ord arg
        else
          LESS
      else
        if (is_roleMap rhs) then
          GREATER
        else
          Term_Ord.term_ord arg;
          
*}

ML{*

structure UnifyDest = Named_Thms
  (val name = @{binding "unify_dest"}
   val description = "Destruction rules to be used in note_unified")

*}

setup{* UnifyDest.setup *}

declare (in reachable_state) split_before[unify_dest]
declare (in reachable_state) split_knows[unify_dest]

ML{*

(* Tries to derive 'False' from equality of sizes of equated terms.
*)
fun inequal_sizes ctxt eq_th =
  let
    val opt_size_eq = 
      SOME (simplify ctxt (eq_th RS  @{thm eq_imp_size_eq}))
      handle THM _ => NONE
  in
    case opt_size_eq of
      SOME size_eq =>
        (case size_eq |> Thm.concl_of |> remove_Trueprop of
          @{term False} => SOME size_eq
        | _                    => NONE)
    | NONE => NONE
  end

(* Unify the equalities in the given list of theorems  
   using rewriting with the simpset of the given context. 
*)
fun unify do_occurs_check ctxt ths =
  let
    (* TODO: Remove hack by using Named_Thms data functor. *)
    val thm_by_name = Proof_Context.get_thm ctxt;
    val ss = ctxt 
      delsimps map thm_by_name ["tid_eq_commute", "reorient_store_eq_store"];

    (* substitute an equality theorem in the given list of 'done' and 
       'todo' theorems. The changed theorems from 'done' are readded
       to the output 'todo' list (the second component of the result).
    *)
    fun subst_eq (done, todo) eq_th =
      let
        val apply = simplify (ss addsimps [eq_th]);
        val (doneUc, doneC) = partition_changed Thm.thm_ord apply done;
      in
        (eq_th::doneUc, doneC @ map apply todo)
      end;

    (* occurence check: tries to prove 'False' from size equality *)
    fun occurs_check eq_th =
      if do_occurs_check then
        inequal_sizes ss eq_th
      else
        NONE

    (* solve a single unification equation *)
    fun solve1 (done, []      ) = done
      | solve1 (done, th::todo) = 
          if (member Thm.eq_thm done th) then
            solve1 (done, todo)
          else if not (Thm.no_prems th) then
            solve1 (th::done, todo)
          else
            (case remove_Trueprop (Thm.concl_of th) of
               (@{const True})           => solve1 (done, todo)
             | (@{const False})          => [th]
             | (@{const "HOL.conj"} $ _ $ _) =>
                 solve1 ( done 
                        , (th RS @{thm conjunct1}) ::
                          (th RS @{thm conjunct2}) :: todo
                        )
             | (Const (@{const_name "HOL.eq"},_) $ _ $ _) => 
                 (case reorient_HOL_eq unify_term_ord th of
                    NONE     => solve1 (done, todo)
                  | SOME th' =>
                     (case occurs_check th' of
                        SOME th_false => [th_false]
                      | NONE          => solve1 (subst_eq (done,todo) th')
                     )
                 )
             | _ => (case map_filter (try (curry (op RS) th)) (UnifyDest.get ctxt) of
                      []  => solve1 (th::done, todo)
                    | ths => solve1 (done, ths @ todo)
                    )
             ) 
  in
    solve1 ([], map (simplify ss) ths)
  end

*}



ML{*

(* Note a set of theorems modified by a function 

     'f:: Proof.Context -> thm list -> thm list'.

   This should be supported by attributes. However,
   currently we resort to the following hack. 

   We do a normal note_theoerms and the retrieve
   the bound theorems, modify them, and store them
   again WITHOUT any attributes being applied.

   This is fragile. However, I couldn't see a better
   way with the current framework.
*)
fun note_modified_thmss f args =
  let
    (* copied from Pure/Isar/proof.ML *)
    fun map_context_result f state =
      f (Proof.context_of state) 
      ||> (fn ctxt => Proof.map_context (K ctxt) state);

    val bindings = map (fst o fst) args;

    fun modify_bound_thms ctxt b =
      let
        val ths  = Proof_Context.get_thms ctxt (Proof_Context.full_name ctxt b);
      in
        ((b,[]), [(f ctxt ths,[])])
      end;

    fun modify_and_renote state =
      state
      |> map_context_result 
          (fn ctxt => ctxt |>
            (Proof_Context.note_thmss "" 
              (map (modify_bound_thms ctxt) bindings))
          )
      |> (fn (named_thss, state') =>
           state'
           |> Proof.set_facts (maps snd named_thss)
         )
  in
    modify_and_renote o Proof.note_thmss_cmd args
  end
*}

ML{*
local
  fun define_cmd name info f =
    Outer_Syntax.command name info
    (Parse_Spec.name_facts >> (Toplevel.print oo (Toplevel.proof o (note_modified_thmss f))));
in
  val _ = 
    define_cmd @{command_spec "note_prefix_closed"} 
      "prefix close facts and store them under the given name"
      ESPL_Methods.prefix_close_thms;

  val _ = 
    define_cmd @{command_spec "note_unified"}
      "unify equality facts and store them under the given name"
      (unify true);

  (* TODO: Implement this command - currently it is just notes. *)
  val _ = 
    define_cmd @{command_spec "note_cyclic"}
      "try to derive a cyclicity violation from the given facts and store them under the given name"
      (K I);

end
*}

end
