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
                  (prod_ord bool_ord TermOrd.term_ord)))
     (proj lhs, proj rhs) 
  end

fun old_unify_term_ord (arg as (lhs,rhs)) = 
  if (is_variable_store_lookup lhs) then 
    if (is_variable_store_lookup rhs) then
      TermOrd.term_ord arg
    else
      LESS
  else
    if (is_variable_store_lookup rhs) then
      GREATER
    else
      if (is_roleMap lhs) then
        if (is_roleMap rhs) then
          TermOrd.term_ord arg
        else
          LESS
      else
        if (is_roleMap rhs) then
          GREATER
        else
          TermOrd.term_ord arg;
          
*}

(*
context reachable_state begin

ML{*

fun both t = (unify_term_ord t, old_unify_term_ord t);

both (@{term "s (MV a b)"}, @{term "LN x i"});
both (@{term "s (MV a b)"}, @{term "s (MV c d)"});
both (swap (@{term "s (MV a b)"}, @{term "s (AV c d)"}));
both (@{term "roleMap r i"}, @{term "Some R"});
both (swap (@{term "roleMap r i"}, @{term "Some R"}));
  

*}
*)

ML{*

structure UnifyDest = Named_Thms
  (val name ="unify_dest"
   val description = "Destruction rules to be used in note_unified")

*}

setup{* UnifyDest.setup *}

declare (in reachable_state) split_before[unify_dest]
declare (in reachable_state) split_knows[unify_dest]

ML{*

(* Tries to derive 'False' from equality of sizes of equated terms.
*)
fun inequal_sizes ss eq_th =
  let
    val opt_size_eq = 
      SOME (simplify ss (eq_th RS  @{thm eq_imp_size_eq}))
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
    val thm_by_name = ProofContext.get_thm ctxt;
    val ss = simpset_of ctxt 
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
             | (@{const "op &"} $ _ $ _) =>
                 solve1 ( done 
                        , (th RS @{thm conjunct1}) ::
                          (th RS @{thm conjunct2}) :: todo
                        )
             | (Const (@{const_name "op ="},_) $ _ $ _) => 
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
        val ths  = ProofContext.get_thms ctxt (ProofContext.full_name ctxt b);
      in
        ((b,[]), [(f ctxt ths,[])])
      end;

    fun modify_and_renote state =
      state
      |> map_context_result 
          (fn ctxt => ctxt |>
            (ProofContext.note_thmss "" 
              (map (modify_bound_thms ctxt) bindings))
          )
      |> (fn (named_thss, state') =>
           state'
           |> Proof.put_facts (SOME (maps snd named_thss))
         )
  in
    modify_and_renote o Proof.note_thmss args
  end

*}

ML{*
local
  structure K = OuterKeyword;
  structure T = Toplevel;

  fun define_cmd name info f =
    OuterSyntax.command name info (K.tag_proof K.prf_decl)
    (SpecParse.name_facts >> (T.print oo (T.proof o (note_modified_thmss f))));
in
  val _ = 
    define_cmd "note_prefix_closed" 
      "prefix close facts and store them under the given name"
      ESPL_Methods.prefix_close_thms;

  val _ = 
    define_cmd "note_unified" 
      "unify equality facts and store them under the given name"
      (unify true);

  (* TODO: Implement this command - currently it is just notes. *)
  val _ = 
    define_cmd "note_cyclic" 
      "try to derive a cyclicity violation from the given facts and store them under the given name"
      (K I);

end
*}


(*

lemma (in reachable_state) test : "X"
proof -
  fix tid\<^isub>1 tid\<^isub>2 tid\<^isub>3
  assume "s (MV ''ni'' tid\<^isub>1) = LN ''ni'' tid\<^isub>3"
  and"s (MV ''ni'' tid\<^isub>1) = LN ''ni'' tid\<^isub>2"
ML_prf{*
  unify true @{context} @{thms this}
  handle THM (_,_,ths) => ths

*}
  note_unified facts = this

lemma

*)

(*

ML{* @{const predOrd} *}
ML{* @{term "predOrd t (Ln \<lbrace>LN ''ni'' i, x\<rbrace>) (Ln y)"} *}
ML{*

case @{term "predOrd t (Ln \<lbrace>LN ''ni'' i, x\<rbrace>) (Ln y)"} of
    (@{const predOrd} $ _ $ (@{const Ln} $ (Const (@{const_name Tup},_) $ _ $ _)) $ _) =>
       Const ("YES 1", TFree ("blah",["blih"]))
  | (Const (@{const_name predOrd}, _) $ _ $ _ $ _ ) =>
       Const ("YES 2", TFree ("blah",["blih"]))
  | (x $ _ $ _ $ _ ) =>
       x
  | _ => Const ("no", TFree ("blah",["blih"]))

*}

lemma test: 
  assumes facts:
    "Enc x y = Enc t v"
    "x = v"
  shows "False"
proof -
  note_unified this = facts
  thm this
oops


text{* Testing the role definition command *}
role nslXInit
where "nslXInit \<equiv> 
  [ Send ''0'' (PEnc \<langle>sC ''0'', sAV ''I'', sN ''ni''\<rangle> (sPK ''R''))
  , Recv ''1'' (PEnc \<langle>sC ''1'', sAV ''R'', sN ''ni'', sMV ''nr''\<rangle> (sPK ''I''))
  , Send ''2'' (PEnc \<langle>sC ''2'', sMV ''nr''\<rangle> (sPK ''R''))
  ]"

text{* An additional role for testing purposes. *}
role nslXResp
where "nslXResp \<equiv>
  [ Recv ''0'' (PEnc \<langle>sC ''0'', sLAV ''I'', sLMV ''ni''\<rangle> (sPK ''R''))
  , Send ''1'' (PEnc \<langle>sC ''1'', sLAV ''R'', sLMV ''ni'', sLN ''nr''\<rangle> (sPK ''I''))
  , Recv ''2'' (PEnc \<langle>sC ''2'', sLN ''nr''\<rangle> (sPK ''R''))
  ]"

protocol nslX
where "nslX = {nslXInit, nslXResp}"

locale atomic_nslX_state = typed_state nslX _ _ _ "weakly_atomic"

lemma (in atomic_nslX_state) SK_from_IK0:
  assumes facts:
    "SK a \<in> knows t"
  shows "a \<in> Compromised"
using facts
proof(sources "SK a")
qed clarsimp

lemma (in atomic_nslX_state) I_sec_ni:
  assumes facts:
    "roleMap r i = Some nslXInit"
    "Ln (Tup (LN ''ni'' i) x) \<prec> Ln y"
    "s(AV ''I'' i) \<notin> Compromised"
    "s(AV ''R'' i) \<notin> Compromised"   
  shows "False"
using facts
proof(sources! "LN ''ni'' i")
  case nslXInit_0_ni
  note_unified facts = facts this
thm split_before[OF `Ln \<lbrace>LN ''ni'' i, x\<rbrace> \<prec> Ln y`]
ML_prf{*
@{term "Ln \<lbrace>LN ''ni'' i, x\<rbrace> \<prec> Ln y"}
*}
  thus ?thesis
  proof(sources! "SK (s (AV ''R'' i))")
    case ik0
    note_unified facts = facts this
    thus ?thesis by clarsimp
  qed
next
  case (nslXInit_2_nr i1)
  note_unified facts = facts this
  thus ?thesis
  proof(sources! "inst s i1 nslXInit_1_pt")
    case fake
    note_unified facts = facts this
    thus ?thesis by order
  next
    case (nslXResp_1_enc r1)
    note_unified facts = facts this
    thus ?thesis .
  qed
next
  case (nslXResp_1_ni r1)
  note_unified facts = facts this
  thus ?thesis
  proof(sources "inst s r1 nslXResp_0_pt")
    case fake
    note_unified facts = facts this
    thus ?thesis by order
  next
    case (nslXInit_0_enc i2)
    note_unified facts = facts this
    thus ?thesis
    proof(sources! "SK (s (AV ''I'' i))")
      case ik0
      note_unified facts = facts this
      thus ?thesis by clarsimp
    qed
  qed
qed





(* OLD TEST INFRASTRUCTURE


ML{*

val th1 = Thm.assume @{cterm "Trueprop (s (AV ''a'' i) = x)"};
val th2 = Thm.assume @{cterm "Trueprop (PK (s (AV ''a'' i)) = inv (y))"};
val th3 = Thm.assume @{cterm "Trueprop (Enc (LN ''a'' i) (PK (s (AV ''a'' j))) = 
                                        Enc (LN ''a'' j) (PK (s (AV ''b'' i))))"};
val th4 = Thm.assume @{cterm "Trueprop ((b::nat) < c)"};
val th5 = Thm.assume @{cterm "Trueprop ((x::execmsg) = Enc (Tup y (PK x)) z)"};


*}


ML{*

unify true @{context} [th1,th2,th3,th5,th1,th2,th3,th5,th1,th2,th3,th5,th1,th2,th3,th5]

*}

subsection{* Redefining the notes command *}

text{*
  note[prefix_closed] this = facts
  note[unified] this = facts

^ preferred version

  note this[unified] = facts

*}

ML{*

Proof.note_thmss
*}

ML{* 

ProofContext.note_thmss
*}

note_prefix_closed
note_unified
note_cyclic

ML{*

local 
  structure P = OuterParse;
  structure S = SpecParse;

  fun bling ctxt =
    let val _ = Output.warning "test";
    in ctxt end;

  fun modifier (name, f) = P.$$$ name >> K f;
  val modifiers = [("test", (K bling)),("unified",unify true)];
in
  val thms_mod = Scan.first (map modifier modifiers @ [Scan.succeed (K I)]);
  val mod_name_facts = thms_mod -- S.name_facts
end
*}
 


lemma test: "blah"
proof -
  note_prefix_closed unified = sym allI
    and blah = ballI
  thm this
  thm blah
  thm unified
  





*)

role C
where "C =
  [ Send ''1'' ( PEnc ( sN ''k'' ) ( sPK ''S'' ) )
  , Recv ''2'' ( PHash ( sN ''k'' ) )             
  ]"                                              

role S
where "S =
  [ Recv ''1'' ( PEnc ( sMV ''k'' ) ( sPK ''S'' ) )
  , Send ''2'' ( PHash ( sMV ''k'' ) )             
  ]"                                               

protocol CR
where "CR = { C, S }"

locale atomic_CR_state = atomic_state CR
locale CR_state = reachable_state CR

lemma (in atomic_CR_state) C_secret_k:
  assumes facts:
    "roleMap r i\<^isub>0 = Some C"
    "s(AV ''S'' i\<^isub>0) \<notin> Compromised"
    "LN ''k'' i\<^isub>0 \<in> knows t"
  shows "False"
using facts proof(sources! " LN ''k'' i\<^isub>0 ")
  case C_1_k note_unified facts = this facts
  thus ?thesis proof(sources! " SK ( s(AV ''S'' i\<^isub>0) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in CR_state) weak_atomicity:
  "complete (t,r,s) atomicAnn"
proof (cases rule: complete_atomicAnnI[completeness_cases_rule])
  case (S_1_k t r s i\<^isub>0) note facts = this
  then interpret state: atomic_state CR t r s
    by unfold_locales assumption+
  show ?case using facts
  proof(sources! "
      Enc ( s(MV ''k'' i\<^isub>0) ) ( PK ( s(AV ''S'' i\<^isub>0) ) ) ")
  qed (insert facts, ((fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
qed

lemma (in atomic_CR_state) C_ni_synch:
  assumes facts:
    "roleMap r i\<^isub>1 = Some C"
    "s(AV ''S'' i\<^isub>1) \<notin> Compromised"
    "(i\<^isub>1, C_2) \<in> steps t"
  shows
    "\<exists>i\<^isub>2.
       roleMap r i\<^isub>2 = Some S &
       s(AV ''S'' i\<^isub>2) = s(AV ''S'' i\<^isub>1) &
       s(MV ''k'' i\<^isub>2) = LN ''k'' i\<^isub>1 &
       St(i\<^isub>1, C_1) \<prec> St(i\<^isub>1, C_2) &
       St(i\<^isub>1, C_1) \<prec> St(i\<^isub>2, S_1) &
       St(i\<^isub>2, S_2) \<prec> St(i\<^isub>1, C_2) &
       St(i\<^isub>2, S_1) \<prec> St(i\<^isub>2, S_2)"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! " Hash ( LN ''k'' i\<^isub>1 ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest: C_secret_k intro: event_predOrdI)
  next
    case (S_2_hash i\<^isub>2) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc ( LN ''k'' i\<^isub>1 ) ( PK ( s(AV ''S'' i\<^isub>2) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest: C_secret_k intro: event_predOrdI)
    next
      case C_1_enc note_unified facts = this facts
      thus ?thesis by force
    qed
  qed
qed

*)

end
