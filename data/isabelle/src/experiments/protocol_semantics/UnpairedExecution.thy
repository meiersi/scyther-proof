theory UnpairedExecution
imports
  "../Protocol"
  ExecMessage
  WelltypedSubst
  ThreadPool
  PaulsonSemantics
  "../DistinctList"
begin

text{* An execution model resulting in knowledge-event traces *}

section{* Execution Model *}

subsection{* Types and Operations *}

subsubsection{* Execution Events *}

datatype execevent = 
    FromIK0 execmsg
  | MkStep tid rolestep
  | MkHash execmsg
  | MkFst  execmsg execmsg
  | MkSnd  execmsg execmsg
  | MkTup  execmsg execmsg
  | MkEncr execmsg execmsg
  | MkDecr execmsg execmsg

datatype knevent = "Knows" "execmsg"   ("\<star>_" [900] 900)
                 | "Event" "execevent" ("\<Delta>_" [900] 900)

types kntrace = "knevent list"

text{*
  The eventMsg is a technical construction used as an over-approximation
  over the input and output messages in order to simplify formulating
  the lemma about all messages of past events in the system being ground.
*}

fun eventMsg :: "wt_subst \<Rightarrow> execevent \<Rightarrow> execmsg" 
where
  "eventMsg s (MkStep tid (Send lbl msg)) = subst s (s2e msg tid)"
| "eventMsg s (MkStep tid (Recv lbl msg)) = subst s (s2e msg tid)"
| "eventMsg s (FromIK0 m) = m"
| "eventMsg s (MkTup x y)  = Tup x y"
| "eventMsg s (MkFst x y)  = Tup x y"
| "eventMsg s (MkSnd x y)  = Tup x y"
| "eventMsg s (MkHash m)   = Hash m"
| "eventMsg s (MkEncr m k) = Enc m k"
| "eventMsg s (MkDecr m k) = Enc m k"

fun pairParts :: "'a msg \<Rightarrow> 'a msg set"
where
  "pairParts (Tup x y) = 
     insert (Tup x y) (pairParts x \<union> pairParts y)"
| "pairParts m = {m}"

fun unpairMsg :: "execmsg set \<Rightarrow> execmsg \<Rightarrow> kntrace"
where
  "unpairMsg known (Tup x y) = 
    (if x \<in> known 
     then []
     else [\<Delta> MkFst x y, \<star> x]) @
     unpairMsg (insert x known) x @
    (if y \<in> (insert x (known \<union> pairParts x))
     then []
     else [\<Delta> MkSnd x y, \<star> y]) @
     unpairMsg (insert y (insert x (known \<union> pairParts x))) y"
| "unpairMsg known m = []"


lemma notin_set_unpairMsg [simp]:
  "\<Delta> MkStep tid step \<notin> set (unpairMsg knows m')"
  "\<Delta> MkEncr m k \<notin> set (unpairMsg knows m')"
  "\<Delta> MkDecr m k \<notin> set (unpairMsg knows m')"
  "\<Delta> MkTup x y \<notin> set (unpairMsg knows m')"
  "\<Delta> MkHash m \<notin> set (unpairMsg knows m')"
  "\<Delta> FromIK0 m \<notin> set (unpairMsg knows m')"
  by(induct m' arbitrary: knows, auto)


lemma pairParts_mono [iff]: "m \<in> pairParts m"
  by(induct m rule: pairParts.induct, auto)


lemma in_set_unpairMsg_casesD:
  "knev \<in> set (unpairMsg knows m) \<Longrightarrow> 
   (\<exists> m'. knev = \<star> m' \<and> m' \<notin> knows \<and> m' \<in> pairParts m \<and> size m' < size m ) \<or>
   (\<exists> x y. knev = \<Delta> MkFst x y \<and> x \<notin> knows \<and> x \<in> pairParts m \<and> 
                                size x < size m \<and> size y < size m) \<or>
   (\<exists> x y. knev = \<Delta> MkSnd x y \<and> y \<notin> knows \<and> y \<in> pairParts m \<and>
                                size x < size m \<and> size y < size m)"
proof(induct m arbitrary: knows)
  case Lit thus ?case by simp next
  case Enc thus ?case by simp next
  case Hash thus ?case by simp next
  case K thus ?case by simp next
  case PK thus ?case by simp next
  case SK thus ?case by simp next
  case (Tup m1 m2 knows) show ?case using prems(3)
    by(auto split: if_splits dest: prems(1,2))
qed

lemma distinct_unpairMsg [iff]: "distinct (unpairMsg knows m)"
  apply(induct m arbitrary: knows, simp_all, safe)
  apply((drule in_set_unpairMsg_casesD)+, 
        force dest: in_set_unpairMsg_casesD)+
  done

lemma Knows_size_unpairMsgD: 
  "\<star> m' \<in> set (unpairMsg knows m) \<Longrightarrow> size m' < size m"
proof(induct m arbitrary: knows)
  case Lit thus ?case by simp next
  case Enc thus ?case by simp next
  case Hash thus ?case by simp next
  case K thus ?case by simp next
  case PK thus ?case by simp next
  case SK thus ?case by simp next
  case (Tup m1 m2 knows) show ?case using prems(3)
    apply(auto split: if_splits)
    by(drule prems, simp)+
qed

lemma MkFst_size_unpairMsgD: 
  "\<Delta> MkFst x y \<in> set (unpairMsg knows m) \<Longrightarrow> size x < size m \<and> size y < size m"
proof(induct m arbitrary: knows)
  case Lit thus ?case by simp next
  case Enc thus ?case by simp next
  case Hash thus ?case by simp next
  case K thus ?case by simp next
  case PK thus ?case by simp next
  case SK thus ?case by simp next
  case (Tup m1 m2 knows) show ?case using prems(3)
    apply(auto split: if_splits)
    by(drule prems, simp)+
qed

lemma MkSnd_size_unpairMsgD: 
  "\<Delta> MkSnd x y \<in> set (unpairMsg knows m) \<Longrightarrow> size x < size m \<and> size y < size m"
proof(induct m arbitrary: knows)
  case Lit thus ?case by simp next
  case Enc thus ?case by simp next
  case Hash thus ?case by simp next
  case K thus ?case by simp next
  case PK thus ?case by simp next
  case SK thus ?case by simp next
  case (Tup m1 m2 knows) show ?case using prems(3)
    apply(auto split: if_splits)
    by(drule prems, simp)+
qed

lemmas size_unpairMsgD = 
  Knows_size_unpairMsgD MkFst_size_unpairMsgD MkSnd_size_unpairMsgD

lemma noteq_Tup_simps [simp]: 
  "x \<noteq> Tup x y" "Tup x y \<noteq> x" 
  "x \<noteq> Tup y x" "Tup y x \<noteq> x" 
  by safe (drule_tac f=size in arg_cong, simp)+


lemma Knows_in_set_unpairMsgD:
  "\<star> m' \<in> set (unpairMsg knows m) \<Longrightarrow>
   m' \<in> pairParts m \<and> size m' < size m \<and> m' \<notin> knows"
  apply(induct m arbitrary: knows)
  prefer 2 apply(force split: if_splits)
  by(force)+

lemma MkFst_in_set_unpairMsgD:
  "\<Delta> MkFst x y \<in> set (unpairMsg knows m) \<Longrightarrow> 
   \<star> x \<in> set (unpairMsg knows m)"
  by(induct m arbitrary: knows, auto)

lemma MkSnd_in_set_unpairMsgD:
  "\<Delta> MkSnd x y \<in> set (unpairMsg knows m) \<Longrightarrow> 
   \<star> y \<in> set (unpairMsg knows m)"
  by(induct m arbitrary: knows, auto)



subsubsection{* Reachable States during Execution *}

types state = "kntrace \<times> rolestep threadpool \<times> wt_subst"

text{* access the state's substitution *}
fun sts :: "state \<Rightarrow> wt_subst"
where "sts (t,r,s) = s"

inductive_set 
  reachable :: "proto \<Rightarrow> state set" 
  for P     :: "proto"
where
  init: "([], empty, empty_wts) \<in> reachable P"

| create:"\<lbrakk> (t, r, s) \<in> reachable P;
            tid \<notin> dom r;
            R \<in> P;
            dom_wts \<alpha> = {EVar (AVar a) tid | a tid. True};
            ran_wts \<alpha> = {Lit (EHonest a)   | a. True} \<union> {Lit Eve}
          \<rbrakk>
          \<Longrightarrow> (t, r(tid \<mapsto> newThread (Rep_role R)), extend_wts s \<alpha>) \<in> reachable P"

| send:  "\<lbrakk> (t, r, s) \<in> reachable P;
            Some (Send l msg) = curStep r tid;
            m = subst s (s2e msg tid)
          \<rbrakk>
          \<Longrightarrow> (t @ [\<Delta>(MkStep tid (Send l msg))] 
                 @ (if \<star>(m) \<in> set t 
                    then [] 
                    else \<star>(m) # unpairMsg (insert m {x | x. \<star> x \<in> set t}) m)
              , nextStep r tid
              , s) \<in> reachable P"
            
| recv:  "\<lbrakk> (t, r, s) \<in> reachable P;
            Some (Recv l msg) = curStep r tid;
            dom_wts \<alpha> = { EVar v tid | v. v \<in> FV msg };
            \<star>(subst (extend_wts s \<alpha>) (s2e msg tid)) \<in> set t
          \<rbrakk>
          \<Longrightarrow> (t @ [\<Delta>(MkStep tid (Recv l msg))], nextStep r tid, extend_wts s \<alpha>) \<in> reachable P"

| ik0:   "\<lbrakk> (t, r, s) \<in> reachable P;
            m \<in> IK0; 
            \<Delta>(FromIK0 m) \<notin> set t; \<star>(m) \<notin> set t
          \<rbrakk>
          \<Longrightarrow> (t @ [\<Delta>(FromIK0 m), \<star>(m)], r, s) \<in> reachable P"

| hash:  "\<lbrakk> (t, r, s) \<in> reachable P;
            \<star>(m) \<in> set t;
            \<Delta>(MkHash m) \<notin> set t; \<star>(Hash m) \<notin> set t
          \<rbrakk>
          \<Longrightarrow> (t @ [\<Delta>(MkHash m), \<star>(Hash m)], r, s) \<in> reachable P"

| tuple: "\<lbrakk> (t, r, s) \<in> reachable P;
            \<star>(x) \<in> set t;
            \<star>(y) \<in> set t;
            \<Delta>(MkTup x y) \<notin> set t; \<star>(Tup x y) \<notin> set t
          \<rbrakk>
          \<Longrightarrow> (t @ [\<Delta>(MkTup x y), \<star>(Tup x y)], r, s) \<in> reachable P"

| encr:  "\<lbrakk> (t, r, s) \<in> reachable P;
            \<star>(m) \<in> set t;
            \<star>(k) \<in> set t;
            \<Delta>(MkEncr m k) \<notin> set t; \<star>(Enc m k) \<notin> set t
          \<rbrakk>
          \<Longrightarrow> (t @ [\<Delta>(MkEncr m k), \<star>(Enc m k)], r, s) \<in> reachable P"


| decr:  "\<lbrakk> (t, r, s) \<in> reachable P;
            \<star>(Enc m k) \<in> set t;
            \<star>(inv k) \<in> set t;
            \<Delta>(MkDecr m k) \<notin> set t; \<star>(m) \<notin> set t
          \<rbrakk>
          \<Longrightarrow> (t @ [\<Delta>(MkDecr m k), \<star>(m)] 
                 @ unpairMsg (insert m {x | x. \<star> x \<in> set t}) m 
              , r, s) \<in> reachable P"


subsection{* Properties *}

subsubsection{* Execution Events *}

lemma eventMsg_ground_extend_wts:
  "ground (eventMsg s e) \<Longrightarrow>
   eventMsg (extend_wts s s') e = eventMsg s e"
  apply(induct rule: eventMsg.induct)
  by(simp_all add: extend_wts_conv_subst)


subsubsection{* Reachable States *}

locale reachable_state =
  fixes P :: proto
  and   t :: kntrace
  and   r :: "rolestep threadpool"
  and   s :: wt_subst
  assumes reachable [simp,intro!]: "(t,r,s) \<in> reachable P"
begin

lemma proto_roles:
  "r tid = Some (todo,done) \<Longrightarrow> 
  \<exists> R \<in> P. Rep_role R = rev done @ todo"
  apply(insert reachable, rotate_tac -1)
  apply(induct arbitrary: tid todo "done" rule: reachable.induct)
  apply(auto simp: newThread_def curStep_def nextStep_def split: if_splits option.splits list.splits)
  done

lemma Step_in_threadpool: 
  "\<Delta>(MkStep tid step) \<in> set t \<Longrightarrow> 
  \<exists> todo done. r tid = Some (todo,done)"
  apply(insert reachable, rotate_tac -1)
  apply(induct rule: reachable.induct)
  by(auto simp: nextStep_def split: if_splits)

lemma todo_notin_trace: 
  "\<lbrakk> r tid = Some (todo,done); step \<in> set todo \<rbrakk> \<Longrightarrow> 
     \<Delta>(MkStep tid step) \<notin> set t"
  apply(insert reachable, rotate_tac -1)
  proof(induct arbitrary: tid todo "done" rule: reachable.induct)
    case init thus ?case by simp next
    case (create t r s tid' R \<alpha>)
      then interpret old_state: reachable_state P t r s by unfold_locales
      show ?case using prems
      apply(clarsimp simp: newThread_def curStep_def split: option.splits if_splits)
      apply(drule old_state.Step_in_threadpool)
      apply(auto)
      done
  next
    case (send t r s l msg tid')
      then interpret old_state: reachable_state P t r s by unfold_locales
      show ?case using prems
      apply(clarsimp simp: nextStep_def curStep_def 
                    split: option.splits if_splits list.splits)
      apply(frule old_state.proto_roles)
      apply(clarsimp)
      apply(subgoal_tac "distinct (Rep_role R)")
      apply(force)
      apply(rule Rep_role_distinct)
      apply(force)
      done
  next
    case (recv t r s l msg tid \<alpha> tid' todo "done")
      then interpret old_state: reachable_state P t r s by unfold_locales
      show ?case using prems
      apply(clarsimp simp: nextStep_def curStep_def 
                    split: option.splits if_splits list.splits)
      apply(frule old_state.proto_roles)
      apply(clarsimp)
      apply(subgoal_tac "distinct (Rep_role R)")
      apply(force)
      apply(rule Rep_role_distinct)
      apply(force)
      done
  next case hash thus ?case by auto
  next case encr thus ?case by auto
  next case decr thus ?case by auto
  next case tuple thus ?case by auto
  next case ik0 thus ?case by auto
qed

lemma done_in_trace: 
  "\<lbrakk> r tid = Some (todo,done); step \<in> set done \<rbrakk> \<Longrightarrow> 
     \<Delta>(MkStep tid step) \<in> set t"
  apply(insert reachable, rotate_tac -1)
  proof(induct arbitrary: tid todo "done" rule: reachable.induct)
    case init thus ?case by simp next
    case (create t r s tid' R \<alpha>) thus ?case
      apply(clarsimp simp: newThread_def curStep_def split: option.splits if_splits)
      apply(rule FalseE)
      apply(thin_tac "dom_wts ?x = ?X")
      apply(auto)
      done
  next
    case (send t r s l msg tid') thus ?case 
      apply(clarsimp simp: nextStep_def curStep_def 
                    split: option.splits if_splits list.splits)
      apply(auto)
      done
  next
    case (recv t r s l msg tid \<alpha> tid' todo "done") thus ?case
      apply(clarsimp simp: nextStep_def curStep_def 
                    split: option.splits if_splits list.splits)
      apply(thin_tac "dom_wts ?x = ?X", force)+
      done
  next case hash thus ?case by auto
  next case encr thus ?case by auto
  next case decr thus ?case by auto
  next case tuple thus ?case by auto
  next case ik0 thus ?case by auto
qed

lemma Knows_in_set_unpairMsgI:
  "\<lbrakk> x \<in> pairParts m; x \<notin> knows; x \<noteq> m \<rbrakk> \<Longrightarrow> 
   \<star> x \<in> set (unpairMsg knows m)"
  apply(induct m arbitrary: x knows)
  apply(simp_all)
  apply(case_tac "x = m1", simp+)
  apply(case_tac "x = m2", simp+)
  apply(case_tac "x \<in> pairParts m1", simp+)
  apply(case_tac "m1 = m2", simp+)
  done

lemma MkFst_in_trace_imp_Knows_fst:
  "\<Delta> MkFst x y \<in> set t \<Longrightarrow> \<star> x \<in> set t"
  apply(insert reachable, rotate_tac -1)
  apply(induct arbitrary: x rule: reachable.induct)
  apply(auto dest!: in_set_unpairMsg_casesD intro!: Knows_in_set_unpairMsgI)
  done

lemma MkSnd_in_trace_imp_Knows_snd:
  "\<Delta> MkSnd x y \<in> set t \<Longrightarrow> \<star> y \<in> set t"
  apply(insert reachable, rotate_tac -1)
  apply(induct arbitrary: x rule: reachable.induct)
  apply(auto dest!: in_set_unpairMsg_casesD intro!: Knows_in_set_unpairMsgI)
  done


lemma distinct_trace:
  "distinct t"
  apply(insert reachable, rotate_tac -1)
proof(induct rule: reachable.induct)
next
  case (recv t r s l msg tid \<alpha>)
    then interpret old_state: reachable_state P t r s by unfold_locales
    show ?case using prems(3,4)
      by(auto simp: curStep_def  split: option.splits list.splits
             dest!: old_state.todo_notin_trace)
next
  case (send t r s l msg tid m)
    then interpret old_state: reachable_state P t r s by unfold_locales
    show ?case using prems(3,4)
      by(auto simp: curStep_def  split: option.splits list.splits
              dest: in_set_unpairMsg_casesD
             dest!: old_state.todo_notin_trace
                    old_state.MkFst_in_trace_imp_Knows_fst
                    old_state.MkSnd_in_trace_imp_Knows_snd)
next 
  case (decr t r s m k)
    then interpret old_state: reachable_state P t r s by unfold_locales
    show ?case using prems(3,6-7)
      by(auto dest: in_set_unpairMsg_casesD
             dest!: old_state.MkFst_in_trace_imp_Knows_fst
                    old_state.MkSnd_in_trace_imp_Knows_snd)
next case hash thus ?case by auto
next case encr thus ?case by auto
next case tuple thus ?case by auto
next case ik0 thus ?case by auto
next case init thus ?case by auto
next case create thus ?case by auto 
qed

end

sublocale reachable_state \<subseteq> distinct_list "t"
  by(unfold_locales, rule distinct_trace)

context reachable_state begin

(*
notation 
  "directPred" (infixl "\<prec>\<^sub>1" 50) and
  "pred" (infixl "\<prec>" 50) and
  "reflPred" (infixl "\<preceq>" 50)
*)

  abbreviation 
    "next'" (infixl "\<prec>\<^sub>1" 50) where "next' \<equiv> next" 
  abbreviation "pred'" (infixl "\<prec>" 50) where "pred' \<equiv> pred"
  abbreviation "predEq'" (infixl "\<preceq>" 50) where "predEq' \<equiv>  predEq"


lemma roleOrd: 
  "\<lbrakk> r tid = Some (todo,done); 
     listOrd (rev done) prev step \<rbrakk> 
   \<Longrightarrow> \<Delta>(MkStep tid prev) \<prec> \<Delta>(MkStep tid step)"
  apply(simp add: pred_def)
  apply(insert reachable, rotate_tac -1)
  proof (induct arbitrary: tid todo "done" rule: reachable.induct)
    case init thus ?case by simp
  next
    case (create t r s tid' R \<alpha>) thus ?case
      by(auto simp: newThread_def split: if_splits)
  next
    case (send t r s l msg tid' m)
      then interpret old_state: reachable_state P t r s by unfold_locales
      show ?case using prems
      apply(clarsimp simp: nextStep_def curStep_def 
                    split: option.splits if_splits list.splits)
      by(auto dest: old_state.proto_roles old_state.todo_notin_trace 
                    old_state.done_in_trace)
  next
   case (recv t r s l msg tid')
      then interpret old_state: reachable_state P t r s by unfold_locales
      show ?case using prems(3,4,6-8)
      apply(clarsimp simp: nextStep_def curStep_def 
                    split: option.splits if_splits list.splits)
      by(auto dest: old_state.proto_roles old_state.todo_notin_trace 
                    old_state.done_in_trace)
  next case hash thus ?case by auto
  next case encr thus ?case by auto
  next case decr thus ?case by auto
  next case tuple thus ?case by auto
  next case ik0 thus ?case by auto
qed

lemma subst_dom_AVar: 
  "r tid = Some thread \<Longrightarrow> EVar (AVar a) tid \<in> dom_wts s"
  apply(insert reachable, rotate_tac -1)
  apply(induct arbitrary: tid thread rule: reachable.induct, simp_all)
  by(simp_all add: curStep_def nextStep_def split: option.splits if_splits)

lemma subst_dom_MVar:
  "\<lbrakk> r tid = Some (todo,done); Recv l msg \<in> set done; 
     MVar v \<in> FV msg
   \<rbrakk> \<Longrightarrow> 
   EVar (MVar v) tid \<in> dom_wts s"
  apply(insert reachable, rotate_tac -1)
proof(induct arbitrary: tid todo "done" rule: reachable.induct)
  case init thus ?case by simp next
  case create thus ?case 
    by(auto simp: newThread_def split: option.splits if_splits) 
next
  case (send t r s lbl msg' tid tid') thus ?case
    apply(clarsimp simp: curStep_def nextStep_def 
                  split: option.splits if_splits list.splits)
    by(auto)
next
  case (recv t r s lbl msg' tid \<alpha> tid') thus ?case
    apply(clarsimp simp: curStep_def nextStep_def 
                  split: option.splits if_splits list.splits)
    apply(thin_tac "dom_wts \<alpha> = ?X", force)
    apply(thin_tac "?x = ?y", force)
    done
qed

lemma Event_ground_unpairMsg:
  "\<lbrakk> \<Delta> e \<in> set (unpairMsg knows m); ground m \<rbrakk> \<Longrightarrow> 
   ground (eventMsg s' e)"
  apply(induct m arbitrary: knows)
  by(auto dest: in_set_unpairMsg_casesD split: if_splits)

lemma Knows_ground_unpairMsg:
  "\<lbrakk> \<star> x \<in> set (unpairMsg knows m); ground m \<rbrakk> \<Longrightarrow> 
   ground x"
  apply(induct m arbitrary: knows)
  by(auto dest: in_set_unpairMsg_casesD split: if_splits)

lemma eventMsg_Knows_ground:
  "(\<forall>e. \<Delta>(e) \<in> set t \<longrightarrow> ground (eventMsg s e)) \<and>
   (\<forall>m. \<star>(m) \<in> set t \<longrightarrow> ground m)"
  apply(insert reachable, rotate_tac -1)
proof (induct arbitrary: m e rule: reachable.induct)
  case (create t r s tid' R \<alpha>) thus ?case
    by(auto simp: eventMsg_ground_extend_wts)
next
  case (send t r s l msg tid m)
    then interpret old_state: reachable_state P t r s by unfold_locales
    show ?case using prems(3-5)
      apply(subgoal_tac "ground m")
      apply(auto intro: Event_ground_unpairMsg Knows_ground_unpairMsg)
      apply(subst ground_subst_s2e_conv_FV)
      apply(clarsimp)
      apply(case_tac v, simp_all)
      apply(frule Some_curStepD, clarsimp)
      apply(rule old_state.subst_dom_AVar, assumption)
      apply(frule Some_curStepD, clarsimp)
      apply(frule old_state.proto_roles, clarsimp)
      apply(auto dest!: Rep_role_Send_FV intro: old_state.subst_dom_MVar)
      done
next
  case (recv t r s l msg tid \<alpha>) thus ?case
    by(auto simp: eventMsg_ground_extend_wts ground_subst_s2e_conv_FV)
next 
  case (decr t r s m k) thus ?case
    by(auto dest!: Event_ground_unpairMsg Knows_ground_unpairMsg)
next case init thus ?case by auto
next case (hash t r s m) thus ?case by auto
next case ik0 thus ?case by auto
next case encr thus ?case by auto
next case tuple thus ?case by auto
qed

lemma Knows_ground:
  "\<star>(m) \<in> set t \<Longrightarrow> ground m"
  by(auto simp: eventMsg_Knows_ground)

lemma eventMsg_ground:
  "\<Delta>(e) \<in> set t \<Longrightarrow> ground (eventMsg s e)"
  by(auto simp: eventMsg_Knows_ground)

lemma Send_ground:
  assumes send: "Some (Send l msg) = curStep r tid"
  shows "ground (subst s (s2e msg tid))"
proof -
thm reachable.send
  interpret sent_state: reachable_state P
    "let m = subst s (s2e msg tid) in
     t @ [\<Delta> MkStep tid (Send l msg)] @ 
         (if \<star>(m) \<in> set t then [] else \<star> m # unpairMsg (insert m {x |x. \<star> x \<in> set t}) m)"
    "nextStep r tid" "s"
    apply(unfold_locales)
    apply(insert reachable)
    apply(drule reachable.send)
    apply(auto intro!: send simp: Let_def)
    done
  show ?thesis
    apply(rule_tac P=ground in ssubst) prefer 2
    apply(rule sent_state.eventMsg_ground, auto simp: Let_def)
    done
qed


subsubsection{* Destruction rules capturing the knowledge effect of an event *}

lemma SendD: 
  "\<Delta>(MkStep tid (Send lbl msg)) \<in> set t \<Longrightarrow> \<star>(subst s (s2e msg tid)) \<in> set t"
  apply(insert reachable, rotate_tac -1)
  apply(induct rule: reachable.induct)
  by(auto simp: extend_wts_conv_subst
          dest: reachable_state.eventMsg_ground[OF reachable_state.intro]) 

lemma FromIK0D: 
  "\<Delta>(FromIK0 m) \<in> set t \<Longrightarrow> \<star>m \<in> set t"
  by(insert reachable, rotate_tac -1, 
     induct rule: reachable.induct, auto)

lemma MkHashD: 
  "\<Delta>(MkHash m) \<in> set t \<Longrightarrow> \<star>(Hash m) \<in> set t"
  by(insert reachable, rotate_tac -1, 
     induct rule: reachable.induct, auto)

lemma MkFstD: 
  "\<Delta>(MkFst x y) \<in> set t \<Longrightarrow> \<star>x \<in> set t"
  by(insert reachable, rotate_tac -1, 
     induct rule: reachable.induct, auto dest: MkFst_in_set_unpairMsgD)

lemma MkSndD: 
  "\<Delta>(MkSnd x y) \<in> set t \<Longrightarrow> \<star>y \<in> set t"
  by(insert reachable, rotate_tac -1, 
     induct rule: reachable.induct, auto dest: MkSnd_in_set_unpairMsgD)

lemma MkTupD: 
  "\<Delta>(MkTup x y) \<in> set t \<Longrightarrow> \<star>(Tup x y) \<in> set t"
  by(insert reachable, rotate_tac -1, 
     induct rule: reachable.induct, auto)

lemma MkEncrD: 
  "\<Delta>(MkEncr m k) \<in> set t \<Longrightarrow> \<star>Enc m k \<in> set t"
  by(insert reachable, rotate_tac -1, 
     induct rule: reachable.induct, auto)

lemma MkDecrD: 
  "\<Delta>(MkDecr m k) \<in> set t \<Longrightarrow> \<star>m \<in> set t"
  by(insert reachable, rotate_tac -1, 
     induct rule: reachable.induct, auto)

end

subsection{* Relating @{term reachable} to @{term ossp} *}


fun kntrace2trace :: "kntrace \<Rightarrow> trace"
where
  "kntrace2trace [] = []"
| "kntrace2trace (\<Delta>(MkStep tid step) # kes) = (tid,step) # kntrace2trace kes"
| "kntrace2trace (_                  # kes) =              kntrace2trace kes"


lemma kntrace2trace_append [simp]: 
  "kntrace2trace (t@t') = kntrace2trace t @ kntrace2trace t'"
  by(induct t rule: kntrace2trace.induct, auto)

lemma set_kntrace2trace_conv_set [simp]:
  "set (kntrace2trace t) = 
   { (tid,step) | tid step. \<Delta>(MkStep tid step) \<in> set t}"
  by(induct t rule: kntrace2trace.induct, auto)

context reachable_state begin

lemma spies_kntrace2trace_extend_wts [simp]:
  "spies (extend_wts s \<alpha>) (kntrace2trace t) = spies s (kntrace2trace t)"
  by(force simp: spies_conv_set extend_wts_conv_subst
           dest: eventMsg_ground)

lemma kntrace2trace_unpairMsg [simp]:
  "kntrace2trace (unpairMsg knows m) = []"
  by(induct m arbitrary: knows, auto)

lemma pairParts_in_infer:
  "\<lbrakk> x \<in> pairParts m; m \<in> infer M \<rbrakk> \<Longrightarrow> x \<in> infer M"
  by(induct m arbitrary: x, auto)

lemma Knows_spies_kntrace2trace:
  "\<star>m \<in> set t \<Longrightarrow> m \<in> infer (spies s (kntrace2trace t))"
  apply(insert reachable, rotate_tac -1)
  apply(induct arbitrary: m rule: reachable.induct)
  prefer 9
  apply(subgoal_tac "m \<in> infer (spies s (kntrace2trace t))")
  apply(auto intro: infer.intros pairParts_in_infer
             split: if_splits  
              dest: in_set_unpairMsg_casesD
              simp: reachable_state.spies_kntrace2trace_extend_wts[OF reachable_state.intro])
  done

lemma in_ossp:
  "(kntrace2trace t, r, s) \<in> ossp P"
  apply(insert reachable)
  apply(induct rule: reachable.induct)
  apply(simp_all add: ossp.intros)
  apply(drule ossp.create, simp+)
  apply(rule_tac P="\<lambda>x. (kntrace2trace t,x,extend_wts s \<alpha>) \<in> ?X" in subst)
  apply(rule ext)
  apply(auto intro: ossp.intros 
            intro!: reachable_state.Knows_spies_kntrace2trace
                    reachable_state.intro)
  done

end

(*
 
lemma infer_Knows:
  "\<lbrakk> m \<in> infer M; (t,r,s) \<in> reachable P; \<forall> x \<in> M. \<star>x \<in> set t \<rbrakk>
  \<Longrightarrow> \<exists> t'. (t@t',r,s) \<in> reachable P \<and> kntrace2trace t' = [] \<and> 
            \<star>m \<in> set (t@t') \<and> (\<forall> x \<in> M. \<star>x \<notin> set t')"
proof(induct arbitrary: t rule: infer.induct)
  case (Inj m) thus ?case by(rule_tac x="[]" in exI, simp)
next
  case (Hash m) show ?case using prems(3)
    apply(simp)
    apply(drule prems(2))
    apply(rule prems)
    apply(clarsimp)
    apply(case_tac "\<star>(Hash m) \<in> set (t@t')")
    apply(rule_tac x="t'" in exI, simp)
    apply(case_tac "\<Delta>(MkHash m) \<in> set (t@t')")
    apply(drule reachable_state.MkHashD[OF reachable_state.intro])
    apply(simp+)
    apply(drule reachable.hash, simp+)
    apply(auto simp: prems(4))
    done
next
  case (Fst m x) show ?case using prems(3)
    apply(simp)
    apply(drule prems(2), rule prems, clarsimp)
    apply(case_tac "\<star>m \<in> set (t@t')")
    apply(rule_tac x="t'" in exI, simp)
    apply(case_tac "\<Delta>(MkFst m x) \<in> set (t@t')")
    apply(drule reachable_state.MkFstD[OF reachable_state.intro])
    apply(simp+)
    apply(drule reachable.fst, simp+)
    apply(auto simp: prems(4))
    done
next
  case (Snd x m) show ?case using prems(3)
    apply(simp)
    apply(drule prems(2), rule prems, clarsimp)
    apply(case_tac "\<star>m \<in> set (t@t')")
    apply(rule_tac x="t'" in exI, simp)
    apply(case_tac "\<Delta>(MkSnd x m) \<in> set (t@t')")
    apply(drule reachable_state.MkSndD[OF reachable_state.intro])
    apply(simp+)
    apply(drule reachable.snd, simp+)
    apply(auto simp: prems(4))
    done
next
  case (Tup x y) show ?case using prems(5)
    apply(simp)
    apply(drule prems(2), rule prems, clarsimp)
    apply(drule prems(4))
    apply(simp add: prems)
    apply(clarsimp)
    apply(case_tac "\<star>(Tup x y) \<in> set (t@t'@t'a)")
    apply(rule_tac x="t'@t'a" in exI, simp)
    apply(case_tac "\<Delta>(MkTup x y) \<in> set (t@t'@t'a)")
    apply(drule reachable_state.MkTupD[OF reachable_state.intro])
    apply(simp+)
    apply(drule_tac x=x and y=y in reachable.tuple)
    apply(auto simp: prems(6))
    done
next
  case (Enc m k) show ?case using prems(5)
    apply(simp)
    apply(drule prems(2), rule prems, clarsimp)
    apply(drule prems(4))
    apply(simp add: prems)
    apply(clarsimp)
    apply(case_tac "\<star>(Enc m k) \<in> set (t@t'@t'a)")
    apply(rule_tac x="t'@t'a" in exI, simp)
    apply(case_tac "\<Delta>(MkEncr m k) \<in> set (t@t'@t'a)")
    apply(drule reachable_state.MkEncrD[OF reachable_state.intro])
    apply(simp+)
    apply(drule_tac m=m and k=k in reachable.encr)
    apply(auto simp: prems(6))
    done
next
  case (Dec m k) show ?case using prems(5)
    apply(simp)
    apply(drule prems(2), rule prems, clarsimp)
    apply(drule prems(4))
    apply(simp add: prems)
    apply(clarsimp)
    apply(case_tac "\<star>m \<in> set (t@t'@t'a)")
    apply(rule_tac x="t'@t'a" in exI, simp)
    apply(case_tac "\<Delta>(MkDecr m k) \<in> set (t@t'@t'a)")
    apply(drule reachable_state.MkDecrD[OF reachable_state.intro])
    apply(simp+)
    apply(drule_tac m=m and k=k in reachable.decr)
    apply(auto simp: prems(6))
    done
qed

lemma spies_kntrace_Knows:
  "\<lbrakk> finite M; (t,r,s) \<in> reachable P; M \<subseteq> spies s (kntrace2trace t) \<rbrakk> \<Longrightarrow> 
   \<exists> t'. (t@t',r,s) \<in> reachable P \<and> 
         kntrace2trace t' = [] \<and>  (\<forall> m \<in> M. \<star>m \<in> set (t@t'))"
  apply(induct rule: finite.induct)
  apply(rule_tac x="[]" in exI, simp)
  apply(clarsimp)
  apply(thin_tac "A \<subseteq> ?X", thin_tac "(t,r,s) \<in> ?X", thin_tac "finite ?X")
  apply(clarsimp simp: spies_conv_set)
  apply(erule disjE)
  apply(case_tac "\<star>a \<in> set (t@t')")
  apply(rule_tac x="t'" in exI, simp)
  apply(case_tac "\<Delta>(FromIK0 a) \<in> set (t@t')")
  apply(drule reachable_state.FromIK0D[OF reachable_state.intro])
  apply(simp+)
  apply(drule reachable.ik0, simp+)
  apply(rule exI, rule conjI)
  apply(auto)
  apply(rule_tac x="t'" in exI)
  apply(auto dest: reachable_state.SendD[OF reachable_state.intro])
  done

lemma ossp_in_reachable:
  "(t,r,s) \<in> ossp P \<Longrightarrow>
   \<exists> t'. t = kntrace2trace t' \<and> (t',r,s) \<in> reachable P"
proof(induct rule: ossp.induct)
  case init thus ?case 
    apply(rule_tac x="[]" in exI)
    by(auto intro: reachable.intros)
next
  case (create t r s tid R \<alpha>) thus ?case
    apply(simp)
    apply(erule exE, erule conjE)
    apply(rule_tac x="t'" in exI)
    apply(simp)
    apply(drule reachable.create, simp+)
    apply(rule_tac P="\<lambda>x. (t',x,extend_wts s \<alpha>) \<in> ?X" in subst)
    apply(rule ext)
    apply(auto)
    done
next
  case (send t r s l msg tid) thus ?case
    apply(clarsimp)
    apply(rule exI, rule conjI) prefer 2
    apply(erule reachable.send, simp+)
    done
next
  case (recv t r s l msg tid \<alpha>) thus ?case
    apply(clarsimp)
    apply(drule infer_finite_support)
    apply(clarsimp)
    apply(drule spies_kntrace_Knows, assumption+)
    apply(clarsimp)
    apply(thin_tac "(t',r,s) \<in> ?X")
    apply(frule infer_Knows, simp+)
    apply(clarsimp)
    apply(rule_tac x="t' @ t'a @ t'b @ [\<Delta>(MkStep tid (Recv l msg))]" in exI)
    apply(simp)
    apply(thin_tac "(t'@t'a,r,s) \<in> ?X")
    apply(drule reachable.recv)
    apply(assumption+)
    apply(auto)
    done
qed


lemma ossp_conv_reachable:
  "ossp P = {(kntrace2trace t,r,s) | t r s. (t,r,s) \<in> reachable P}"
  by(auto intro!: ossp_in_reachable reachable_state.in_ossp
                  reachable_state.intro)

*)

end