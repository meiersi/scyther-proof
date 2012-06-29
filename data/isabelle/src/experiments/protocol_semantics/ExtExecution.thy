theory ExtExecution
imports
  "../Protocol"
  ExecMessage
  WelltypedSubst
  ThreadPool
begin

section{* Execution Model *}

subsection{* Types and Operations *}

subsubsection{* Execution Events *}

datatype execevent = 
    FromIK0 execmsg
  | MkStep tid rolestep
  | MkHash execmsg
  | MkUnt  execmsg execmsg
  | MkTup  execmsg execmsg
  | MkEncr execmsg execmsg
  | MkDecr execmsg execmsg

types trace = "execevent list"

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
| "eventMsg s (MkUnt x y)  = Tup x y"
| "eventMsg s (MkHash m)   = Hash m"
| "eventMsg s (MkEncr m k) = Enc m k"
| "eventMsg s (MkDecr m k) = Enc m k"



subsubsection{* Intruder Knowledge *}

fun knows :: "wt_subst \<Rightarrow> trace \<Rightarrow> execmsg set" 
where
  "knows s [] = {}"
| "knows s (MkStep tid (Send lbl msg) # es) = 
     insert (subst s (s2e msg tid)) (knows s es)"
| "knows s (MkStep tid (Recv lbl msg) # es) = (knows s es)"
| "knows s (FromIK0 m # es)  = insert m           (knows s es)"
| "knows s (MkTup x y # es)  = insert (Tup x y)   (knows s es)"
| "knows s (MkUnt x y # es)  = insert x (insert y (knows s es))"
| "knows s (MkHash m   # es) = insert (Hash m)    (knows s es)"
| "knows s (MkEncr m k # es) = insert (Enc m k)   (knows s es)"
| "knows s (MkDecr m k # es) = insert m           (knows s es)"


fun eout :: "wt_subst \<Rightarrow> execevent \<Rightarrow> execmsg set" 
where
  "eout s (MkStep tid (Send lbl msg)) = 
     {subst s (s2e msg tid)}"
| "eout s (MkStep tid (Recv lbl msg)) = {}"
| "eout s (FromIK0 m)                 = {m}"
| "eout s (MkTup x y )                = {Tup x y}"
| "eout s (MkUnt x y )                = {x,y}"
| "eout s (MkHash m  )                = {Hash m}"
| "eout s (MkEncr m k)                = {Enc m k}"
| "eout s (MkDecr m k)                = {m}"


subsubsection{* Reachable States during Execution *}

types state = "trace \<times> rolestep threadpool \<times> wt_subst"

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
            ran_wts \<alpha> = {Lit (EHonest a)   | a. True}
          \<rbrakk>
          \<Longrightarrow> (t, r(tid \<mapsto> newThread (Rep_role R)), extend_wts s \<alpha>) \<in> reachable P"

| send:  "\<lbrakk> (t, r, s) \<in> reachable P;
            Some (Send l msg) = curStep r tid
          \<rbrakk>
          \<Longrightarrow> (t @ [MkStep tid (Send l msg)], nextStep r tid, s) \<in> reachable P"
            
| recv:  "\<lbrakk> (t, r, s) \<in> reachable P;
            Some (Recv l msg) = curStep r tid;
            dom_wts \<alpha> = { EVar v tid | v. v \<in> FV msg };
            subst (extend_wts s \<alpha>) (s2e msg tid) \<in> knows s t
          \<rbrakk>
          \<Longrightarrow> (t @ [MkStep tid (Recv l msg)], nextStep r tid, extend_wts s \<alpha>) \<in> reachable P"

| ik0:   "\<lbrakk> (t, r, s) \<in> reachable P;
            m \<in> IK0
          \<rbrakk>
          \<Longrightarrow> (t @ [FromIK0 m], r, s) \<in> reachable P"

| hash:  "\<lbrakk> (t, r, s) \<in> reachable P;
            m \<in> knows s t
          \<rbrakk>
          \<Longrightarrow> (t @ [MkHash m], r, s) \<in> reachable P"

| tuple: "\<lbrakk> (t, r, s) \<in> reachable P;
            x \<in> knows s t;
            y \<in> knows s t
          \<rbrakk>
          \<Longrightarrow> (t @ [MkTup x y], r, s) \<in> reachable P"

| untup: "\<lbrakk> (t, r, s) \<in> reachable P;
            Tup x y \<in> knows s t
          \<rbrakk>
          \<Longrightarrow> (t @ [MkUnt x y], r, s) \<in> reachable P"

| encr:  "\<lbrakk> (t, r, s) \<in> reachable P;
            m \<in> knows s t;
            k \<in> knows s t
          \<rbrakk>
          \<Longrightarrow> (t @ [MkEncr m k], r, s) \<in> reachable P"


| decr:  "\<lbrakk> (t, r, s) \<in> reachable P;
            Enc m k \<in> knows s t;
            inv k \<in> knows s t
          \<rbrakk>
          \<Longrightarrow> (t @ [MkDecr m k], r, s) \<in> reachable P"



subsection{* Properties *}

subsubsection{* Execution Events *}


lemma eventMsg_ground_extend_wts:
  "ground (eventMsg s e) \<Longrightarrow>
   eventMsg (extend_wts s s') e = eventMsg s e"
  apply(induct rule: eventMsg.induct)
  by(simp_all add: extend_wts_conv_subst)

lemma knows_append[simp]: 
  "knows s (t @ t') = knows s t \<union> knows s t'"
  by(induct t rule: knows.induct, auto )

lemma knows_MkHash: "MkHash m \<in> set t \<Longrightarrow> Hash m \<in> knows s t"
  by(induct t rule: knows.induct, auto )

lemma knows_MkTup: "MkTup x y \<in> set t \<Longrightarrow> Tup x y \<in> knows s t"
  by(induct t rule: knows.induct, auto )

lemma knows_MkUnt1: "MkUnt x y \<in> set t \<Longrightarrow> x \<in> knows s t"
  by(induct t rule: knows.induct, auto )

lemma knows_MkUnt2: "MkUnt x y \<in> set t \<Longrightarrow> y \<in> knows s t"
  by(induct t rule: knows.induct, auto )

lemma knows_MkEncr: "MkEncr m k \<in> set t \<Longrightarrow> Enc m k \<in> knows s t"
  by(induct t rule: knows.induct, auto )

lemma knows_MkDecr: "MkDecr m k \<in> set t \<Longrightarrow> m \<in> knows s t"
  by(induct t rule: knows.induct, auto )


lemma knows_ground_extend_wts:
  "\<lbrakk> \<And> m. m \<in> knows s t \<Longrightarrow> ground m \<rbrakk> \<Longrightarrow>
   knows (extend_wts s s') t = knows s t"
  apply(induct rule: knows.induct)
  apply(simp_all add: extend_wts_conv_subst)
  done

lemma eout_ground_by_eventMsg_ground:
  "\<lbrakk> m \<in> eout s e; ground (eventMsg s e) \<rbrakk> \<Longrightarrow> ground m"
  by(induct e rule: eout.induct, auto)

lemma knows_conv_eout: 
  "knows s t = (\<Union> e \<in> set t. eout s e)"
  by(induct t rule: knows.induct, auto)


subsubsection{* Reachable States *}


lemma reachable_proto_roles:
  "\<lbrakk> (t,r,s) \<in> reachable P; r tid = Some (todo,done) \<rbrakk> 
  \<Longrightarrow> \<exists> R \<in> P. Rep_role R = rev done @ todo"
  apply(induct arbitrary: tid todo "done" rule: reachable.induct)
  apply(auto simp: newThread_def curStep_def nextStep_def split: if_splits option.splits list.splits)
  done

lemma reachable_Step_in_threadpool: 
  "\<lbrakk> MkStep tid step \<in> set t; (t,r,s) \<in> reachable P \<rbrakk> 
  \<Longrightarrow> \<exists> todo done. r tid = Some (todo,done)"
  by(rotate_tac 1, induct rule: reachable.induct, auto simp: nextStep_def)

lemma reachable_todo_notin_trace: 
  "\<lbrakk> r tid = Some (todo,done); step \<in> set todo; (t,r,s) \<in> reachable P \<rbrakk> \<Longrightarrow> 
     MkStep tid step \<notin> set t"
  apply(rotate_tac -1)
  proof(induct arbitrary: tid todo "done" rule: reachable.induct)
    case init thus ?case by simp next
    case (create t r s tid' R \<alpha>) thus ?case
      apply(clarsimp simp: newThread_def curStep_def split: option.splits if_splits)
      apply(drule reachable_Step_in_threadpool, assumption, simp)
      apply(auto)
      done
  next
    case (send t r s l msg tid') thus ?case 
      apply(clarsimp simp: nextStep_def curStep_def 
                    split: option.splits if_splits list.splits)
      apply(drule reachable_proto_roles, assumption)
      apply(clarsimp)
      apply(subgoal_tac "distinct (Rep_role R)")
      apply(force)
      apply(rule Rep_role_distinct)
      apply(force)
      done
  next
    case (recv t r s l msg tid \<alpha> tid' todo "done") thus ?case
      apply(clarsimp simp: nextStep_def curStep_def 
                    split: option.splits if_splits list.splits)
      apply(drule reachable_proto_roles, assumption)
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
  next case untup thus ?case by auto
  next case ik0 thus ?case by auto
qed

lemma reachable_done_in_trace: 
  "\<lbrakk> r tid = Some (todo,done); step \<in> set done; (t,r,s) \<in> reachable P \<rbrakk> \<Longrightarrow> 
     MkStep tid step \<in> set t"
  apply(rotate_tac -1)
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
  next case untup thus ?case by auto
  next case ik0 thus ?case by auto
qed

lemma reachable_roleOrd: 
  "\<lbrakk> (t, r, s) \<in> reachable P; r tid = Some (todo,done); 
     (prev, step) \<in> listOrd (rev done) \<rbrakk> 
   \<Longrightarrow> (MkStep tid prev, MkStep tid step) \<in> listOrd (rev (remdups (rev t)))"
  proof (induct arbitrary: tid todo "done" rule: reachable.induct)
    case init thus ?case by simp
  next
    case (create t r s tid' R \<alpha>) thus ?case
      by(auto simp: newThread_def split: if_splits)
  next
   case (send t r s l msg tid') thus ?case 
      apply(clarsimp simp: nextStep_def curStep_def 
                    split: option.splits if_splits list.splits)
      apply(frule reachable_proto_roles, assumption)
      apply(auto dest: reachable_todo_notin_trace reachable_done_in_trace)
      apply(force)
      done
  next
   case (recv t r s l msg tid') thus ?case
      apply(thin_tac "dom_wts ?x = ?X")
      apply(clarsimp simp: nextStep_def curStep_def 
                    split: option.splits if_splits list.splits)
      apply(frule reachable_proto_roles, assumption)
      apply(auto dest: reachable_todo_notin_trace reachable_done_in_trace)
      apply(force)
      done
  next case hash thus ?case by auto
  next case encr thus ?case by auto
  next case decr thus ?case by auto
  next case tuple thus ?case by auto
  next case untup thus ?case by auto
  next case ik0 thus ?case by auto
qed


lemma reachable_subst_dom_AVar: 
  "\<lbrakk> (t,r,s) \<in> reachable P; r tid = Some thread \<rbrakk> 
  \<Longrightarrow> EVar (AVar a) tid \<in> dom_wts s"
  apply(induct arbitrary: tid thread rule: reachable.induct, simp_all)
  by(simp_all add: curStep_def nextStep_def split: option.splits if_splits)


lemma reachable_subst_dom_MVar:
  "\<lbrakk> (t,r,s) \<in> reachable P;
     r tid = Some (todo,done); Recv l msg \<in> set done; 
     MVar v \<in> FV msg
   \<rbrakk> \<Longrightarrow> 
   EVar (MVar v) tid \<in> dom_wts s"
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
next
  case hash thus ?case by auto next
  case tuple thus ?case by auto next
  case encr thus ?case by auto next
  case decr thus ?case by auto next
  case ik0 thus ?case by auto
qed


lemma reachable_eventMsg_ground:
  "\<lbrakk> (t,r,s) \<in> reachable P; e \<in> set t \<rbrakk> \<Longrightarrow> ground (eventMsg s e)"
proof (induct arbitrary: m e rule: reachable.induct)
  case init thus ?case by auto
next
  case (hash t r s m m') thus ?case
    apply(auto simp add: knows_conv_eout)
    apply(force dest: eout_ground_by_eventMsg_ground)
    done
next
  case ik0 thus ?case by auto
next
  case encr thus ?case
    apply(auto simp add: knows_conv_eout)
    apply(auto dest: eout_ground_by_eventMsg_ground)
    done
next
  case (decr t r s m k m') thus ?case
    apply(auto simp add: knows_conv_eout)
    apply(auto dest: eout_ground_by_eventMsg_ground)
    done
next
  case tuple thus ?case
    apply(auto simp add: knows_conv_eout)
    apply(auto dest: eout_ground_by_eventMsg_ground)
    done
next
  case (untup t r s x y m) thus ?case
    apply(auto simp add: knows_conv_eout)
    apply(auto dest: eout_ground_by_eventMsg_ground)
    done
next
  case (create t r s tid' R \<alpha> m) thus ?case
    by(auto simp: eventMsg_ground_extend_wts)
next
  case (send t r s l msg tid m) thus ?case
    apply(auto)
    apply(subst ground_subst_s2e_conv_FV)
    apply(clarsimp)
    apply(case_tac v, simp_all)
    apply(drule Some_curStepD, clarsimp)
    apply(rule reachable_subst_dom_AVar, assumption+)
    apply(drule Some_curStepD, clarsimp)
    apply(frule reachable_proto_roles, assumption, clarsimp)
    apply(auto dest!: Rep_role_Send_FV intro: reachable_subst_dom_MVar)
    done
next
  case (recv t r s l msg tid \<alpha> m) thus ?case
    by(auto simp: eventMsg_ground_extend_wts ground_subst_s2e_conv_FV)
qed

lemma reachable_Send_ground:
  "\<lbrakk> (t,r,s) \<in> reachable P;
     Some (Send l msg) = curStep r tid
   \<rbrakk>
   \<Longrightarrow> ground (subst s (s2e msg tid))"
  apply(subgoal_tac 
   "(t@[MkStep tid (Send l msg)],nextStep r tid,s) \<in> reachable P")
  apply(auto dest: reachable_eventMsg_ground intro!: reachable.send)
  done

lemma reachable_knows_ground:
  "\<lbrakk> (t,r,s) \<in> reachable P; m \<in> knows s t \<rbrakk> \<Longrightarrow> ground m"
  by(auto simp: reachable_eventMsg_ground knows_conv_eout 
         elim!: eout_ground_by_eventMsg_ground)

lemma reachable_eout_ground:
  "\<lbrakk> (t,r,s) \<in> reachable P; e \<in> set t; m \<in> eout s e; m \<notin> IK0 \<rbrakk> 
   \<Longrightarrow> ground m"
  by(auto dest!: reachable_knows_ground simp: knows_conv_eout)

lemma reachable_eout_extend_wts [simp]:
  "\<lbrakk> (t,r,s) \<in> reachable P; e \<in> set t \<rbrakk> \<Longrightarrow>
   eout (extend_wts s \<alpha>) e = eout s e"
  apply(induct rule: eout.induct)
  apply(auto dest: reachable_eventMsg_ground 
             simp: extend_wts_conv_subst)
  done

lemma reachable_knows_extend_wts [simp]:
  "(t,r,s) \<in> reachable P \<Longrightarrow> knows (extend_wts s s') t = knows s t"
  by(simp add: knows_conv_eout)



end