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
theory ExplicitModel
imports
  HOL_ext
  Hints
  Protocol
  ExecMessage
begin



chapter{* Security Proofs *}

section{* Explicit Execution Model *}

datatype rawevent = 
    Step "tid \<times> rolestep"
  | Learns "execmsg set"
  | LKReveal id


datatype reveal =  
  RCompr notetype tid
| RLKR execmsg

types explicit_trace = "rawevent list"
types execstep = "tid \<times> rolestep"
types threadpool = "tid \<rightharpoonup> (rolestep list \<times> rolestep list \<times> rolestep set)"

fun knows :: "explicit_trace \<Rightarrow> execmsg set"
where
  "knows [] = {}"
| "knows (Learns M # t) = M \<union> knows t"
| "knows (Step estep # t) = knows t"
| "knows (LKReveal a # t) = knows t"

fun steps :: "explicit_trace \<Rightarrow> execstep set"
where
  "steps [] = {}"
| "steps (Learns M # t) = steps t"
| "steps (Step estep # t) = insert estep (steps t)"
| "steps (LKReveal a # t) = steps t"

fun reveals :: "explicit_trace \<Rightarrow> reveal set"
where
  "reveals (Step (i, s) # xs)  = 
     (if (noteStep s) then
        insert (RCompr (noteType s) i) (reveals xs)
      else
        reveals xs)"
| "reveals (Learns m # xs) = reveals xs"
| "reveals (LKReveal a # xs) =  insert (RLKR (Lit (EAgent a))) (reveals xs)"
| "reveals [] = {}"

fun lkreveals :: "explicit_trace \<Rightarrow> execmsg set"
where
  "lkreveals [] = {}"
| "lkreveals (Learns M # t) = lkreveals t"
| "lkreveals (Step estep # t) = lkreveals t"
| "lkreveals (LKReveal a # t) = insert (Lit (EAgent a)) (lkreveals t)"

definition longTermKeys :: "id \<Rightarrow> execmsg set"
where
  "longTermKeys a =  { SK (Lit (EAgent a)) } \<union>
                     { K (Lit (EAgent a)) b | b. b \<in> Agent } \<union> 
                     { K b (Lit (EAgent a)) | b. b \<in> Agent } \<union> 
                     { KShr A | A. a \<in> A }"
                    
lemma SK_in_longTermKeys [iff]:
  "(SK x \<in>  longTermKeys a) = (x = (Lit (EAgent a)))"
  by (auto simp: longTermKeys_def)

lemma K_in_longTermKeys [iff]:
  "(K x y \<in> longTermKeys a) = 
   ( (x = (Lit (EAgent a)) \<and> y \<in> Agent) \<or> 
     (y = (Lit (EAgent a)) \<and> x \<in> Agent) 
   )"
  by (auto simp: longTermKeys_def)

lemma KShr_in_longTermKeys [iff]:
  "(KShr A \<in> longTermKeys a) = (a \<in> A)"
  by (auto simp: longTermKeys_def)

lemma notin_longTermKeys [iff]:
  "Hash m \<notin> longTermKeys a"
  "Tup x y \<notin> longTermKeys a"
  "Enc m k \<notin> longTermKeys a"
by (auto simp: longTermKeys_def)

lemma longTermKeys_conv: 
  "(m \<in> longTermKeys a) = 
   ( (m = SK (Lit (EAgent a))) \<or> 
     (\<exists> b \<in> Agent. m = K (Lit (EAgent a)) b \<or> 
                   m = K b (Lit (EAgent a))
     ) \<or> 
     (\<exists> A. m = KShr A \<and> a \<in> A)
   )"
  by (auto simp: longTermKeys_def)


types state = "explicit_trace \<times> threadpool \<times> store"

inductive_set 
  reachable :: "proto \<Rightarrow> state set" 
  for P     :: "proto"
where
  init:  "\<lbrakk> \<forall> i done todo skipped. r i = Some (done,todo,skipped) \<longrightarrow>  done = [] \<and> skipped = {} \<and> todo \<in> P;
            \<forall> a i. s (AVar a, i) \<in> Agent
          \<rbrakk>
          \<Longrightarrow> ([Learns IK0], r, s) \<in> reachable P"
 
| compr: "\<lbrakk> (t, r, s) \<in> reachable P;
            r i = Some (done, Note l ty pt # todo, skipped);
            Some m = inst s i pt
          \<rbrakk>
          \<Longrightarrow> (t @ [Step (i,Note l ty pt), Learns (pairParts m - knows t)], r(i \<mapsto> (done @ [Note l ty pt], todo, skipped)), s) \<in> reachable P"

| skip:  "\<lbrakk> (t, r, s) \<in> reachable P;
            r i = Some (done, Note l ty pt # todo, skipped)
          \<rbrakk> 
          \<Longrightarrow> (t,  r(i \<mapsto> (done @ [Note l ty pt], todo, insert (Note l ty pt) skipped)), s) \<in> reachable P"

| lkr:   "\<lbrakk> (t, r, s) \<in> reachable P;
            LKReveal a \<notin> set t
          \<rbrakk>
          \<Longrightarrow> (t @ [LKReveal a, Learns (longTermKeys a - knows t)], r, s) \<in> reachable P"

| send:  "\<lbrakk> (t, r, s) \<in> reachable P;
            r i = Some (done, Send l pt # todo, skipped);
            Some m = inst s i pt
          \<rbrakk>
          \<Longrightarrow> (t @ [Step (i, Send l pt), Learns (pairParts m - knows t)], r(i \<mapsto> (done @ [Send l pt], todo, skipped)), s) \<in> reachable P"
            
| recv:  "\<lbrakk> (t, r, s) \<in> reachable P;
            r i = Some (done, Recv l pt # todo, skipped);
            Some m = inst s i pt;
            m \<in> knows t
          \<rbrakk>
          \<Longrightarrow> (t @ [Step (i, Recv l pt)], r(i \<mapsto> (done @ [Recv l pt], todo, skipped)), s) \<in> reachable P"

| hash:  "\<lbrakk> (t, r, s) \<in> reachable P;
            m \<in> knows t;
            Hash m \<notin> knows t
          \<rbrakk>
          \<Longrightarrow> (t @ [Learns {Hash m}], r, s) \<in> reachable P"

| tuple: "\<lbrakk> (t, r, s) \<in> reachable P;
            x \<in> knows t;
            y \<in> knows t;
            Tup x y \<notin> knows t
          \<rbrakk>
          \<Longrightarrow> (t @ [Learns {Tup x y}], r, s) \<in> reachable P"

| encr:  "\<lbrakk> (t, r, s) \<in> reachable P;
            m \<in> knows t;
            k \<in> knows t;
            Enc m k \<notin> knows t
          \<rbrakk>
          \<Longrightarrow> (t @ [Learns {Enc m k}], r, s) \<in> reachable P"


| decr:  "\<lbrakk> (t, r, s) \<in> reachable P;
            Enc m k \<in> knows t;
            inv k \<in> knows t
          \<rbrakk>
          \<Longrightarrow> (t @ [Learns (pairParts m - knows t)], r, s) \<in> reachable P"

locale reachable_state =  wf_proto +
  fixes t :: explicit_trace
  and   r :: threadpool
  and   s :: store
  assumes reachable [simp,intro!]: "(t,r,s) \<in> reachable P"
begin
  text{* A local variant of the induction rule of @{term "reachable"}. *}
  lemmas reachable_induct = reachable.induct
    [ OF reachable
    , rule_format
    , consumes 0
    , case_names init compr skip lkr send recv hash tuple encr decr
    ]
end

text{* An extension of the reachable state locale denoting
       an individual thread and its state. *}

locale reachable_thread = reachable_state +
  fixes i       :: "tid"
    and "done"  :: "rolestep list"
    and todo    :: "rolestep list"
    and skipped :: "rolestep set" 
  assumes thread_exists: "r i = Some (done, todo, skipped)"
begin

text{* The thread state is built such that @{term "done @ todo"} is
         always a role of @{term P}. *}

lemma role_in_P:  "done @ todo \<in> P"
using thread_exists
proof (induct arbitrary: i "done" todo skipped rule: reachable_induct)
qed (fastsimp split: if_splits)+

end

text{* Importing all lemmas of the wellformed role locale for
the term @{term "done @ todo"}. *}
sublocale reachable_thread \<subseteq> wf_role "done @ todo"
  by (rule wf_roles[OF role_in_P])



subsection{* Basic Properties *}

lemma knowsI: "\<lbrakk> Learns M \<in> set t; m \<in> M \<rbrakk> \<Longrightarrow> m \<in> knows t"
  by(induct t rule: knows.induct, auto)

lemma knowsD: "m \<in> knows t \<Longrightarrow> \<exists> M. Learns M \<in> set t \<and> m \<in> M"
  by(induct t rule: steps.induct, auto)

lemma knows_append [simp]: 
  "knows (xs@ys) = knows xs \<union> knows ys"
  by(induct xs rule: knows.induct, auto)

lemma stepsI: "Step estep \<in> set t \<Longrightarrow> estep \<in> steps t"
  by(induct t rule: steps.induct, auto)

lemma stepsD: "estep \<in> steps t \<Longrightarrow> Step estep \<in> set t"
  by(induct t rule: steps.induct, auto)

lemma Step_in_set_conv [simp]: 
  "(Step estep \<in> set t) = (estep \<in> steps t)"
  by(auto intro!: stepsI stepsD)

lemma steps_append [simp]: 
  "steps (t@t') = steps t \<union> steps t'"
  by(induct t rule: steps.induct, auto)

lemma lkrevealsI: "LKReveal a \<in> set t \<Longrightarrow> (Lit (EAgent a)) \<in> lkreveals t"
  by(induct t rule: lkreveals.induct, auto)

lemma lkrevealsD: "(Lit (EAgent a)) \<in> lkreveals t \<Longrightarrow> LKReveal a \<in> set t"
  by(induct t rule: lkreveals.induct, auto)

lemma Lkr_in_set_conv [simp]: 
  "(LKReveal a \<in> set t) = ((Lit (EAgent a)) \<in> lkreveals t)"
  by(auto intro!: lkrevealsI lkrevealsD)

lemma lkreveals_append [simp]: 
  "lkreveals (t@t') = lkreveals t \<union> lkreveals t'"
  by(induct t rule: lkreveals.induct, auto)

lemma lkreveals_agent: 
  "a \<in> lkreveals t \<Longrightarrow> \<exists> b. a = (Lit (EAgent b))"
  by(induct t rule: lkreveals.induct, auto)

subsection{* Thread Execution *}

lemma (in reachable_state) step_in_dom: 
  "(i, step) \<in> steps t \<Longrightarrow> i \<in> dom r"
proof (induct rule: reachable_induct) qed auto

lemma reveals_Nil[dest!]:
  "a \<in> reveals [] \<Longrightarrow> False"
by (auto)

lemma reveals_append [simp]:
  "reveals (xs@ys) = reveals xs \<union> reveals ys"
by(induct xs rule: reveals.induct, auto)

lemma RLKR_lkreveals_conv:
  "(RLKR a \<in> reveals t) = (a \<in> lkreveals t)"
proof(induct t rule: reveals.induct)
  case (1 i s xs)
  thus ?case by force
qed auto

lemma steps_to_reveals:
  "(i, Note l ty pt) \<in> steps t \<Longrightarrow> RCompr ty i \<in> reveals t"
by(induct t rule: reveals.induct) (auto)

lemma reveals_to_steps:
  "RCompr ty i \<in> reveals t \<Longrightarrow> \<exists> l pt. (i, Note l ty pt) \<in> steps t"
proof(induct t rule: reveals.induct)
  case (1 i' s xs)
  thus ?case by (cases s) auto
qed auto

lemma RCompr_steps_conv:
  "RCompr ty i \<in> reveals t = (\<exists> l pt. (i, Note l ty pt) \<in> steps t)"
by (fastsimp intro: reveals_to_steps steps_to_reveals)

context reachable_thread
begin

lemma in_dom_r [iff]: "i \<in> dom r" 
  by (auto intro!: thread_exists)

lemma distinct_done [iff]: "distinct done"
  using distinct by auto

lemma skipped_in_done: 
  "step \<in> skipped \<Longrightarrow> step \<in> set done"
using thread_exists
proof (induct arbitrary: i "done" skipped todo rule: reachable_induct)
qed (auto split: if_splits)+

lemma distinct_todo [iff]: "distinct todo"
using distinct by auto


(*
 
 Proofs of the relationship between steps, skipped and done 

 ********************************************************************************************)

lemma note_in_skipped: 
  "\<lbrakk> step \<in> skipped \<rbrakk> \<Longrightarrow> 
   \<exists> l ty pt. (step = (Note l ty pt))"
using thread_exists
proof(induct arbitrary: i "done" todo skipped rule: reachable_induct)
  case init
  thus "?case" by fastsimp
qed( auto split: if_splits)


lemma send_notin_skipped [iff]: 
  "Send l pt \<notin> skipped"
 by (auto dest!: note_in_skipped)

lemma recv_notin_skipped [iff]: 
  "Recv l pt \<notin> skipped"
 by (auto dest!: note_in_skipped)

lemma in_steps_conv_done_skipped:
  "(i, step) \<in> steps t = 
   (step \<in> set done \<and> step \<notin> skipped)"
using thread_exists
using distinct
proof(induct arbitrary: i "done" todo skipped rule: reachable_induct)
  case init thus ?case by fastsimp
next 
  case (send t r s i "done" l pt todo skipped m i' done' todo' skipped')
  thus ?case
  proof(cases "i = i'")
    case True
    then interpret thread: 
      reachable_thread P t r s i "done" "Send l pt # todo" skipped'
      using send by unfold_locales auto
    thus ?thesis 
      using send `i = i'` by fastsimp 
  qed auto
next
  case (recv t r s i "done" l pt todo skipped m i' done' todo' skipped')
  thus ?case
  proof(cases "i = i'")
    case True
    then interpret thread: 
      reachable_thread P t r s i "done" "Recv l pt # todo" skipped'
      using recv by unfold_locales auto
    thus ?thesis 
      using recv `i = i'` by fastsimp 
  qed auto
next
  case (compr t r s i "done" l ty pt todo skipped m i' done' todo' skipped')  
  thus ?case
  proof(cases "i = i'")
    case True
    thus ?thesis using compr `i = i'`
    proof(cases "step = Note l ty pt")
       case True
      interpret thread:
        reachable_thread P t r s i "done" "Note l ty pt # todo" skipped'
        using compr  `i = i'` by unfold_locales auto
      thus ?thesis using compr  `i = i'` `step = Note l ty pt` by (fastsimp dest: thread.skipped_in_done )
    qed fastsimp
  qed auto
next
  case(skip t r s i "done" l ty pt todo skipped i' done' todo' skipped')
  thus ?case
  proof(cases "i = i'")
    case True
    thus ?thesis using skip `i = i'`
    proof(cases "step = Note l ty pt")
      case True
      interpret thread:
        reachable_thread P t r s i "done" "Note l ty pt # todo" skipped
        using skip  `i = i'` by unfold_locales auto
      thus ?thesis using skip  `i = i'` `step = Note l ty pt` by fastsimp
    qed fastsimp
 qed auto
qed auto

lemma in_steps_recv:
  "((Recv l pt) \<in> set done) = ((i,Recv l pt) \<in> steps t)"
using thread_exists
proof(induct arbitrary: i "done" todo skipped rule rule: reachable_induct)
  case init
    thus "?case" by fastsimp
qed ((unfold map_upd_Some_unfold)?, auto)+

lemma in_steps_send:
  "((Send l pt) \<in> set done) = ((i,Send l pt) \<in> steps t)"
using thread_exists
proof(induct arbitrary: i "done" todo skipped rule rule: reachable_induct)
  case init
    thus "?case" by fastsimp
qed ((unfold map_upd_Some_unfold)?, auto)+

lemmas send_steps_in_done [elim!] = iffD1[OF in_steps_send, rule_format]
lemmas send_done_in_steps [elim!] = iffD2[OF in_steps_send, rule_format]
lemmas recv_steps_in_done [elim!] = iffD1[OF in_steps_recv, rule_format]
lemmas recv_done_in_steps [elim!] = iffD2[OF in_steps_recv, rule_format]


lemma in_steps_eq_in_done:
  "step \<notin> skipped \<Longrightarrow> ((i, step) \<in> steps t) = (step \<in> set done)" 
using thread_exists
by(auto simp add: in_steps_conv_done_skipped)

lemma todo_notin_doneD:
  "step \<in> set todo \<Longrightarrow> step \<notin> set done"
using distinct
using role_in_P
by(auto)

lemma done_notin_todoD:
  "step \<in> set done \<Longrightarrow> step \<notin> set todo"
using distinct
using role_in_P
by(auto)

lemma todo_notin_skippedD:
  "step \<in> set todo \<Longrightarrow> step \<notin> skipped"
using distinct
using role_in_P
by(fastsimp dest: skipped_in_done)

lemma skipped_notin_todoD:
  "step \<in> skipped \<Longrightarrow> step \<notin> set todo"
using distinct
using role_in_P
by(fastsimp dest: skipped_in_done)

lemma notin_steps_notin_trace:
  "(i, step) \<notin> steps t \<Longrightarrow> (Step (i, step)) \<notin> set t"
by(auto)

lemma in_steps_in_done:
  assumes inSteps:
    "(i, step) \<in> steps t"
  shows 
    "step \<in> set done"
proof(cases step)
  case (Send l pt)
    thus ?thesis using inSteps by (fastsimp dest: in_steps_send[THEN iffD2])
next
  case (Recv l pt)
    thus ?thesis using inSteps by (fastsimp dest: in_steps_recv[THEN iffD2])
next
  case (Note l ty pt)
    thus ?thesis using inSteps by (fastsimp simp add: in_steps_conv_done_skipped)
qed


lemma step_notin_skippedD [dest]:
  "\<lbrakk> step \<in> skipped; (i, step) \<in> steps t \<rbrakk> \<Longrightarrow> False"
by(auto simp add: in_steps_conv_done_skipped)

lemma notin_skipped_notin_steps [dest]:
  "\<lbrakk> step \<in> set done; (i, step) \<notin> steps t; step \<notin> skipped \<rbrakk> \<Longrightarrow> False"
by(auto simp add: in_steps_conv_done_skipped)

lemma[dest]:
  "\<lbrakk> step \<in> set todo; step \<in> set done \<rbrakk> \<Longrightarrow> False"
by(fastsimp dest: todo_notin_doneD)

lemma[dest]:
  "\<lbrakk> step \<in> set todo; step \<in> skipped \<rbrakk> \<Longrightarrow> False"
by(auto dest: todo_notin_skippedD)

lemma[dest]:
  "\<lbrakk> (i, step) \<notin>  steps t; (Step (i, step)) \<in> set t \<rbrakk> \<Longrightarrow> False"
by(auto)

lemma[dest]:
  "\<lbrakk> (i, step) \<in> steps t; (Step (i, step)) \<notin> set t \<rbrakk> \<Longrightarrow> False"
by(auto)

lemma listOrd_done_imp_listOrd_trace:
  assumes facts:
    "listOrd done prev step"
    "prev \<notin> skipped"
    "step \<notin> skipped" 
  shows stepOrd:
    "listOrd t (Step (i, prev)) (Step (i, step))"
using thread_exists
using facts
proof(induct arbitrary: i "done" todo skipped rule: reachable_induct)
  case (init r s i "done" todo) 
  thus ?case
    by fastsimp
next
  case (send t r s i "done" l msg todo skipped m i' done' todo' skipped')
  thus ?case using send 
 proof(cases "i = i'")
    case True
      interpret this_thread:
          reachable_thread P t r s i' "done" "Send l msg # todo'" skipped'
          using send `i = i'` by unfold_locales auto
       thus ?thesis using send `i = i'`
          by fastsimp
  qed fastsimp
next
  case (recv t r s i "done" l msg todo skipped m i' done' todo' skipped')
  from recv show ?case 
  proof(cases "i = i'")
    case True
      interpret this_thread:
          reachable_thread P t r s i' "done" "Recv l msg # todo'" skipped'
          using recv `i = i'` by unfold_locales auto
       thus ?thesis using recv `i = i'`
          by fastsimp
  qed fastsimp
next
  case (compr t r s i "done" l ty msg todo skipped m i' done' todo' skipped')
  from compr show ?case 
  proof(cases "i = i'")
    case True
      interpret this_thread:
          reachable_thread P t r s i' "done" "Note l ty msg # todo'" skipped'
          using compr `i = i'` by unfold_locales auto
       thus ?thesis using compr `i = i'`
          by fastsimp
  qed fastsimp
next
  case (skip t r s i "done" l ty msg todo skipped i' done' todo' skipped') 
  from skip show ?case 
  proof(cases "i = i'")
    case True
    then interpret this_thread:
      reachable_thread P t r s i "done" "Note l ty msg # todo" skipped
      using skip `i = i'` by unfold_locales auto
    thus ?thesis using skip `i = i'`
      by fastsimp
  qed fastsimp
qed auto

lemma listOrd_recv_role_imp_listOrd_trace:
  assumes facts:
    "(i, step) \<in> steps t"
    "listOrd (done @ todo) (Recv l pt) step"
  shows rtOrd:
    "listOrd t (Step (i, Recv l pt)) (Step (i, step))" 
using distinct
using facts
by(auto dest: in_set_listOrd1 todo_notin_doneD listOrd_done_imp_listOrd_trace in_set_listOrd2  listOrd_append[THEN iffD1] in_steps_conv_done_skipped[THEN iffD1])

lemma listOrd_send_role_imp_listOrd_trace:
  assumes facts:
    "(i, step) \<in> steps t"
    "listOrd (done @ todo) (Send l pt) step"
  shows stOrd:
    "listOrd t (Step (i, Send l pt)) (Step (i, step))" 
using distinct
using facts
by(auto dest: in_set_listOrd1 todo_notin_doneD listOrd_done_imp_listOrd_trace in_set_listOrd2  listOrd_append[THEN iffD1] in_steps_conv_done_skipped[THEN iffD1])

lemma roleOrd_notSkipped_imp_listOrd_trace:
  assumes facts:
    "(i, step) \<in> steps t"
    "step' \<notin> skipped"
    "listOrd (done @ todo)  step' step"
  shows
    "listOrd t (Step (i, step')) (Step  (i, step))"
using distinct
using facts
by(auto dest: in_set_listOrd1 todo_notin_doneD listOrd_done_imp_listOrd_trace in_set_listOrd2  listOrd_append[THEN iffD1] in_steps_conv_done_skipped[THEN iffD1])

end


subsection{* Variable Substitutions *}

context reachable_state
begin

lemma inst_AVar_cases: 
  "s (AVar v, i) \<in> Agent"
 by (induct rule: reachable_induct, auto)

lemma inst_AVar_in_IK0: 
 "s (AVar v, i) \<in> IK0"
using inst_AVar_cases[of v i] 
by (auto simp: IK0_def Agent_def)

lemma knows_IK0: "m \<in> IK0 \<Longrightarrow> m \<in> knows t"
 by(induct rule: reachable_induct, auto)

lemma inst_AVar_in_knows [iff]:
  "s (AVar a, i) \<in> knows t"
  by (rule knows_IK0[OF inst_AVar_in_IK0])

end (* reachable_state *)

lemma (in reachable_state) send_step_FV:
  assumes thread_exists: "r i = Some (done, Send l msg # todo, skipped)"
  and FV: "MVar n \<in> FV msg"
  shows "\<exists> l' msg'. (i, Recv l' msg') \<in> steps t \<and>  MVar n \<in> FV msg'"
proof -
  interpret this_thread: reachable_thread P t r s i "done" "Send l msg # todo" skipped
    using thread_exists by unfold_locales auto
  let ?role = "done @ Send l msg # todo"
  have "Send l msg \<in> set ?role" by simp
  then obtain l' msg' 
    where "listOrd ?role (Recv l' msg') (Send l msg)"
    and "MVar n \<in> FV msg'"
    using FV by(fast dest!: this_thread.Send_FV)
  thus ?thesis using this_thread.distinct
    by(auto dest: in_set_listOrd1 in_set_listOrd2)
qed

lemma (in reachable_state) note_step_FV:
  assumes thread_exists: "r i = Some (done, Note l ty msg # todo, skipped)"
  and FV: "MVar n \<in> FV msg"
  shows "\<exists> l' msg'. (i, Recv l'  msg') \<in> steps t \<and>  MVar n \<in> FV msg'"
proof -
  interpret this_thread: reachable_thread P t r s i "done" "Note l ty msg # todo" skipped
    using thread_exists by unfold_locales auto
  let ?role = "done @ Note l ty msg # todo"
  have "Note l ty msg \<in> set ?role" by simp
  then obtain l' msg' 
    where "listOrd ?role (Recv l' msg') (Note l ty msg)"
    and "MVar n \<in> FV msg'"
    using FV by(fast dest!: this_thread.Note_FV)
  thus ?thesis using this_thread.distinct
    by(auto dest: in_set_listOrd1 in_set_listOrd2)
qed


subsubsection{* The Effect of a Step on the Intruder Knowledge *}


context reachable_state
begin

lemma SendD: 
  "(i, Send lbl pt) \<in> steps t \<Longrightarrow> 
   (\<exists> m. Some m = inst s i pt \<and> m \<in> knows t)"
proof(induct rule: reachable_induct)
qed auto

end


subsection{* Almost Distinct Traces *}

fun distinct' :: "explicit_trace \<Rightarrow> bool"
where
  "distinct' [] = True"
| "distinct' (Learns M # t) =
     ((\<forall> m \<in> M. m \<notin> knows t) \<and> distinct' t)"
| "distinct' (Step estep # t) =
     ((estep \<notin> steps t) \<and> distinct' t)"
| "distinct' (LKReveal a # t) =
     (((Lit (EAgent a)) \<notin> lkreveals t) \<and> distinct' t)"


lemma distinct'_append [simp]:
  "distinct' (t@t') = 
   (distinct' t \<and> distinct' t' \<and> 
    (knows t \<inter> knows t' = {}) \<and> (steps t \<inter> steps t' = {}) \<and>
      (lkreveals t \<inter> lkreveals t') = {})"
proof (induct t rule: distinct'.induct)
qed (auto intro!: knowsI)

lemma distinct'_singleton [iff]: "distinct' [x]"
by (cases x) auto

lemma (in reachable_state) distinct'_trace [iff]:
  "distinct' t"
proof(induct arbitrary: i "done" todo skipped rule: reachable_induct)
  case (recv t r s i "done" l msg todo skipped)
  then interpret this_thread: 
    reachable_thread P t r s i "done" "Recv l msg # todo" skipped
    by unfold_locales auto
  show ?case using  `distinct' t` this_thread.distinct
    by(fastsimp dest: this_thread.in_steps_in_done)
next
  case (send t r s i "done" l msg todo skipped m)
  then interpret this_thread: 
    reachable_thread P t r s i "done" "Send l msg # todo" skipped
    by unfold_locales auto
  show ?case using `distinct' t` and this_thread.distinct
    by(fastsimp dest: this_thread.in_steps_in_done)
next
  case (compr t r s i "done" l ty msg todo skipped m)
  then interpret this_thread: 
     reachable_thread P t r s i "done" "Note l ty msg # todo" skipped
     by unfold_locales auto
  show ?case using `distinct' t` and this_thread.distinct
     by(fastsimp dest: this_thread.in_steps_in_done)
next
  case (skip t r s i "done" l ty msg todo skipped)
  then interpret this_thread: 
     reachable_thread P t r s i "done" "Note l ty msg # todo" skipped
     by unfold_locales auto
  show ?case using `distinct' t` and this_thread.distinct
    by(auto)
qed auto


subsection{* Happens-Before Order *}

datatype event = St "tid \<times> rolestep" | Ln execmsg | LKR execmsg

fun predOrd :: "explicit_trace \<Rightarrow> event \<Rightarrow> event \<Rightarrow> bool"
where
  "predOrd []             x y = False"
| "predOrd (Learns M # xs) x y =
     ((x \<in> Ln ` M \<and> (y \<in> Ln ` knows xs \<or> y \<in> St ` steps xs \<or> y \<in> LKR ` lkreveals xs)) \<or>
      predOrd xs x y)"
| "predOrd (Step estep # xs) x y =
     ((x = St estep \<and> (y \<in> Ln ` knows xs \<or> y \<in> St ` steps xs \<or> y \<in> LKR ` lkreveals xs)) \<or>
      predOrd xs x y)"
| "predOrd (LKReveal a # xs) x y = 
     ((x = LKR (Lit (EAgent a)) \<and> (y \<in> Ln ` knows xs \<or> y \<in> St ` steps xs \<or> y \<in> LKR ` lkreveals xs)) \<or>
      predOrd xs x y)"

definition predEqOrd :: "explicit_trace \<Rightarrow> event \<Rightarrow> event \<Rightarrow> bool"
where "predEqOrd t x y = ((x = y) \<or> predOrd t x y)"


lemma predOrd_singleton [simp]: "\<not> predOrd [a] x y"
by (cases a) auto

lemma in_knows_predOrd1: "predOrd t (Ln x) y \<Longrightarrow> x \<in> knows t"
proof (induct t)
  case (Cons e t) thus ?case by (cases e) auto
qed auto

lemma in_knows_predOrd2: "predOrd t x (Ln y) \<Longrightarrow> y \<in> knows t"
proof (induct t)
  case (Cons e t) thus ?case by (cases e) auto
qed auto

lemma in_steps_predOrd1: "predOrd t (St x) y \<Longrightarrow> x \<in> steps t"
proof (induct t)
  case (Cons e t) thus ?case by (cases e) auto
qed auto

lemma in_steps_predOrd2: "predOrd t x (St y) \<Longrightarrow> y \<in> steps t"
proof (induct t)
  case (Cons e t) thus ?case by (cases e) auto
qed auto

lemma in_lkreveals_predOrd1: "predOrd t (LKR x) y \<Longrightarrow> x \<in> lkreveals t"
proof (induct t)
  case (Cons e t) thus ?case by (cases e) auto
qed auto

lemma in_lkreveals_predOrd2: "predOrd t x (LKR y) \<Longrightarrow> y \<in> lkreveals t"
proof (induct t)
  case (Cons e t) thus ?case by (cases e) auto
qed auto

lemma in_reveals_predOrd1:
  assumes facts: "predOrd t (St (i, st)) e"
                 "noteStep st"
  shows "RCompr (noteType st) i \<in> reveals t"
using facts
by(force dest: noteStepD intro: RCompr_steps_conv[THEN iffD2] in_steps_predOrd1)

lemma in_reveals_predOrd2:
  assumes facts: "predOrd t e (St (i, st))"
                 "noteStep st"
  shows "RCompr (noteType st) i \<in> reveals t"
using facts
by(force dest: noteStepD intro: RCompr_steps_conv[THEN iffD2] in_steps_predOrd2)

lemma note_in_reveals_predOrd1:
  assumes facts: "predOrd t (St (i, Note l ty pt)) e"
  shows "RCompr ty i \<in> reveals t"
using facts
by(force dest: noteStepD intro: RCompr_steps_conv[THEN iffD2] in_steps_predOrd1)

lemma note_in_reveals_predOrd2:
  assumes facts: "predOrd t e (St (i, Note l ty pt))"
  shows "RCompr ty i \<in> reveals t"
using facts
by(force dest: noteStepD intro: RCompr_steps_conv[THEN iffD2] in_steps_predOrd2)

lemma lkr_in_reveals_predOrd1:
  "predOrd t (LKR a) e \<Longrightarrow> RLKR a \<in> reveals t"
by(force intro: RLKR_lkreveals_conv[THEN iffD2] in_lkreveals_predOrd1)

lemma lkr_in_reveals_predOrd2:
  "predOrd t e (LKR a) \<Longrightarrow> RLKR a \<in> reveals t"
by(force intro: RLKR_lkreveals_conv[THEN iffD2] in_lkreveals_predOrd2)


lemmas event_predOrdI = 
  in_knows_predOrd1 in_knows_predOrd2 
  in_steps_predOrd1 in_steps_predOrd2

lemmas compr_predOrdI =
  lkr_in_reveals_predOrd1 lkr_in_reveals_predOrd2 
  note_in_reveals_predOrd1 note_in_reveals_predOrd2

lemma event_predOrdE:
  "\<lbrakk>predOrd t (Ln x) (Ln y);    \<lbrakk> x \<in> knows t; y \<in> knows t         \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>predOrd t (Ln x) (St b);    \<lbrakk> x \<in> knows t; b \<in> steps t         \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>predOrd t (St a) (Ln y);    \<lbrakk> a \<in> steps t; y \<in> knows t         \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>predOrd t (St a) (St b);    \<lbrakk> a \<in> steps t; b \<in> steps t         \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>predOrd t (LKR c) (Ln y);   \<lbrakk> RLKR c \<in> reveals t; y \<in> knows t     \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>predOrd t (LKR c) (St b);   \<lbrakk> RLKR c \<in> reveals t; b \<in> steps t     \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>predOrd t (St a) (LKR d);   \<lbrakk> a \<in> steps t; RLKR d \<in> reveals t     \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>predOrd t (Ln x) (LKR d);   \<lbrakk> x \<in> knows t; RLKR d \<in> reveals t     \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  "\<lbrakk>predOrd t (LKR c) (LKR d);  \<lbrakk> RLKR c \<in> reveals t; RLKR d \<in> reveals t \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by(fastsimp intro: event_predOrdI compr_predOrdI)+


lemma predOrd_LKR_agent1:
  "predOrd t (LKR a) b \<Longrightarrow>  \<exists> c. a = (Lit (EAgent c))"
by(auto dest!: lkreveals_agent  RLKR_lkreveals_conv[THEN iffD1] dest: compr_predOrdI )

lemma predOrd_LKR_agent2:
  "predOrd t b (LKR a) \<Longrightarrow> \<exists> c. a = (Lit (EAgent c))"
by(auto dest!: lkreveals_agent  RLKR_lkreveals_conv[THEN iffD1] dest: compr_predOrdI )

lemma in_set_predOrd1: 
  "predOrd t x y \<Longrightarrow> x \<in> Ln ` knows t \<or> x \<in> St ` steps t \<or> x \<in> LKR ` lkreveals t"
by (induct t x y rule: predOrd.induct) auto

lemma in_set_predOrd2: 
  "predOrd t x y \<Longrightarrow> y \<in> Ln ` knows t \<or> y \<in> St ` steps t \<or> y \<in> LKR ` lkreveals t"
by (induct t x y rule: predOrd.induct) auto

lemma listOrd_imp_predOrd:
  "listOrd t (Step e) (Step e') \<Longrightarrow> predOrd t (St e) (St e')"
by (induct t rule: steps.induct) (auto dest!: stepsI)

lemma predOrd_append [simp]:
  "predOrd (xs@ys) x y = 
   (predOrd xs x y \<or> predOrd ys x y \<or>
   ((x \<in> Ln ` knows xs \<or> x \<in> St ` steps xs \<or> x \<in> LKR ` lkreveals xs) \<and> 
    (y \<in> Ln ` knows ys \<or> y \<in> St ` steps ys \<or> y \<in> LKR ` lkreveals ys)))"
  apply(induct xs x y rule: predOrd.induct)
  apply(simp_all)
  apply(blast+)
  done

lemma predOrd_distinct'_irr [simp]: 
  "distinct' t \<Longrightarrow> \<not>predOrd t x x"
  apply(induct t, auto)
  apply(case_tac x, auto)
  apply(case_tac a, auto)
  apply(case_tac a, auto)
  apply(case_tac a, auto)
  done

lemma predOrd_distinct'_trans: 
  "\<lbrakk> predOrd t x y; predOrd t y z; distinct' t \<rbrakk> 
   \<Longrightarrow> predOrd t x z"
  apply(induct t x y rule: predOrd.induct)
  apply(auto dest: in_set_predOrd1 in_set_predOrd2)
  done

lemma predOrd_distinct'_asymD: 
  "\<lbrakk> predOrd t x y; distinct' t \<rbrakk> \<Longrightarrow> \<not> predOrd t y x"
  apply(induct t x y rule: predOrd.induct)
  apply(auto dest: in_set_predOrd1 in_set_predOrd2)
  done


sublocale reachable_state \<subseteq> beforeOrd: order "predEqOrd t" "predOrd t"
  apply(unfold_locales)
  apply(auto simp: predEqOrd_def
          dest: predOrd_distinct'_asymD 
         intro: predOrd_distinct'_trans)
  done

abbreviation (in reachable_state)
  "pred'"   (infixl "\<prec>" 50) where "pred' \<equiv> predOrd t"

abbreviation (in reachable_state) 
  "predEq'" (infixl "\<preceq>" 50) where "predEq' \<equiv>  predEqOrd t"

lemma predOrd_conv:
  "predOrd xs x y = 
  (\<exists> ys zs. xs = ys @ zs \<and> 
            (x \<in> Ln ` knows ys \<or> x \<in> St ` steps ys \<or> x \<in> LKR ` lkreveals ys) \<and>
            (y \<in> Ln ` knows zs \<or> y \<in> St ` steps zs \<or> y \<in> LKR ` lkreveals zs))"
  (is "?pred xs = (\<exists> ys zs. ?decomp xs ys zs)")
proof -
  { assume "?pred xs"
    hence "\<exists> ys zs. ?decomp xs ys zs"
    proof (induct xs)
      case Nil thus ?case by simp
    next
      case (Cons e xs) thus ?case
      proof(cases e)
	case (Step st) thus ?thesis
	proof(cases "x = St st")
	  case True hence "?decomp (e#xs) [e] xs" 
	    using Step Cons by auto
	  thus ?thesis by blast
	next
	  case False
	  hence "predOrd xs x y"
	    using Step Cons by auto
	  then obtain ys zs where "?decomp xs ys zs"
	    using Cons by blast
	  hence "?decomp (e#xs) (e#ys) zs"
	    using Step Cons by auto
	  thus ?thesis by blast
	qed
      next
	case (Learns M) thus ?thesis
	proof(cases "\<exists> m \<in> M. x = Ln m")
	  case True 
	  then obtain m where "m \<in> M" and "x = Ln m"
	    by auto
	  hence "?decomp (e#xs) [e] xs" 
	    using Learns Cons by auto
	  thus ?thesis by blast
	next
	  case False
	  hence "predOrd xs x y"
	    using Learns Cons by auto
	  then obtain ys zs where "?decomp xs ys zs"
	    using Cons by blast
	  hence "?decomp (e#xs) (e#ys) zs"
	    using Learns Cons by auto
	  thus ?thesis by blast
	qed
      next
        case (LKReveal a) thus ?thesis
        proof(cases "x = LKR (Lit (EAgent a))")
          case True hence "?decomp (e#xs) [e] xs"
            using LKReveal Cons by auto
          thus ?thesis by blast
        next
          case False hence "predOrd xs x y"
            using LKReveal Cons by auto
          then obtain ys zs where "?decomp xs ys zs"
             using Cons by blast
          hence "?decomp (e#xs) (e#ys) zs"
             using LKReveal Cons by auto
          thus ?thesis by blast
        qed
      qed
    qed
  }
  moreover
  { assume "\<exists> ys zs. ?decomp xs ys zs"
    hence "?pred xs"
    proof (induct xs)
      case Nil thus ?case by simp
    next
      case (Cons e xs)
      then obtain ys zs where decomp1: "?decomp (e#xs) ys zs"
	by blast
      hence "ys = [] \<and> e # xs = zs \<or> (\<exists>ys'. e # ys' = ys \<and> xs = ys' @ zs)"
	(is "?nil \<or> ?non_nil")
	by (simp add: Cons_eq_append_conv)
      moreover
      { assume ?nil hence ?case using decomp1 by auto }
      moreover
      { assume ?non_nil
	then obtain ys' where decomp2: "ys = e # ys'" and "xs = ys' @ zs"
	  by auto
	hence ?case
	proof(cases e)
	  case (Step st) thus ?thesis
	  proof(cases "x = St st")
	    case True thus ?thesis
	      using Step decomp1 decomp2 by auto
	  next
	    case False
	    hence "?decomp xs ys' zs"
	      using Step decomp1 decomp2 by auto
	    hence "predOrd xs x y"
	      using Cons by auto
	    thus ?thesis
	      using Step by auto
	  qed
	next
	  case (Learns M) thus ?thesis
	  proof(cases "\<exists> m \<in> M. x = Ln m")
	    case True thus ?thesis
	      using Learns decomp1 decomp2 by auto
	  next
	    case False
	    hence "?decomp xs ys' zs"
	      using Learns decomp1 decomp2 by auto
	    hence "predOrd xs x y"
	      using Cons by auto
	    thus ?thesis
	      using Learns by auto
	  qed
        next
          case (LKReveal a) thus ?thesis
          proof(cases "x = LKR (Lit (EAgent a))")
            case True thus ?thesis
              using LKReveal decomp1 decomp2 by auto
          next
            case False
            hence "?decomp xs ys' zs"
              using LKReveal decomp1 decomp2 by auto
            hence "predOrd xs x y"
              using Cons by auto
            thus ?thesis 
              using LKReveal by auto
          qed
	qed
      }
      ultimately show ?case by fast
    qed
  }
  ultimately show ?thesis by fast
qed


subsection{* Input Terms *}


context reachable_state
begin

lemma knows_pairParts_closed:
  "m \<in> knows t \<Longrightarrow> pairParts m \<subseteq> knows t"
proof(induct arbitrary: m rule: reachable_induct)
  case init thus ?case by(auto simp: IK0_def) 
next
  case send thus ?case by(auto dest: pairParts_idemD)
next
  case decr thus ?case by(auto dest: pairParts_idemD)
next
  case tuple thus ?case by fastsimp
next
  case lkr thus ?case by(auto simp: longTermKeys_def)
next
  case compr thus ?case by(auto dest: pairParts_idemD)
qed auto


lemmas knows_pairParts_closedD =
  subsetD[OF knows_pairParts_closed, rule_format]

lemmas rev_knows_pairParts_closedD =
  rev_subsetD[OF _ knows_pairParts_closed, rule_format]


lemma pairParts_before:
  "\<lbrakk> predOrd t (Ln m) y; m' \<in> pairParts m \<rbrakk> \<Longrightarrow>
   predOrd t (Ln m') y"
proof(induct rule: reachable_induct)
  case (hash t r s msg)
  then interpret s1: reachable_state P t r s
    by unfold_locales
  from hash show ?case
    by (fastsimp dest: s1.rev_knows_pairParts_closedD)
next
  case (encr t r s msg key)
  then interpret s1: reachable_state P t r s
    by unfold_locales
  from encr show ?case
    by (fastsimp dest: s1.rev_knows_pairParts_closedD)
next
  case (tuple t r s msg1 msg2)
  then interpret s1: reachable_state P t r s
    by unfold_locales
  from tuple show ?case
    by (fastsimp dest: s1.rev_knows_pairParts_closedD)
next
  case (decr t r s msg key)
  then interpret s1: reachable_state P t r s
    by unfold_locales
  from decr show ?case
    by (fastsimp dest: s1.rev_knows_pairParts_closedD)
next
  case (send t r s i "done" l msg todo msg)
  then interpret s1: reachable_state P t r s
    by unfold_locales
  from send show ?case
    by (fastsimp dest: s1.rev_knows_pairParts_closedD)
next
  case (recv t r s i "done" l msg todo)
  then interpret s1: reachable_state P t r s
    by unfold_locales
  from recv show ?case
    by (fastsimp dest: s1.rev_knows_pairParts_closedD)
next
  case (init r s) thus ?case by simp
next
  case (lkr t r s a)
  then interpret s1: reachable_state P t r s
    by unfold_locales
  from lkr show ?case
   by (fastsimp dest: s1.rev_knows_pairParts_closedD)
next
  case (skip t r s i "done" l ty pt todo)
  then interpret s1: reachable_state P t r s 
    by unfold_locales
  from skip show ?case
    by(fastsimp dest: s1.rev_knows_pairParts_closedD)
next
  case (compr t r s i "done" l ty pt todo skipped m)
  then interpret s1: reachable_state P t r s
    by unfold_locales
  from compr show ?case
    by(fastsimp dest: s1.rev_knows_pairParts_closedD)
qed

lemma Ln_before_inp:
  "(i, Recv l pt) \<in> steps t \<Longrightarrow> 
   \<exists> m. Some m = inst s i pt \<and> Ln m \<prec> St (i, Recv l pt)"
  by (induct arbitrary: i l pt rule: reachable_induct) fastsimp+

lemma Ln_before_inpE:
  "\<lbrakk> (i, Recv l pt) \<in> steps t;
     \<And> m. \<lbrakk> Some m = inst s i pt; Ln m \<prec> St (i, Recv l pt) \<rbrakk>
           \<Longrightarrow> Q
   \<rbrakk> \<Longrightarrow> Q"
  by (auto dest!: Ln_before_inp)

(*
lemmas knows_inp = in_knows_predOrd1[OF Ln_before_inp, rule_format]
*)

text{* Three of the lemmas for the reasoning technique. *}
lemmas Input = Ln_before_inp

lemma split_before:
  "Ln (Tup m m') \<prec> y \<Longrightarrow> Ln m \<prec> y \<and> Ln m' \<prec> y"
  by (fastsimp intro: pairParts_before)

lemma split_knows:
  "Tup m m' \<in> knows t \<Longrightarrow> m \<in> knows t \<and> m' \<in> knows t"
  by (fastsimp intro: knows_pairParts_closedD)
end

subsection{* Case Distinction on Learning Messages *}

text{* Note that the hints are logically equal to true. Thus they have no logical
  content. However they are placed here to track the individual cases when 
  computing the decryption chains for a concrete message and protocol.
*}

fun decrChain :: "string \<Rightarrow> explicit_trace \<Rightarrow> event set \<Rightarrow> execmsg \<Rightarrow> execmsg \<Rightarrow> bool"
where
  "decrChain path t from (Enc msg key) m = 
   ( ( m = Enc msg key \<and> (\<forall> f \<in> from. predOrd t f (Ln m)) \<and> 
       hint ''decrChainPath'' path
     ) \<or>
     ( (\<forall> f \<in> from. predOrd t f (Ln (Enc msg key))) \<and> 
       decrChain (path@''E'') t {Ln (Enc msg key), Ln (inv key)} msg m  )
   )"
| "decrChain path t from (Tup x y) m = 
   ( ( m = Tup x y \<and> (\<forall> f \<in> from. predOrd t f (Ln m)) \<and>
       hint ''decrChainPath'' path
     ) \<or>
     decrChain (path@''L'') t from x m \<or>
     decrChain (path@''R'') t from y m
   )"
| "decrChain path t from msg m =
   ( m = msg \<and> (\<forall> f \<in> from. predOrd t f (Ln m)) \<and>
     hint ''decrChainPath'' path
   )"

lemma decrChain_append:
  "decrChain path t from msg m \<Longrightarrow> decrChain path (t@t') from msg m"
  by (induct path t "from" msg m rule: decrChain.induct) auto

lemma decrChain_unpair:
  "\<lbrakk> m' \<in> pairParts m; m' \<in> M;
     \<forall> f \<in> from. f \<in> Ln ` knows t \<or> f \<in> St ` steps t
   \<rbrakk> \<Longrightarrow> decrChain path (t@[Learns M]) from m m'"
by (induct m arbitrary: path M) (auto simp: remove_hints)

lemma decrChain_decrypt:
  "\<lbrakk> decrChain path t from msg (Enc m k);
     Enc m k \<in> knows t; inv k \<in> knows t;
     m' \<in> pairParts m; m' \<notin> knows t \<rbrakk> \<Longrightarrow>
   decrChain path' (t @ [Learns (pairParts m - knows t)]) from msg m'"
proof(induct msg arbitrary: path path' "from")
  case (Enc msg key)
  hence from_before [simp]: 
    "\<forall>f\<in>from. predOrd t f (Ln (Enc msg key))" by auto
  have "m = msg \<and> k = key \<or> 
    decrChain (path@''E'') t {Ln (Enc msg key), Ln (inv key)} msg (Enc m k)"
    (is "?here \<or> ?nested")
    using Enc by auto
  moreover
  { assume "?here"
    hence "?case"
    proof(cases "m' = Enc m k")
      case True thus ?thesis
	using `?here` Enc by fastsimp
    next
      case False thus ?thesis
	using `?here` Enc
	by(auto intro!: decrChain_unpair)
    qed
  }
  moreover
  { assume "?nested"
    hence "?case" using Enc
      by (fastsimp dest!: Enc(2))
  }
  ultimately show ?case by fast
qed auto


lemma (in reachable_state) knows_cases_raw:
  assumes knows: "m' \<in> knows t"
  shows 
   "(m' \<in> IK0) \<or>
    (\<exists> m.   m' = Hash m   \<and> Ln m \<prec> Ln (Hash m)) \<or>
    (\<exists> m k. m' = Enc  m k \<and> Ln m \<prec> Ln (Enc m k) \<and> Ln k \<prec> Ln (Enc m k)) \<or>
    (\<exists> x y. m' = Tup  x y \<and> Ln x \<prec> Ln (Tup x y) \<and> Ln y \<prec> Ln (Tup x y)) \<or>
    (\<exists> i done todo skipped. r i = Some (done, todo, skipped) \<and> 
       (\<exists> l pt m. 
          Send l pt \<in> set done \<and> Some m = inst s i pt \<and> 
          decrChain [] t {St (i, Send l pt)} m m'
       )
    ) \<or>
    (\<exists> i done todo skipped. r i = Some (done, todo, skipped) \<and> 
       (\<exists> l ty pt m. 
          Note l ty pt \<in> set done \<and> Note l ty pt \<notin> skipped \<and> 
          Some m = inst s i pt \<and> 
          decrChain [] t {St (i, Note l ty pt)} m m'
       )
    ) \<or>
   (\<exists> a. m' = SK a \<and> LKR a \<prec> Ln m') \<or>
   (\<exists> a b. m' = K a b \<and> LKR a \<prec> Ln m') \<or>
   (\<exists> a b. m' = K a b \<and> LKR b \<prec> Ln m') \<or> 
   (\<exists> A. \<exists> a \<in> A. m' = KShr A \<and> LKR (Lit (EAgent a)) \<prec> Ln m')
   "
  (is "?cases m' t r s")
proof -
  --{* Prove cases transfer lemma for trace extension *}
  { fix m' t t' r s
    let ?thesis = "?cases m' (t@t') r s"
    assume "?cases m' t r s" 
    (is "?ik0 \<or> ?hash \<or> ?enc \<or> ?tup \<or> ?chain t r s \<or> ?note t r s \<or> ?keys")
    moreover
    { assume "?ik0"  hence "?thesis" by blast }    moreover
    { assume "?hash" hence "?thesis" by fastsimp } moreover
    { assume "?enc"  hence "?thesis" by fastsimp } moreover
    { assume "?tup"  hence "?thesis" by fastsimp } moreover
    { assume "?chain t r s"
      hence "?chain (t@t') r s" 
	by (fastsimp intro!: decrChain_append)
      hence "?thesis" by blast
    } moreover
    { assume "?note t r s"
      hence "?note (t@t') r s" 
	by (fastsimp intro!: decrChain_append)
      hence "?thesis" by blast
    } moreover
    { assume "?keys" hence "?thesis" by auto }
    ultimately have ?thesis by fast
  }
  note cases_appendI_trace = this

  --{* Prove actual thesis *}
  from knows show ?thesis
  proof (induct arbitrary: m' rule: reachable_induct)
    case init thus ?case by simp
  next
    case (hash t r s m)
    let ?t' = "t @ [Learns {Hash m}]"
    note IH = hash(2)
    have "m' \<in> knows t \<or> m' = Hash m" (is "?old \<or> ?new")
      using hash by fastsimp
    moreover
    { assume "?new" hence ?case 
	using `m \<in> knows t` by fastsimp 
    }
    moreover
    { assume "?old" 
      hence ?case by (fastsimp intro!: IH cases_appendI_trace)
    }
    ultimately show ?case by fast
  next
    case (encr t r s m k)
    let ?t' = "t @ [Learns {Enc m k}]"
    note IH = encr(2)
    have "m' \<in> knows t \<or> m' = Enc m k" (is "?old \<or> ?new")
      using encr by fastsimp
    moreover
    { assume "?new" hence ?case 
	using `m \<in> knows t` and `k \<in> knows t` by fastsimp 
    }
    moreover
    { assume "?old" 
      hence ?case by (fast intro!: IH cases_appendI_trace)
    }
    ultimately show ?case by fast
  next
    case (tuple t r s x y)
    let ?t' = "t @ [Learns {Tup x y}]"
    note IH = tuple(2)
    have "m' \<in> knows t \<or> m' = Tup x y" (is "?old \<or> ?new")
      using tuple by fastsimp
    moreover
    { assume "?new" hence ?case 
	using `x \<in> knows t` and `y \<in> knows t` by fastsimp 
    }
    moreover
    { assume "?old" 
      hence ?case by (fast intro!: IH cases_appendI_trace)
    }
    ultimately show ?case by fast
  next
    case (recv t r s i "done" l pt todo skipped)
    hence "?cases m' t r s" 
      (is "?ik0 \<or> ?hash \<or> ?enc \<or> ?tup \<or> ?chain t r s \<or> ?note t r s \<or> ?keys")
      by clarsimp
    moreover
    { assume "?ik0"   hence "?case" by blast    } moreover
    { assume "?hash"  hence "?case" by fastsimp } moreover
    { assume "?enc"   hence "?case" by fastsimp } moreover
    { assume "?keys"  hence "?case" by fastsimp } moreover
    { assume "?tup"   hence "?case" by fastsimp } moreover
    { let ?t' = "t@[Step (i, Recv l pt)]"
      and ?r' = "r(i \<mapsto> (done @ [Recv l pt], todo, skipped))"
      assume "?chain t r s" then
      obtain i' done' todo' l' pt' skipped' m
	where thread': "r i' = Some (done', todo', skipped')"
	and send: "Send l' pt' \<in> set done'"
        and msg:  "Some m = inst s i' pt'"
	and chain:"decrChain [] t {St (i', Send l' pt')} m m'"
	by auto
      then interpret th1: reachable_thread P t r s i' done' todo' skipped'
	using recv by unfold_locales auto
      moreover
      obtain done'' todo'' skipped''
	where "Send l' pt' \<in> set done''"
	and "?r' i' = Some (done'', todo'', skipped'')"
	using `r i = Some (done, Recv l pt # todo, skipped)` thread' send
	by (cases "i = i'") (fastsimp+)
      ultimately
      have "?chain ?t' ?r' s"
	using chain msg
        by (fast intro!: decrChain_append)
      hence "?case" by auto
    } moreover
    { let ?t' = "t@[Step (i, Recv l pt)]"
      and ?r' = "r(i \<mapsto> (done @ [Recv l pt], todo, skipped))"
      assume "?note t r s" then
      obtain i' done' todo' skipped' l' ty' pt' m
	where thread': "r i' = Some (done', todo', skipped')"
	and inDone: "Note l' ty' pt' \<in> set done'"
        and notSkipped: "Note l' ty' pt' \<notin> skipped'"
        and msg: "Some m = inst s i' pt'"
	and chain: "decrChain [] t {St (i', Note l' ty' pt')} m m'"
        by auto
      then interpret th1: reachable_thread P t r s i' done' todo' skipped'
	using recv by unfold_locales auto
      moreover
      obtain done'' todo'' skipped''
	where "Note l' ty' pt' \<in> set done''"
        and "Note l' ty' pt' \<notin> skipped'' "
	and "?r' i' = Some (done'', todo'', skipped'')"
	using `r i = Some (done, Recv l pt # todo, skipped)` thread' inDone notSkipped
	by (cases "i = i'") (fastsimp+)
      ultimately
      have "?note ?t' ?r' s" using msg chain notSkipped inDone
        by (fast intro!: decrChain_append)
      hence "?case" by auto
    }
    ultimately show ?case by fastsimp
  next
    case (send t r s i "done" l pt todo skipped m)
    then interpret th1: 
      reachable_thread P t r s i "done" "Send l pt # todo" skipped
      by unfold_locales
    let ?r' = "r(i \<mapsto> (done @ [Send l pt], todo, skipped))"
    let ?t' = "(t @ [Step (i, Send l pt)]) @ [Learns (pairParts m - knows t)]"
    have "m' \<in> knows t \<or> m' \<in> pairParts m \<and> m' \<notin> knows t \<and> Some m = inst s i pt" 
      (is "?old \<or> ?new")
      using send by fastsimp
    moreover
    { assume "?new"
      hence "decrChain [] ?t' {St (i, Send l pt)} m m'"
	by (fastsimp intro!: decrChain_unpair)
      moreover
      have "?r' i = Some (done @ [Send l pt], todo, skipped)"
	using th1.thread_exists by auto
      ultimately
      have ?case using `Some m = inst s i pt`
	apply-
        apply(rule disjI2)
        apply(rule disjI2)
        apply(rule disjI2)
        apply(rule disjI2)
        apply(rule disjI1)
        apply(fastsimp)
	done
    }
    moreover
    { assume "?old" 
      hence "?cases m' t r s" 
        (is "?ik0 \<or> ?hash \<or> ?enc \<or> ?tup \<or> ?chain t r s \<or> ?note t r s \<or> ?keys")
	using send by clarsimp
      moreover
      { assume "?ik0"   hence "?case" by blast    } moreover
      { assume "?hash"  hence "?case" by fastsimp } moreover
      { assume "?enc"   hence "?case" by fastsimp } moreover
      { assume "?keys"  hence "?case" by fastsimp } moreover
      { assume "?tup"   hence "?case" by fastsimp } moreover
      { assume "?chain t r s" then
	obtain i' done' todo' l' pt' skipped' m
	  where thread': "r i' = Some (done', todo',skipped')"
	  and send: "Send l' pt' \<in> set done'"
          and msg:  "Some m = inst s i' pt'"
	  and chain: "decrChain [] t {St (i', Send l' pt')} m m'"
	  by auto
	obtain done'' todo'' skipped''
	  where "Send l' pt' \<in> set done''"
	  and "(r(i \<mapsto> (done @ [Send l pt], todo, skipped))) i' = Some (done'', todo'',skipped'')"
	  using `r i = Some (done, Send l pt # todo, skipped)` thread' send
	  by (cases "i = i'") (fastsimp+)
	hence "?chain ?t' ?r' s"
	  using chain msg
          by (fast intro!: decrChain_append)
	hence "?case" by auto
      } moreover
      { assume "?note t r s" then
        obtain i' done' todo' skipped' l' ty' pt' m
	  where thread': "r i' = Some (done', todo', skipped')"
	  and inDone: "Note l' ty' pt' \<in> set done'"
          and notSkipped: "Note l' ty' pt' \<notin> skipped'"
          and msg: "Some m = inst s i' pt'"
	  and chain: "decrChain [] t {St (i', Note l' ty' pt')} m m'"
          by auto
        obtain done'' todo'' skipped''
	  where "Note l' ty' pt' \<in> set done''"
          and "Note l' ty' pt' \<notin> skipped'' "
	  and "?r' i' = Some (done'', todo'', skipped'')"
	  using `r i = Some (done, Send l pt # todo, skipped)` thread' inDone notSkipped
	  by (cases "i = i'") (fastsimp+)
        hence "?note ?t' ?r' s" using chain notSkipped inDone msg
 	  by(fast intro!: decrChain_append)
        hence "?case" by auto
       }
      ultimately have ?case by fast
    }
    ultimately show ?case by fast
  next
    case (decr t r s m k)
    then interpret s1: reachable_state P t r s
      by unfold_locales
    let ?t' = "t @ [Learns (pairParts m - knows t)]"
    note IH = decr(2)
    have "m' \<in> knows t \<or> m' \<in> pairParts m \<and> m' \<notin> knows t" 
      (is "?old \<or> ?new")
      using decr by fastsimp
    moreover
    { assume "?new"
      hence "m' \<in> pairParts m" and "m' \<notin> knows t" by auto
      hence 
	"(predOrd t (Ln m) (Ln (Enc m k)) \<and> predOrd t (Ln k) (Ln (Enc m k))) \<or>
         ((\<exists>i done todo skipped. r i = Some (done, todo,skipped) \<and>
          (\<exists>l pt ms. Send l pt \<in> set done \<and> Some ms = inst s i pt \<and> 
                    decrChain [] t {St (i, Send l pt)} ms (Enc m k)))) \<or>
         ((\<exists>i done todo skipped. r i = Some (done, todo,skipped) \<and>
          (\<exists>l ty pt ms. Note l ty pt \<in> set done \<and> Note l ty pt \<notin> skipped \<and>
                       Some ms = inst s i pt \<and> 
                  decrChain [] t {St (i, Note l ty pt)} ms (Enc m k))))"
	(is "?fake_enc \<or> ?decchain t (Enc m k) \<or> ?notechain t (Enc m k)")
	using IH[OF `Enc m k \<in> knows t`] by auto
      moreover
      { assume "?fake_enc"
	hence "?case" using `?new`
	  by (auto dest!: in_knows_predOrd1 s1.rev_knows_pairParts_closedD)
      }
      moreover
      { assume "?decchain t (Enc m k)" then
	obtain i' done' todo' l' pt' skipped' ms
	  where thread': "r i' = Some (done', todo',skipped')"
	  and send: "Send l' pt' \<in> set done'"
          and msg:  "Some ms = inst s i' pt'"
	  and chain: "decrChain [] t {St (i', Send l' pt')} ms (Enc m k)"
	  by auto
	moreover
	hence "decrChain [] ?t' {St (i', Send l' pt')} ms m'"
	  using `?new` `Enc m k \<in> knows t` `inv k \<in> knows t`
	  by (fastsimp intro!: decrChain_decrypt)
	ultimately
	have "?decchain ?t' m'" by fastsimp
	hence "?case" by blast
      }
      moreover
      { assume "?notechain t (Enc m k)" then
	obtain i' done' todo' l' ty' pt' skipped' ms
	  where thread': "r i' = Some (done', todo',skipped')"
	  and inDone: "Note l' ty' pt' \<in> set done'"
          and notSkipped: "Note l' ty' pt' \<notin>  skipped'"
          and msg:   "Some ms = inst s i' pt'"
	  and chain: "decrChain [] t {St (i', Note l' ty' pt')} ms (Enc m k)"
	  by auto
	moreover
	hence "decrChain [] ?t' {St (i', Note l' ty' pt')} ms m'"
	  using `?new` `Enc m k \<in> knows t` `inv k \<in> knows t`
	  by (fastsimp intro!: decrChain_decrypt)
	ultimately
	have "?notechain ?t' m'" by fastsimp
	hence "?case" by blast
      }
      ultimately have ?case by fast
    }
    moreover
    { assume "?old" 
      hence ?case by (fast intro!: IH cases_appendI_trace)
    }
    ultimately show ?case by fast thm decr
  next
    case(lkr t r s a)
    then interpret s1: reachable_state P t r s
      by unfold_locales
    let ?t' = "t @ [ LKReveal a, Learns (longTermKeys a - knows t)]"
    note IH = lkr(2)
    have "m' \<in> knows t \<or> m' \<in> longTermKeys a \<and> m' \<notin> knows t" 
      (is "?old \<or> ?new")
    using lkr by fastsimp
    moreover 
    {
      assume "?old"
      hence "?case" by (fast intro!: IH cases_appendI_trace)
    }
    moreover
    {
      assume "?new"
      hence ?case by (auto simp: longTermKeys_def)
    }
    ultimately show "?case" by fast
  next
   case (skip t r s i "done" l ty pt todo skipped)
   then interpret this_thread:  reachable_thread P t r s i "done" "Note l ty pt # todo" skipped  by unfold_locales
   let ?r' = "r(i \<mapsto> (done @ [Note l ty pt], todo, insert (Note l ty pt) skipped))"
   have "m' \<in> knows t" using skip by fastsimp
   hence "?cases m' t r s" 
     (is "?ik0 \<or> ?hash \<or> ?enc \<or> ?tup \<or> ?chain t r s \<or> ?note t r s \<or> ?keys")
     using skip by clarsimp
   moreover
   { assume "?ik0"   hence "?case" by blast    } moreover
   { assume "?hash"  hence "?case" by fastsimp } moreover
   { assume "?enc"   hence "?case" by fastsimp } moreover
   { assume "?keys"  hence "?case" by fastsimp } moreover
   { assume "?tup"   hence "?case" by fastsimp } moreover
   { assume "?chain t r s" then
     obtain i' done' todo' l' pt' skipped' m
       where thread': "r i' = Some (done', todo',skipped')"
       and send: "Send l' pt' \<in> set done'"
       and msg: "Some m = inst s i' pt'"
       and chain: "decrChain [] t {St (i', Send l' pt')} m m'"
       by auto
     obtain done'' todo'' skipped''
       where "Send l' pt' \<in> set done''"
       and "?r' i' = Some (done'', todo'',skipped'')"
       using skip(3) thread' send
       by (cases "i = i'") (fastsimp+)
     hence "?chain t ?r'  s"
       using chain msg by fast
     hence "?case" by auto
   }
   moreover
   { assume "?note t r s" then
     obtain i' done' todo' skipped' l' ty' pt' m
       where thread': "r i' = Some (done', todo', skipped')"
       and inDone: "Note l' ty' pt' \<in> set done'"
       and notSkipped: "Note l' ty' pt' \<notin> skipped'"
       and msg:   "Some m = inst s i' pt'"
       and chain: "decrChain [] t {St (i', Note l' ty' pt')} m m'"
       by auto
      obtain done'' todo'' skipped''
       where "Note l' ty' pt' \<in> set done''"
       and "Note l' ty' pt' \<notin> skipped'' "
       and "?r' i' = Some (done'', todo'', skipped'')"
       using `r i = Some (done, Note l ty pt # todo, skipped)` thread' inDone notSkipped
       by (cases "i = i'") (force dest: this_thread.done_notin_todoD)+
     hence "?note t ?r' s" 
       using chain notSkipped inDone msg
       by fast
     hence "?case" by auto
   } moreover
   { assume "?keys" hence "?case" by fastsimp }
   ultimately  
   show  "?case" by fastsimp
  next
   case(compr t r s i "done" l ty pt todo skipped m m')
   then interpret th1: 
      reachable_thread P t r s i "done" "Note l ty pt # todo" skipped
      by unfold_locales
    let ?r' = "r(i \<mapsto> (done @ [Note l ty pt], todo, skipped))"
    let ?t' = "(t @ [Step (i, Note l ty pt)]) @ [Learns (pairParts m - knows t)]"
    have "m' \<in> knows t \<or> m' \<in> pairParts m \<and> m' \<notin> knows t \<and> Some m = inst s i pt" 
      (is "?old \<or> ?new")
      using compr by fastsimp
    moreover
    { assume "?new"
  (*
        hence "m' \<in> pairParts (inst s i pt)" and "m' \<notin> knows t" using `m = inst s i pt` 
      by auto
*)
        hence "decrChain [] ?t' {St (i, Note l ty pt)} m m'" 
          by (fastsimp intro!: decrChain_unpair)
      moreover
        have "?r' i = Some (done @ [Note l ty pt], todo, skipped)" 
          using th1.thread_exists by auto
      moreover
        have "Note l ty pt \<in> set (Note l ty pt # todo)" 
          using th1.thread_exists by auto
        hence "Note l ty pt \<notin> skipped" 
          by (fastsimp dest: th1.todo_notin_skippedD)
      ultimately
      have ?case using `Some m = inst s i pt`
	apply-
        apply(rule disjI2)
        apply(rule disjI2)
        apply(rule disjI2)
        apply(rule disjI2)
        apply(rule disjI2)
        apply(rule disjI1)
        by force
    }
    moreover
    { assume "?old" 
      hence "?cases m' t r s" 
        (is "?ik0 \<or> ?hash \<or> ?enc \<or> ?tup \<or> ?chain t r s \<or> ?note t r s \<or> ?keys")
	using compr by clarsimp
      moreover
      { assume "?ik0"   hence "?case" by blast    } moreover
      { assume "?hash"  hence "?case" by fastsimp } moreover
      { assume "?enc"   hence "?case" by fastsimp } moreover
      { assume "?keys"  hence "?case" by fastsimp } moreover
      { assume "?tup"   hence "?case" by fastsimp } moreover
      { assume "?chain t r s" then
	obtain i' done' todo' l' pt' skipped' m
	  where thread': "r i' = Some (done', todo',skipped')"
	  and send: "Send l' pt' \<in> set done'"
          and msg:  "Some m = inst s i' pt'"
	  and chain: "decrChain [] t {St (i', Send l' pt')} m m'"
	  by auto
	obtain done'' todo'' skipped''
	  where "Send l' pt' \<in> set done''"
	  and "(r(i \<mapsto> (done @ [Note l ty pt], todo, skipped))) i' = Some (done'', todo'',skipped'')"
	  using compr(3) thread' send
	  by (cases "i = i'") (fastsimp+)
	hence "?chain ?t' ?r' s" using chain msg
          by(fast intro!: decrChain_append)
	hence "?case"  by auto
      } moreover
      { assume "?note t r s" then
        obtain i' done' todo' skipped' l' ty' pt' m
	  where thread': "r i' = Some (done', todo', skipped')"
	  and inDone: "Note l' ty' pt' \<in> set done'"
          and notSkipped: "Note l' ty' pt' \<notin> skipped'"
          and msg:   "Some m = inst s i' pt'"
	  and chain: "decrChain [] t {St (i', Note l' ty' pt')} m m'"
          by auto
        obtain done'' todo'' skipped''
	  where "Note l' ty' pt' \<in> set done''"
          and "Note l' ty' pt' \<notin> skipped'' "
	  and "?r' i' = Some (done'', todo'', skipped'')"
	  using `r i = Some (done, Note l ty pt # todo, skipped)` thread' inDone notSkipped
	  by (cases "i = i'") (fastsimp+)
        hence "?note ?t' ?r' s"
          using chain notSkipped inDone msg
          by(fast intro!: decrChain_append)
        hence "?case" by auto
       }
      ultimately have ?case by fast
    }
    ultimately show ?case by fast
  qed
qed

end
