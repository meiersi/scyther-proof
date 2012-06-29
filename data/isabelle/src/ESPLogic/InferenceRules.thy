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
theory InferenceRules
imports
  HOL_ext
  Hints
  ExplicitModel
begin


section{* Inference Rules *}

subsection{* Role Order *}

definition roleMap :: "threadpool \<Rightarrow> tid \<rightharpoonup> role"
where "roleMap pool \<equiv> (\<lambda>(done,todo,skipped). Some (done @ todo)) \<circ>\<^sub>m pool"

lemma roleMap_empty [simp]: "roleMap empty = empty"
  by(simp add: roleMap_def)

lemma dom_roleMap [simp]: "dom (roleMap r) = dom r"
  by(auto simp: dom_def roleMap_def map_comp_def 
         split: option.splits)

lemma roleMap_upd [simp]:
  "roleMap (pool(i \<mapsto> (done,todo,skipped))) = 
   (roleMap pool)(i \<mapsto> (done@todo))"
  by(rule ext, simp add: roleMap_def map_comp_def)

lemma roleMap_SomeD:
  "roleMap r i = Some R \<Longrightarrow> 
  \<exists> todo done skipped. r i = Some (done, todo, skipped) \<and> R = done@todo"
  by(auto simp: roleMap_def map_comp_def split: option.splits)

lemma roleMap_SomeI:
  "\<lbrakk> r i = Some (done, todo, skipped); R = done @ todo \<rbrakk> \<Longrightarrow>
   roleMap r i = Some R"
  by(auto simp: roleMap_def map_comp_def split: option.splits)

lemma roleMap_SomeE:
  assumes role_exists: "roleMap r i = Some R"
  obtains "done" todo skipped
  where "r i = Some (done, todo, skipped)" and "R = done @ todo"
using role_exists
by (auto simp:  roleMap_def map_comp_def split: option.splits)

lemma roleMap_le_roleMapI [intro!]:
  assumes roleMap_leD: 
    "\<And> i done todo skipped. r i = Some (done, todo, skipped) \<Longrightarrow> 
     \<exists> done' todo' skipped'. r' i = Some (done', todo', skipped') \<and> done@todo = done'@todo'"
  shows "roleMap r \<subseteq>\<^sub>m roleMap r'"
by(auto simp: roleMap_def map_comp_def  split: option.splits
      intro!: map_leI dest!: roleMap_leD)

lemma (in reachable_thread) roleMap: 
  "roleMap r i = Some (done@todo)"
  by(fast intro!: thread_exists roleMap_SomeI)

subsection{* Prefix Close *}


definition prefixClose :: "store \<Rightarrow> explicit_trace \<Rightarrow> role \<Rightarrow> rolestep \<Rightarrow> tid \<Rightarrow> bool"
where
"prefixClose s t R step i = 
  (\<forall> st st'. 
      (nextRel (filter (\<lambda> x. \<not> (noteStep x)) (takeWhile (\<lambda> x. x \<noteq> step) R) @ [step]) st st') \<longrightarrow>
      ((recvStep st \<longrightarrow> (\<exists> m. Some m = inst s i (stepPat st) \<and> predOrd t (Ln m) (St (i, st)))) \<and>
       predOrd t (St (i, st)) (St (i, st')))
   )"

context reachable_state begin

lemma note_filtered_done[iff]:
   "Note l ty pt \<notin> set (filter (\<lambda> x. \<not> (noteStep x)) done)"
by auto

lemma take_while_is_done:
  assumes facts:
    "r i = Some(done, step # todo, skipped)"
    "roleMap r i = Some R"
  shows isDone:
    "(takeWhile (\<lambda> x. x \<noteq> step) R) = done"
using facts
proof -
  interpret reachable_thread P t r s i "done" "step#todo" skipped
    using facts by unfold_locales auto
  hence "step \<in> set (step # todo)" by auto
  hence "step \<notin> set done" using facts by (fastsimp dest!: todo_notin_doneD)
  hence "(takeWhile (\<lambda> x. x \<noteq> step) done) = done" by auto
  hence "(takeWhile (\<lambda> x. x \<noteq> step) (done @ (step # todo))) = done" by auto
  moreover
  have "R = (done @ (step # todo))" using facts by (fastsimp dest: roleMap_SomeD)
  ultimately show ?thesis by auto
qed

lemma note_filtered_role:
    "Note l ty pt \<in> set (filter (\<lambda> x. \<not> (noteStep x)) (takeWhile (\<lambda> x. x \<noteq> step) R) @ [step]) \<Longrightarrow> step = (Note l ty pt)"
by auto

lemma note_filtered_revRole:
"Note l ty pt \<in> set (step# rev (filter (\<lambda> x. \<not> (noteStep x)) (takeWhile (\<lambda> x. x \<noteq> step) R))) \<Longrightarrow> step = (Note l ty pt)"
by auto

lemma filtered_role_conv:
  assumes filtered:
  "st \<in> set (filter (\<lambda> x. \<not> (noteStep x)) (takeWhile (\<lambda> x. x \<noteq> step) R) @ [step])"
  shows "(st \<in> set R \<and> st \<noteq> (Note l ty pt)) \<or> (st = step)"
proof -
  have "st \<in> set (filter (\<lambda> x. \<not> (noteStep x)) (takeWhile (\<lambda> x. x \<noteq> step) R)) \<or> (st = step)" using filtered by auto
  moreover {
    assume inFilter: "st \<in> set (filter (\<lambda> x. \<not> (noteStep x)) (takeWhile (\<lambda> x. x \<noteq> step) R)) \<and> (st \<noteq> step)"
    hence "st \<in> set (takeWhile (\<lambda> x. x \<noteq> step) R) \<and> (st \<noteq> step)" by auto
    hence "st \<in> set R \<and> (st \<noteq> step)" by (auto dest: set_takeWhileD)
    hence "st \<in> set R" by auto
    moreover
    have "st \<noteq> (Note l ty pt)" using inFilter by (auto dest: note_filtered_role)
    ultimately have ?thesis by auto
  }
  ultimately show ?thesis by auto
qed

lemma filtered_done_conv:
  assumes isThread:
    "r i = Some(done, step # todo, skipped)"
    "roleMap r i = Some R"
  and filtered:
    "st \<in> set (filter (\<lambda> x. \<not> (noteStep x)) (takeWhile (\<lambda> x. x \<noteq> step) R) @ [step])"
  shows
    "(st \<in> set done \<and> st \<noteq> (Note l ty pt)) \<or> (st = step)"
proof -
  have "(st \<in> set R \<and> st \<noteq> (Note l ty pt)) \<or> (st = step)" using filtered by (fastsimp dest: filtered_role_conv)
  moreover
  have "(takeWhile (\<lambda> x. x \<noteq> step) R) = done" using isThread by (fastsimp dest: take_while_is_done)
  ultimately show ?thesis using isThread and filtered by fastsimp
qed

lemma filtered_in_done:
  assumes step: "(i, step) \<in> steps t"
  and role_exists: "roleMap r i = Some R \<and> r i = Some(done, todo, skipped)"
  and inFiltered: "st \<in> set (filter (\<lambda> x. \<not> (noteStep x)) (takeWhile (\<lambda> x. x \<noteq> step) R) @ [step])"
  shows "st \<in> set done"
proof -
  interpret this_thread:
    reachable_thread P t r s i "done" todo skipped
    using role_exists by unfold_locales auto
  hence "step \<in> set done"
    using step by (auto dest: this_thread.in_steps_in_done)
  moreover
  then obtain prefix suffix 
    where done_split: "done = prefix @ step # suffix \<and> step \<notin> set prefix"
    by (auto dest!: split_list_first)
  hence "takeWhile (\<lambda>x. x \<noteq> step) (prefix@step#suffix@todo) = prefix"
    by (subst takeWhile_append2) auto
  hence  "takeWhile (\<lambda>x. x \<noteq> step) R = prefix"
    using role_exists done_split by (auto elim!: roleMap_SomeE) 
  moreover {
    assume "st \<noteq> step \<and> takeWhile (\<lambda>x. x \<noteq> step) R = prefix"
    hence "st \<in> set prefix" using inFiltered 
      by auto
    hence ?thesis using done_split by fastsimp
  }
  moreover {
    assume "st = step \<and> step \<in> set done"
    hence ?thesis by auto
  }
  ultimately show ?thesis by auto
qed


lemma recv_roleOrd_imp_predOrd:
  assumes step: "(i, step) \<in> steps t"
  and role_exists: "roleMap r i = Some R"
  and role_ord: "listOrd R (Recv l pt) step"
  shows "St (i, (Recv l pt)) \<prec> St (i, step)"
proof -
  from role_exists
  obtain "done" todo skipped
    where "R = done @ todo"
    and "r i = Some (done, todo, skipped)"
    by (auto elim!: roleMap_SomeE)
  then interpret this_thread:
    reachable_thread P t r s i "done" todo skipped
    by unfold_locales auto
  show ?thesis using step role_ord `R = done @ todo`
    by (fast intro!: listOrd_imp_predOrd
                     this_thread.listOrd_recv_role_imp_listOrd_trace)
qed


lemma send_roleOrd_imp_predOrd:
  assumes step: "(i, step) \<in> steps t"
  and role_exists: "roleMap r i = Some R"
  and role_ord: "listOrd R (Send l pt) step"
  shows "St (i, (Send l pt)) \<prec> St (i, step)"
proof -
  from role_exists
  obtain "done" todo skipped
    where "R = done @ todo"
    and "r i = Some (done, todo, skipped)"
    by (auto elim!: roleMap_SomeE)
  then interpret this_thread:
    reachable_thread P t r s i "done" todo skipped
    by unfold_locales auto
  show ?thesis using step role_ord `R = done @ todo`
    by (fast intro!: listOrd_imp_predOrd
                     this_thread.listOrd_send_role_imp_listOrd_trace)
qed

lemmas roleOrd_imp_predOrd' =
  send_roleOrd_imp_predOrd[OF in_steps_predOrd1, rule_format]
  recv_roleOrd_imp_predOrd[OF in_steps_predOrd1, rule_format]

lemmas roleOrd_imp_step =
  in_steps_predOrd1[OF send_roleOrd_imp_predOrd, rule_format]
  in_steps_predOrd1[OF recv_roleOrd_imp_predOrd, rule_format]

lemmas roleOrd_imp_step' =
  roleOrd_imp_step[OF in_steps_predOrd1, rule_format]

lemma prefixClose_rawI:
  assumes "\<And> st st'. 
    \<lbrakk> nextRel (filter (\<lambda> x. \<not> (noteStep x)) (takeWhile (\<lambda> x. x \<noteq> step) R) @ [step]) st st';
      recvStep st
    \<rbrakk> \<Longrightarrow> \<exists> m. Some m = inst s i (stepPat st) \<and> Ln m \<prec> St (i, st)"
  and "\<And> st st'. 
    \<lbrakk> nextRel (filter (\<lambda> x. \<not> (noteStep x)) (takeWhile (\<lambda> x. x \<noteq> step) R) @ [step]) st st'
    \<rbrakk> \<Longrightarrow> St (i, st) \<prec> St (i, st')"
  shows "prefixClose s t R step i"
using prems by (auto simp: prefixClose_def)

lemma prefixCloseI:
  assumes step: "(i, step) \<in> steps t"
  and role_exists: "roleMap r i = Some R"
  shows "prefixClose s t R step i"
proof -
  from role_exists
  obtain "done" todo skipped
    where R_split: "R = done @ todo"
    and "r i = Some (done, todo,skipped)"
    by (auto elim!: roleMap_SomeE)
  moreover
  then interpret this_thread:
    reachable_thread P t r s i "done" todo skipped
    by unfold_locales auto
  
  from step have "step \<in> set done"
    by (rule this_thread.in_steps_in_done)
  then obtain prefix suffix 
    where done_split: "done = prefix @ step # suffix \<and> step \<notin> set prefix"
    by (auto dest!: split_list_first)
  moreover
  hence "takeWhile (\<lambda>x. x \<noteq> step) (prefix@step#suffix@todo) = prefix"
    by (subst takeWhile_append2) auto
  moreover
  { fix st st'
    assume nextRel: "nextRel (step#rev (filter (\<lambda> x. \<not> (noteStep x)) prefix)) st' st"

    hence in_nextRel: "st' \<in> set (step#rev (filter (\<lambda> x. \<not> (noteStep x)) prefix)) \<and>
      st \<in> set (step#rev (filter (\<lambda> x. \<not> (noteStep x)) prefix))"
      by(auto dest: in_set_nextRel1 in_set_nextRel2)
    hence "st \<in> set done" and "st' \<in> set done"
      using done_split step role_exists nextRel
      by (auto dest: in_set_nextRel1 in_set_nextRel2 filtered_in_done)
    hence "st \<in> set done \<and> st \<notin> skipped" and "st' \<in> set done \<and> st' \<notin> skipped"
      using step in_nextRel
      apply -
      apply(rule conjI, assumption)
      apply(case_tac "st = step")
        apply(fastsimp dest: this_thread.in_steps_conv_done_skipped[THEN iffD1])
      apply(fastsimp dest!: this_thread.note_in_skipped note_filtered_revRole)

      apply(rule conjI, assumption)
      apply(case_tac "st' = step")
        apply(fastsimp dest: this_thread.in_steps_conv_done_skipped[THEN iffD1])
      by(fastsimp dest!: this_thread.note_in_skipped note_filtered_revRole)
    hence steps: "(i, st) \<in> steps t" "(i, st') \<in> steps t"
      by(auto dest: this_thread.in_steps_conv_done_skipped[THEN iffD1])
    { assume "recvStep st" then
      obtain l pt where "st = Recv l pt" by (cases st) auto
      hence "\<exists> m. Some m = inst s i (stepPat st) \<and> Ln m \<prec> St (i, st)"
	using steps by(auto intro!: Ln_before_inp)
    }
    note input = this

    have "listOrd R st st'" 
      using nextRel and R_split and done_split
      by(fastsimp dest: nextRel_imp_listOrd listOrd_rev[THEN iffD1] listOrd_filter)
    hence "St (i, st) \<prec> St (i, st')"
      using role_exists steps R_split
      apply -
      apply(drule this_thread.in_steps_conv_done_skipped[THEN iffD1])
      by(fastsimp dest!: this_thread.roleOrd_notSkipped_imp_listOrd_trace dest:listOrd_imp_predOrd)+
    note input and this
  }
  ultimately show ?thesis
    by (auto simp: prefixClose_def)
qed

text{* Support for the "prefix\_close" command. *}

lemma ext_prefixClose: 
  "\<lbrakk> (i, step) \<in> steps t; roleMap r i = Some R \<rbrakk> \<Longrightarrow>
   prefixClose s t R step i \<and> 
   (recvStep step \<longrightarrow> (\<exists> m. Some m = inst s i (stepPat step) \<and> Ln m \<prec> St (i, step)))"
  by (cases step) (fastsimp intro!: prefixCloseI Ln_before_inp)+

text{* 
  Used for prefix closing assumptions corresponding to a case of
  an annotation completeness induction proof.
*}
lemma thread_prefixClose: 
  assumes thread_exists: "r i = Some (step#done, todo, skipped)"
      and not_skipped:   "step \<notin> skipped"
    shows 
   "(\<forall> st st'. nextRel (step # (filter (\<lambda> x. \<not> (noteStep x)) done)) st st' \<longrightarrow>
      ((recvStep st \<longrightarrow> 
          (\<exists> m. Some m = inst s i (stepPat st) \<and> predOrd t (Ln m) (St (i, st)))
        ) \<and>
        predOrd t (St (i, st)) (St (i, st')))
    ) \<and>
    (recvStep (last (step#done)) \<longrightarrow>
       (\<exists> m. Some m = inst s i (stepPat (last (step#done))) \<and> 
             predOrd t (Ln m) (St (i, (last (step#done))))
       )
    )"
  (is "?prefix \<and> ?inp_last")
proof -
  interpret this_thread: reachable_thread P t r s i "step#done" todo skipped
    using thread_exists by unfold_locales auto
  {
    assume recv: "recvStep (last (step#done))"
    hence last_step: "(i, last (step#done)) \<in> steps t"
      proof
        obtain l pt
          where recv_eq: "(Recv l pt) = (last (step # done))"
          using recv by (fastsimp dest!: recvStepD)
        hence "Recv l pt \<in> set (step # done)" by auto
        thus ?thesis
          using thread_exists recv_eq
          by(fastsimp dest!: this_thread.in_steps_recv[THEN iffD1])
        qed
    hence "?inp_last"
      by (cases "last (step # done)") (fastsimp dest!: Ln_before_inp)+
  }
  moreover
  { 
    fix st st'
    assume "nextRel (step # (filter (\<lambda> x. \<not> (noteStep x)) done)) st st'"
    hence listOrd: "listOrd (step # [x\<leftarrow>done . \<not> noteStep x]) st st'"
      by (auto dest: nextRel_imp_listOrd)
    hence skipped: "st \<notin> skipped \<and> st' \<notin> skipped"
      proof(cases "st = step \<and> st' \<in> set done \<and> \<not> noteStep st'")
        case True
        thus "?thesis" using listOrd not_skipped by (fastsimp dest: this_thread.note_in_skipped)
      next
        case False
        note falseAsms = this
        thus ?thesis using falseAsms listOrd  
          by (cases "listOrd [x\<leftarrow>done . \<not> noteStep x] st st'") 
          (auto simp add: dest: this_thread.note_in_skipped in_set_listOrd1 in_set_listOrd2 )
      qed
    hence  "st \<notin> skipped" "st' \<notin> skipped" by auto

    hence step_ord: "predOrd t (St (i, st)) (St (i, st'))"
    proof(cases "st = step \<and> st' \<in> set [x\<leftarrow>done . \<not> noteStep x]")
      case True
      hence "st' \<in> set done" by auto
      thus ?thesis using listOrd skipped True
        apply -
        apply(drule conjunct1,
              drule_tac ?P = "st = step" and ?Q = "st' \<in> set done" in conjI,
              assumption)
        apply(drule_tac ?Q = "listOrd done st st'" and ?P = "st = step \<and> st' \<in> set done" in disjI1)
        apply(drule listOrd.simps(2)[THEN iffD2])
        by(fastsimp dest: listOrd_imp_predOrd this_thread.listOrd_done_imp_listOrd_trace)
    next
      case False
      note assms = this
      thus ?thesis
      proof(cases "listOrd [x\<leftarrow>done . \<not> noteStep x] st st'")
         case False
         thus ?thesis using assms listOrd by auto
      next
         case True 
         thus ?thesis using assms listOrd skipped
           apply -
           apply(drule listOrd_filter)
           apply(drule_tac ?Q = "listOrd done st st'" and ?P = "st = step \<and> st' \<in> set done" in disjI2)
           apply(drule listOrd.simps(2)[THEN iffD2])
           by (fastsimp dest: listOrd_imp_predOrd this_thread.listOrd_done_imp_listOrd_trace)
      qed
    qed
    hence recv: "recvStep st \<Longrightarrow> 
                 \<exists> m. Some m = inst s i (stepPat st) \<and> predOrd t (Ln m) (St (i, st))"
      using this_thread.roleMap
      by (cases st) (auto intro!: Ln_before_inp dest: in_steps_predOrd1)
    note step_ord recv
  }
  ultimately
  show ?thesis by fast
qed

end

text{* 
  TODO: Find the right place for this lemma. It is used only in
  the "prefix\_close" command.
*}
lemma steps_in_steps: "(i,step) \<in> steps t \<Longrightarrow> (i,step) \<in> steps t"
  by auto


subsection{* Additional Lemmas on Learning Messages *}


context reachable_state
begin

(* TODO: Move *)
lemma nothing_before_IK0: "m \<in> IK0 \<Longrightarrow> \<not> y \<prec> Ln m"
proof(induct arbitrary: y rule: reachable_induct)
  case (send t r s i "done" l pt todo m y)
  then interpret this_state: reachable_state P t r s by unfold_locales
  show ?case using send
    by(fastsimp dest: this_state.knows_IK0)
next
  case (decr t r s m k y)
  then interpret this_state: reachable_state P t r s by unfold_locales
  show ?case using decr
    by(fastsimp dest: this_state.knows_IK0)
next 
  case (lkr t r s a)
  then interpret this_state: reachable_state P t r s by unfold_locales
  show ?case using lkr
    by(fastsimp dest: this_state.knows_IK0)
next 
  case (compr t r s "done" l ty pt todo skipped m y)
  then interpret this_state: reachable_state P t r s by unfold_locales
  show ?case using compr
    by(fastsimp dest: this_state.knows_IK0)
qed auto

lemmas nothing_before_IK0_iffs [iff] = in_IK0_simps[THEN nothing_before_IK0]

end (* rechable_state *)

subsubsection{* Resoning about Variable Contents *}

context reachable_state
begin

lemma inst_AVar_ineqs [iff]:
  "s (AVar v, i) \<noteq> Tup x y"
  "s (AVar v, i) \<noteq> Enc m k"
  "s (AVar v, i) \<noteq> Hash m"
  "s (AVar v, i) \<noteq> PK a"
  "s (AVar v, i) \<noteq> SK a"
  "s (AVar v, i) \<noteq> K a b"
  "s (AVar v, i) \<noteq> KShr A"
  "s (AVar v, i) \<noteq> Lit (ENonce n i')"
  "s (AVar v, i) \<noteq> Lit (EConst c)"
  "s (AVar v, i) \<noteq> Lit (EveNonce n)"
  by (insert inst_AVar_cases[of v i]) 
     (auto simp: Agent_def)

declare inst_AVar_cases[iff]
declare inst_AVar_ineqs[symmetric, iff]

end

subsubsection{* Reducing injective to non-injective agreement proofs *}

lemma iagree_to_niagree:
  assumes niagree:  "\<And> i. prem i \<Longrightarrow> (\<exists> j. conc i j)"
  and     conc_inj: "\<And> i1 i2 j. \<lbrakk> conc i1 j \<and> conc i2 j \<rbrakk> \<Longrightarrow> i1 = i2"
  shows "let prems = prem; 
             concs = conc
         in \<exists>f. inj_on f prems \<and> (\<forall>i. prems i \<longrightarrow> concs i (f i))"
proof -
  let ?f = "\<lambda> i. SOME j. conc i j"
  have "inj_on ?f prem"
    apply(auto simp: inj_on_def mem_def dest!: niagree)
    apply(rule_tac j="(SOME j. conc x j)" in conc_inj[OF conjI])
    apply(rule someI, simp+)+
    done
  moreover have "\<forall> i. prem i \<longrightarrow> conc i (?f i)"
    by(auto simp: inj_on_def dest!: niagree intro: someI)
  ultimately show ?thesis
    by auto
qed

end
