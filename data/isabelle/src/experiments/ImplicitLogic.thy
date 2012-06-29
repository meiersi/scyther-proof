theory Logic
imports
  DirectLogic
begin



fun unpairMsg :: "execmsg \<Rightarrow> trace"
where
  "unpairMsg (Tup x y) = MkUnt x y # unpairMsg x @ unpairMsg y"
| "unpairMsg m         = []"

fun unpairTrace :: "wt_subst \<Rightarrow> trace \<Rightarrow> trace"
where
  "unpairTrace s [] = []"
| "unpairTrace s (MkStep tid (Send l msg) # es) = 
     MkStep tid (Send l msg) # 
     unpairMsg (subst s (spec2exec msg tid)) @
     unpairTrace s es"
| "unpairTrace s (MkDecr m k # es) =
     MkDecr m k # 
     unpairMsg m @ 
     unpairTrace s es"
| "unpairTrace s (e # es) = e # unpairTrace s es"

thm reachable_eout_extend_wts

lemma unpairTrace_append [simp]:
  "unpairTrace s (t@t') = unpairTrace s t @ unpairTrace s t'"
  by(induct t rule: unpairTrace.induct, auto)

lemma extend_wts_assoc:
  "extend_wts (extend_wts s s') s'' = extend_wts s (extend_wts s' s'')"
  sorry


lemma reachable_unpairTrace_extend_wts [simp]:
  "(t, r, s) \<in> reachable P
   \<Longrightarrow> unpairTrace (extend_wts s s') t = unpairTrace s t"
  apply(induct arbitrary: s' rule: reachable.induct)
  apply(simp_all add: extend_wts_assoc extend_wts_conv_subst 
                      reachable_Send_ground)
  done

lemma knows_unpairTrace_subset: 
  "knows s t \<subseteq> knows s (unpairTrace s t)"
  by(induct t rule: unpairTrace.induct, auto)

lemma reachable_append_unpairMsg:
  "\<lbrakk> (t,r,s) \<in> reachable P; m \<in> knows s t \<rbrakk>
   \<Longrightarrow> (t@unpairMsg m, r, s) \<in> reachable P"
proof(induct m arbitrary: t)
  case (Tup x y) show ?case using prems(3-4)
    apply(simp)
    apply(subgoal_tac "t @ MkUnt x y # unpairMsg x @ unpairMsg y = 
                       (t @ MkUnt x y # unpairMsg x) @ unpairMsg y")
    apply(simp only:)
    apply(rule prems(2))
    apply(subgoal_tac "t @ MkUnt x y # unpairMsg x =
                       (t @ [MkUnt x y]) @ unpairMsg x")
    apply(simp only:)
    apply(rule prems(1))
    apply(erule reachable.intros)
    apply(simp_all (no_asm))
    done
next
  case Lit thus ?case by simp next
  case Enc thus ?case by simp next
  case Hash thus ?case by simp next
  case SK thus ?case by simp next
  case PK thus ?case by simp next
  case K thus ?case by simp next
qed


lemma reachable_unpairTrace_reachable:
  "(t,r,s) \<in> reachable P \<Longrightarrow>
   (unpairTrace s t, r, s) \<in> reachable P"
proof(induct rule: reachable.induct)
  case init thus ?case by(simp add: reachable.init)
  case (create t r s tid R \<alpha>) thus ?case
    apply(simp)
    apply(rotate_tac 1)
    apply(drule reachable.create)
    apply(simp+)
    apply(subgoal_tac 
     "(\<lambda>a. if a = tid then Some (newThread R) else r a) =  
      r(tid \<mapsto> newThread R)")
    apply(simp)
    apply(rule ext, simp)
    done
next
  case (recv t r s l msg tid \<alpha>) thus ?case
    apply(simp)
    apply(rule reachable.intros)
    by(auto elim!: subsetD[OF knows_unpairTrace_subset])
next
  case hash thus ?case
    apply(simp)
    apply(rule reachable.intros)
    by(auto elim!: subsetD[OF knows_unpairTrace_subset])
next
  case encr thus ?case
    apply(simp)
    apply(rule reachable.intros)
    by(auto elim!: subsetD[OF knows_unpairTrace_subset])
next
  case tuple thus ?case
    apply(simp)
    apply(rule reachable.intros)
    by(auto elim!: subsetD[OF knows_unpairTrace_subset])
next
  case untup thus ?case
    apply(simp)
    apply(rule reachable.intros)
    by(auto elim!: subsetD[OF knows_unpairTrace_subset])
next
  case (decr t r s m k) thus ?case
    apply(simp add: reachable_append_unpairMsg)
    apply(subgoal_tac "unpairTrace s t @ MkDecr m k # unpairMsg m =
                       (unpairTrace s t @ [MkDecr m k]) @ unpairMsg m")
    apply(simp only:)
    apply(rule reachable_append_unpairMsg)
    apply(erule reachable.intros)
    by(auto elim!: subsetD[OF knows_unpairTrace_subset])
next
  case (send t r s l msg tid) thus ?case
    apply(simp add: reachable_append_unpairMsg)
    apply(subgoal_tac "unpairTrace s t @ MkStep tid (Send l msg) # unpairMsg (subst s (spec2exec msg tid)) =
                       (unpairTrace s t @ [MkStep tid (Send l msg)]) @ unpairMsg (subst s (spec2exec msg tid))")
    apply(simp only:)
    apply(rule reachable_append_unpairMsg)
    apply(erule reachable.intros)
    by(auto elim!: subsetD[OF knows_unpairTrace_subset])
qed

lemma unpairTrace_charn:
  "\<lbrakk> m \<in> knows s t; m' \<in> unpair m \<rbrakk> \<Longrightarrow>
   m' \<in> knows s (unpairTrace s t)"
  apply(induct m)
  apply(auto elim!: subsetD[OF knows_unpairTrace_subset])
  apply(simp add: knows_conv_eout)
  apply(erule disjE)
  apply(force simp: IK0_def)
  apply(clarsimp)
  apply(case_tac x)
  apply(case_tac rolestep)
  apply(simp_all)
  sorry

fun out :: "wt_subst \<Rightarrow> execevent \<Rightarrow> execmsg set"
where
  "out s (MkStep tid (Send lbl msg)) = 
     unpair (subst s (spec2exec msg tid))"
| "out s (MkStep tid (Recv lbl msg)) = {}"
| "out s (MkTup  x y)       = unpair x \<union> unpair y"
| "out s (MkUnt  x y)       = unpair x \<union> unpair y"
| "out s (MkHash m)         = {Hash m}"
| "out s (MkEncr m k)       = {Enc m k}"
| "out s (MkDecr m k)       = unpair m"

definition kn' :: "state \<Rightarrow> execmsg \<Rightarrow> bool"
where "kn' q m' = (case q of (t,r,s) \<Rightarrow> 
                   \<forall> m \<in> unpair (subst s m').
                     m \<in> IK0 \<or> (\<exists> e \<in> set t. m \<in> out s e))"

lemma out_conv_eout:
  "out s e = (\<Union> m \<in> eout s e. unpair m)"
  by(induct e rule: out.induct, auto)

lemma kn'_conv_knows:
  "kn' (t,r,s) m' = 
  (\<forall> m \<in> unpair m'. subst s m \<in> knows s (unpairTrace s t))"
  apply(simp add: kn'_def)
  apply(rule iffI)
  apply(clarify)
  apply(frule unpair_subst_distr)
  apply(drule bspec)
  apply(assumption)
  apply(simp add: out_conv_eout knows_conv_eout)
  apply(subgoal_tac "subst s m \<in> knows s t")
  



section{* Secrecy and Authentication Logic *}

subsection{* Abstract Events *}

datatype logicevent =
   DoStep tid rolestep
 | DoHash execmsg
 | DoEncr execmsg execmsg
 | DoDecr execmsg execmsg


fun substEv :: "wt_subst \<Rightarrow> logicevent \<Rightarrow> logicevent"
where
  "substEv s (DoStep tid step) = DoStep tid step"
| "substEv s (DoHash m)        = DoHash (subst s m)"
| "substEv s (DoEncr m k)      = DoEncr (subst s m) (subst s k)"
| "substEv s (DoDecr m k)      = DoDecr (subst s m) (subst s k)"

fun instEv :: "logicevent \<Rightarrow> execevent"
where
  "instEv (DoStep tid step) = MkStep tid step"
| "instEv (DoHash m)        = MkHash m"
| "instEv (DoEncr m k)      = MkEncr m k"
| "instEv (DoDecr m k)      = MkDecr m k"

fun out :: "wt_subst \<Rightarrow> execevent \<Rightarrow> execmsg set"
where
  "out s (MkStep tid (Send lbl msg)) = 
     unpair (subst s (spec2exec msg tid))"
| "out s (MkStep tid (Recv lbl msg)) = {}"
| "out s (MkTup  x y)       = unpair x \<union> unpair y"
| "out s (MkUnt  x y)       = unpair x \<union> unpair y"
| "out s (MkHash m)         = {Hash m}"
| "out s (MkEncr m k)       = {Enc m k}"
| "out s (MkDecr m k)       = unpair m"


subsection{* Predicates *}


definition kn :: "state \<Rightarrow> execmsg \<Rightarrow> bool"
where "kn q m' = (case q of (t,r,s) \<Rightarrow> 
                   \<forall> m \<in> unpair (subst s m').
                     m \<in> IK0 \<or> (\<exists> e \<in> set t. m \<in> out s e))"

definition ev :: "state \<Rightarrow> logicevent \<Rightarrow> bool"
where "ev q e \<equiv> (case q of (t,r,s) \<Rightarrow> 
                  instEv (substEv s e) \<in> set t)"

definition learn :: "state \<Rightarrow> logicevent \<Rightarrow> execmsg \<Rightarrow> bool"
where "learn q e m' \<equiv> (case q of (t,r,s) \<Rightarrow>  
                        instEv (substEv s e) \<in> set t \<and>                      
                        (\<forall> m \<in> unpair (subst s m'). 
                            m \<in> IK0 \<or> 
                            m \<in> out s (instEv (substEv s e)) \<or>
                           (\<exists> e'. (e',(instEv (substEv s e))) \<in> firstOccOrd t \<and>
                                   m \<in> out s e')
                        ) \<and>
                        (\<exists> m \<in> unpair (subst s m').
                           m \<notin> IK0 \<and> 
                           m \<in> out s (instEv (substEv s e)) \<and> 
                          (\<forall> e'. (e',instEv (substEv s e)) \<in> firstOccOrd t \<longrightarrow> 
                                  m \<notin> out s e'
                          )
                        )
                      )"

definition evbefore :: "state \<Rightarrow> logicevent \<Rightarrow> logicevent \<Rightarrow> bool"
where "evbefore q e1 e2 \<equiv> (case q of (t,r,s) \<Rightarrow>  
                            (instEv (substEv s e1), instEv (substEv s e2))
                            \<in> firstOccOrd t)"

definition knbefore :: "state \<Rightarrow> execmsg \<Rightarrow> logicevent \<Rightarrow> bool"
where "knbefore q m' e \<equiv> (case q of (t,r,s) \<Rightarrow> 
                           instEv (substEv s e) \<in> set t \<and>
                           (\<forall> m \<in> unpair (subst s m').
                              m \<in> IK0 \<or>
                              (\<exists> e'. (e',instEv (substEv s e)) \<in> firstOccOrd t \<and> 
                                     m \<in> out s e'
                              )
                            )
                          )"

definition runs :: "state \<Rightarrow> tid \<Rightarrow> role \<Rightarrow> bool"
where "runs q tid R \<equiv> (case q of (t,r,s) \<Rightarrow> 
                        (case r tid of
                          Some (todo,done) \<Rightarrow> Rep_role R = rev done @ todo
                        | None             \<Rightarrow> False))"

subsection{* Properties of Conversion Operators *}

lemma out_conv_eout:
  "out s e = (\<Union> m \<in> eout s e. unpair m)"
  by(induct e rule: out.induct, auto)

lemma reachable_instEv_substEv_extend_wts [simp]:
  "\<lbrakk> (t,r,s) \<in> reachable P; instEv (substEv s e) \<in> set t \<rbrakk>
    \<Longrightarrow> instEv (substEv (extend_wts s s') e) = instEv (substEv s e)"
  apply(induct e rule: substEv.induct)
  apply(auto simp: extend_wts_conv_subst 
             dest!: reachable_eventMsg_ground)
  done



subsection{* Rules *}

subsubsection{* Simplification *}

lemma kn_simps [simp]:
  "kn q (Tup x y) = (kn q x \<and> kn q y)"
  "kn q (Lit (EConst c))"
  "kn q (Lit (EHonest a))"
  "kn q (Lit (EveNonce n))"
  "kn q (SK (Lit Eve))"
  "kn q (PK (Lit (EHonest a)))"
  "kn q (K (Lit (EHonest a)) (Lit Eve))"
  "kn q (K (Lit Eve) (Lit (EHonest a)))"
  apply(cases q, simp add: add kn_def ball_Un)
  by(cases q, simp add: IK0_def kn_def image_def)+

lemma knbefore_simps:
  "knbefore q (Tup x y) e = (knbefore q x e \<and> knbefore q y e)"
  "ev q e \<Longrightarrow> knbefore q (Lit (EConst c)) e"
  "ev q e \<Longrightarrow> knbefore q (Lit (EHonest a)) e"
  "ev q e \<Longrightarrow> knbefore q (Lit (EveNonce n)) e"
  "ev q e \<Longrightarrow> knbefore q (SK (Lit Eve)) e"
  "ev q e \<Longrightarrow> knbefore q (PK (Lit (EHonest a))) e"
  "ev q e \<Longrightarrow> knbefore q (K (Lit (EHonest a)) (Lit Eve)) e"
  "ev q e \<Longrightarrow> knbefore q (K (Lit Eve) (Lit (EHonest a))) e"
  apply(cases q, simp add: knbefore_def, force)
  by(cases q, simp add: IK0_def knbefore_def image_def ev_def)+


subsubsection{* Purely Logical *}

lemma evbeforeD1: "evbefore q e1 e2 \<Longrightarrow> ev q e1"
  by(auto dest: in_set_firstOccOrd1 simp: evbefore_def ev_def)

lemma evbeforeD2: "evbefore q e1 e2 \<Longrightarrow> ev q e2"
  by(auto dest: in_set_firstOccOrd2 simp: evbefore_def ev_def)

lemma knbeforeD1: "knbefore q m e \<Longrightarrow> kn q m"
  by(auto dest!: in_set_firstOccOrd1 simp: knbefore_def kn_def)

lemma knbeforeD2: "knbefore q m e \<Longrightarrow> ev q e"
  by(auto dest!: in_set_firstOccOrd2 simp: knbefore_def ev_def)

lemma learnD1: "learn q e m \<Longrightarrow> ev q e"
  by(auto simp: learn_def ev_def)

lemma learnD2: "learn q e m \<Longrightarrow> kn q m"
  by(auto dest!: in_set_firstOccOrd1 simp add: learn_def kn_def)

lemma ebefore_irr: "\<not>evbefore q e e"
  by(auto simp: evbefore_def)

lemma ebefore_trans: "\<lbrakk> evbefore q e1 e2; evbefore q e2 e3 \<rbrakk> \<Longrightarrow> evbefore q e1 e3"
  by(auto simp: evbefore_def intro: firstOccOrd_trans)

lemma learn_fun: 
  "\<lbrakk> learn q e1 m; learn q e2 m \<rbrakk> 
  \<Longrightarrow> instEv (substEv (sts q) e1) = instEv (substEv (sts q) e2)"
  apply(clarsimp simp: learn_def)
  apply(drule firstOccOrd_cases)
  apply(assumption)
  apply(erule disjE)
  apply(simp)
  apply(erule disjE)
  apply(thin_tac "\<forall> x \<in> ?X. ?P x")
  apply(drule_tac x=ma in bspec)
  apply(force)
  apply(simp)
  apply(force)
  apply(auto)
  by(auto simp: learn_def dest: firstOccOrd_cases)

lemma learn_knbefore_evbefore:
  "\<lbrakk> learn q e1 m; knbefore q m e2 \<rbrakk> \<Longrightarrow> evbefore q e1 e2"
  apply(clarsimp simp: learn_def knbefore_def evbefore_def)
  apply(drule_tac y="instEv (substEv ya e2)" in firstOccOrd_cases)
  apply(drule in_set_firstOccOrd2, simp)
  apply(safe)
  apply(force)
  apply(subgoal_tac "(e', instEv (substEv ya e1)) \<in> firstOccOrd xa")
  apply(force)
  apply(rule firstOccOrd_trans)
  apply(auto)
  done

lemma runs_fun: "\<lbrakk> runs q tid R1; runs q tid R2 \<rbrakk> \<Longrightarrow> R1 = R2"
  by(auto simp: runs_def Rep_role_inject[symmetric] split: option.splits )

subsubsection{* Role Order *}

 
lemma evbefore_roleOrd:
  "\<lbrakk> ev q (DoStep tid step);  runs q tid R;
     (prev, step) \<in> roleOrd R; q \<in> reachable P \<rbrakk> 
   \<Longrightarrow> evbefore q (DoStep tid prev) (DoStep tid step)"
  apply(clarsimp simp: ev_def evbefore_def firstOccOrd_def runs_def
                split: option.splits)
  apply(rename_tac t r s todo "done")
  apply(unfold roleOrd_def)
  apply(rule reachable_roleOrd)
  apply(assumption)
  apply(assumption)
  apply(auto dest: reachable_todo_notin_trace reachable_done_in_trace in_set_listOrd2)
  done


subsubsection{* Input Messages *}

fun einp :: "wt_subst \<Rightarrow> execevent \<Rightarrow> execmsg set"
where
  "einp s (MkStep tid (Send l m)) = {}"
| "einp s (MkStep tid (Recv l m)) = {subst s (spec2exec m tid)}"
| "einp s (MkHash m)              = {m}"
| "einp s (MkTup x y)             = {x, y}"
| "einp s (MkUnt x y)             = {Tup x y}"
| "einp s (MkEncr m k)            = {m, k}"
| "einp s (MkDecr m k)            = {Enc m k, inv k}"

fun inp :: "logicevent \<Rightarrow> execmsg set"
where
  "inp (DoStep tid (Send l m)) = {}"
| "inp (DoStep tid (Recv l m)) = unpair (spec2exec m tid)"
| "inp (DoHash m)            = unpair m"
| "inp (DoEncr m k)          = unpair m \<union> unpair k"
| "inp (DoDecr m k)          = insert (Enc m k) (unpair (inv k))"


lemma einp_ground_by_eventMsg_ground:
  "\<lbrakk> m \<in> einp s e; ground (eventMsg s e) \<rbrakk> \<Longrightarrow> ground m"
  by(induct e rule: einp.induct, auto)

lemma reachable_einp_extend_wts [simp]:
  "\<lbrakk> (t,r,s) \<in> reachable P; e \<in> set t \<rbrakk>
    \<Longrightarrow> einp (extend_wts s s') e = einp s e"
  apply(induct rule: einp.induct)
  apply(auto dest: reachable_eventMsg_ground 
             simp: extend_wts_conv_subst)
  done

lemma reachable_knows_einp:
  "\<lbrakk> (t,r,s) \<in> reachable P; e \<in> set t; m \<in> einp s e \<rbrakk>
   \<Longrightarrow> m \<in> knows s t"
thm reachable_knows_extend_wts

thm reachable_einp_extend_wts

  by(induct arbitrary: e rule: reachable.induct, auto)

lemma reachable_knows_before_einp:
  "\<lbrakk> (t,r,s) \<in> reachable P; e \<in> set t; m \<in> einp s e \<rbrakk>
   \<Longrightarrow> 
   m \<in> IK0 \<or> (\<exists> e' \<in> set t. (e', e) \<in> firstOccOrd t \<and> m \<in> eout s e')"
  apply(induct arbitrary: e m rule: reachable.induct)
  apply(simp_all)
  apply(erule disjE, simp)
  apply(force intro!: firstOccOrd_appendI1)
  apply((thin_tac "dom_wts ?x = ?X")?, (thin_tac "ran_wts ?x = ?X")?)
  apply(case_tac "e \<in> set t")
  apply(force intro!: firstOccOrd_appendI1)
  apply(force simp: knows_conv_eout intro!: firstOccOrd_appendI2)
  apply(case_tac "e \<in> set t")
  apply(force intro!: firstOccOrd_appendI1)
  apply(force simp: knows_conv_eout intro!: firstOccOrd_appendI2)
  apply(case_tac "e \<in> set t")
  apply(force intro!: firstOccOrd_appendI1)
  apply(force simp: knows_conv_eout intro!: firstOccOrd_appendI2)
  apply(case_tac "e \<in> set t")
  apply(force intro!: firstOccOrd_appendI1)
  apply(force simp: knows_conv_eout intro!: firstOccOrd_appendI2)
  apply(case_tac "e \<in> set t")
  apply(force intro!: firstOccOrd_appendI1)
  apply(force simp: knows_conv_eout intro!: firstOccOrd_appendI2)
  apply(case_tac "e \<in> set t")
  apply(force intro!: firstOccOrd_appendI1)
  apply(force simp: knows_conv_eout intro!: firstOccOrd_appendI2)
  done



lemma Recv_knbefore:
  "\<lbrakk>  ev q (DoStep tid (Recv l msg)); 
      m \<in> unpair (spec2exec msg tid); 
      q \<in> reachable P \<rbrakk> 
   \<Longrightarrow> knbefore q m (DoStep tid (Recv l msg))"
  apply(cases q, rename_tac t r s)
  apply(simp add: ev_def knbefore_def)
  apply(drule reachable_knows_before_einp, assumption, simp)
  apply(drule unpair_subst_distr)
  apply(simp add: out_conv_eout knows_conv_eout)
  apply(erule disjE)
  apply(drule in_IK0_by_unpair, assumption, simp)
  apply(force)
  done

lemma Hash_knbefore:
  "\<lbrakk>  ev q (DoHash m'); m \<in> unpair m'; q \<in> reachable P \<rbrakk> 
   \<Longrightarrow> knbefore q m (DoHash m')"
  apply(cases q, rename_tac t r s)
  apply(simp add: ev_def knbefore_def)
  apply(drule reachable_knows_before_einp, assumption, simp)
  apply(drule unpair_subst_distr)
  apply(simp add: out_conv_eout knows_conv_eout)
  apply(erule disjE)
  apply(drule in_IK0_by_unpair, assumption, simp)
  apply(force)
  done

lemma Encr_knbefore_msg:
  "\<lbrakk>  ev q (DoEncr m' k'); m \<in> unpair m'; q \<in> reachable P \<rbrakk> 
   \<Longrightarrow> knbefore q m (DoEncr m' k')"
  apply(cases q, rename_tac t r s)
  apply(simp add: ev_def knbefore_def)
  apply(drule reachable_knows_before_einp, assumption)
  apply(simp, rule disjI1, rule refl)
  apply(drule unpair_subst_distr)
  apply(simp add: out_conv_eout knows_conv_eout)
  apply(erule disjE)
  apply(drule in_IK0_by_unpair, assumption, simp)
  apply(force)
  done

lemma Encr_knbefore_key:
  "\<lbrakk>  ev q (DoEncr m' k'); m \<in> unpair k'; q \<in> reachable P \<rbrakk> 
   \<Longrightarrow> knbefore q m (DoEncr m' k')"
  apply(cases q, rename_tac t r s)
  apply(simp add: ev_def knbefore_def)
  apply(drule reachable_knows_before_einp, assumption)
  apply(simp, rule disjI2, rule refl)
  apply(drule unpair_subst_distr)
  apply(simp add: out_conv_eout knows_conv_eout)
  apply(erule disjE)
  apply(drule in_IK0_by_unpair, assumption, simp)
  apply(force)
  done

lemma Decr_knbefore_enc:
  "\<lbrakk>  ev q (DoDecr m k); q \<in> reachable P \<rbrakk> 
   \<Longrightarrow> knbefore q (Enc m k) (DoDecr m k)"
  apply(cases q, rename_tac t r s)
  apply(simp add: ev_def knbefore_def)
  apply(drule reachable_knows_before_einp, assumption)
  apply(simp, rule disjI1, rule refl)
  apply(force simp: out_conv_eout knows_conv_eout)
  done

lemma Decr_knbefore_key:
  "\<lbrakk>  ev q (DoDecr m' k'); m \<in> unpair (inv k'); q \<in> reachable P \<rbrakk> 
   \<Longrightarrow> knbefore q m (DoDecr m' k')"
  apply(cases q, rename_tac t r s)
  apply(simp add: ev_def knbefore_def)
  apply(drule reachable_knows_before_einp, assumption)
  apply(simp, rule disjI2, rule refl)
  apply(drule unpair_subst_distr)
  apply(simp add: out_conv_eout knows_conv_eout)
  apply(erule disjE)
  apply(drule in_IK0_by_unpair, assumption, simp)
  apply(force)
  done


lemmas Hash_kn = knbeforeD1[OF Hash_knbefore, rule_format]



subsubsection{* Decryption Chains *}

types chain = "(specmsg \<times> specmsg) list \<times> specmsg"

fun msgChains :: "specmsg \<Rightarrow> chain list"
where
  "msgChains (Lit (SNonce n))      = [([], Lit (SNonce n))]"
| "msgChains (Lit (SVar (MVar n))) = [([], Lit (SVar (MVar n)))]"
| "msgChains (Lit _)               = []"
| "msgChains (Tup x y) = msgChains x @ msgChains y"
| "msgChains (Enc m k) = 
     ([], Enc m k) # 
     map (\<lambda> (encs,end). ((m,k)#encs,end)) (msgChains m)"
| "msgChains (Hash m)  = [([], Hash m)]"
| "msgChains (K a b)   = [([], K a b) ]"
| "msgChains (PK a)    = [([], PK a)  ]"
| "msgChains (SK a)    = [([], SK a)  ]"

fun chainStart :: "chain \<Rightarrow> specmsg"
where
  "chainStart ([],start)  = start"
| "chainStart ((m,k)#_,_) = Enc m k"

fun chainEnd :: "chain \<Rightarrow> specmsg"
where 
  "chainEnd (_,end) = end"

lemma chainEnd_in_parts:
  "c \<in> set (msgChains msg) \<Longrightarrow> chainEnd c \<in> parts msg"
  apply(induct msg arbitrary: c, case_tac lit)
  apply(auto)
  by(case_tac varid, auto)

(* if there are no long-term-keys in the parts of the message 
   then chain end is not part of it *)
lemma no_ltkeys_chainEnd: 
  "\<lbrakk> no_ltkeys msg; c \<in> set (msgChains msg) \<rbrakk> \<Longrightarrow> 
   K a b \<noteq> chainEnd c \<and> PK a \<noteq> chainEnd c \<and> SK a \<noteq> chainEnd c"
  apply(induct msg arbitrary: c, case_tac lit)
  apply(simp_all)
  apply(case_tac varid)
  by(simp+, force+)


fun chain :: "state \<Rightarrow> tid \<Rightarrow> chain \<Rightarrow> bool"
where
  "chain q tid ([],      _  ) = True"
| "chain q tid ([(m,k)], end) = 
     learn q (DoDecr (spec2exec m tid) 
                     (spec2exec k tid)) 
             (spec2exec end tid)"
| "chain q tid ((m,k)#(m',k')#encs, end) =
    (learn q (DoDecr (spec2exec m tid) 
                     (spec2exec k tid)) 
             (spec2exec (Enc m' k') tid)
     \<and> chain q tid ((m',k')#encs, end)
    )"

lemma kn_rolemap_inv: 
  "kn (t, r', s) m \<Longrightarrow> kn (t, r, s) m"
  by(simp add: kn_def)

(*
lemma reachable_kn_extend_wts [simp]:
  "\<lbrakk> (t,r,s) \<in> reachable P \<rbrakk>
  \<Longrightarrow> kn (t,r, extend_wts s s') m = kn (t,r,s) m"
  apply(simp add: kn_def)

*)

lemma kn_substI: "kn q m \<Longrightarrow> kn q (subst (sts q) m)"
  by(auto simp: kn_def)

lemma kn_substE: 
  "\<lbrakk> kn q (subst s m); subst (sts q) (subst s m) = subst (sts q) m \<rbrakk>
  \<Longrightarrow> kn q m"
  by(auto simp: kn_def)

thm extend_wts_conv_subst

lemma subst_subdomain: 
  "dom_wts s' \<subseteq> dom_wts s \<Longrightarrow> subst s' (subst s m) = subst s m"
  apply(induct m rule: subst.induct, simp_all)
  apply(case_tac "l \<in> dom_wts s")
  apply(auto simp: dom_wts_def)
  done

lemma substEv_subdomain:
  "dom_wts s' \<subseteq> dom_wts s \<Longrightarrow> substEv s' (substEv s e) = substEv s e"
  by(induct e rule: substEv.induct, auto intro!: subst_subdomain)

lemma reachable_kn_extend_wts [simp]:
  "(t,r,s) \<in> reachable P \<Longrightarrow> 
   kn (t,r,extend_wts s s') m = kn (t,r,s) (subst (extend_wts s s') m)"
  apply(subgoal_tac "subst s (subst (extend_wts s s') m) = 
                     subst (extend_wts s s') m")
  apply(auto simp: kn_def out_conv_eout
           intro!: subst_subdomain)
  done



lemma reachable_learn_extend_wts [simp]:
  "(t,r',s) \<in> reachable P \<Longrightarrow> 
   learn (t,r,extend_wts s s') e m = 
   learn (t,r',s) (substEv (extend_wts s s') e) (subst (extend_wts s s') m)"
  apply(subgoal_tac "subst s (subst (extend_wts s s') m) = 
                     subst (extend_wts s s') m")
  apply(subgoal_tac "substEv s (substEv (extend_wts s s') e) = 
                     substEv (extend_wts s s') e")
  apply(simp add: learn_def out_conv_eout)
  apply(rule iffI)
  apply(force dest: in_set_firstOccOrd1)
  apply(force dest: in_set_firstOccOrd1)
  apply(auto intro!: substEv_subdomain subst_subdomain)
  done

lemma Rep_wt_subst_atomic: "\<exists> l'. Rep_wt_subst s l = Lit l'"
  apply(insert Rep_wt_subst_welltyped[of s])
  apply(simp add: welltyped_def)
  apply(drule_tac x=l in spec, auto)
  done

lemma Rep_wt_subst_noteq_simps [simp]: 
  "Rep_wt_subst s l \<noteq> Hash m"
  "Rep_wt_subst s l \<noteq> Enc m k"
  "Rep_wt_subst s l \<noteq> Tup x y"
  "Rep_wt_subst s l \<noteq> PK a"
  "Rep_wt_subst s l \<noteq> SK a"
  "Rep_wt_subst s l \<noteq> K a b"
  by(insert Rep_wt_subst_atomic[of s l], auto)

lemma kn_append_cases: 
  "kn (t@t', r, s) m \<Longrightarrow> 
   kn (t, r, s) m \<or>
   (\<exists> e \<in> set t'. e \<notin> set t \<and> subst s m \<in> out s e)"
  by(auto simp: kn_def)

lemma firstOccOrd_Nil [simp]: "firstOccOrd [] = {}"
  by(simp add: firstOccOrd_def)

lemma firstOccOrd_Snoc1 [simp]: 
  "x \<in> set xs \<Longrightarrow> firstOccOrd (xs@[x]) = firstOccOrd xs"
  by(induct xs rule: rev_induct, auto simp: firstOccOrd_def)

lemma firstOccOrd_Snoc2 [simp]:
  "x \<notin> set xs \<Longrightarrow> 
   firstOccOrd (xs@[x]) = firstOccOrd xs \<union> { (y,x) | y. y \<in> set xs }"
  by(induct xs rule: rev_induct, auto simp: firstOccOrd_def)

thm if_splits(1)

lemma firstOccOrd_splits:
  "P (firstOccOrd (xs@[x])) =
   ((x \<in> set xs \<longrightarrow> P (firstOccOrd xs)) \<and>
    (x \<notin> set xs \<longrightarrow> P (firstOccOrd xs \<union> { (y,x) | y. y \<in> set xs })))"
  by(auto, case_tac "x \<in> set xs", auto)

lemma firstOccOrd_decomp: 
  "(e,e') \<in> firstOccOrd t 
  \<Longrightarrow> \<exists> xs ys zs. t = xs@e#ys@e'#zs \<and> 
                  e \<notin> set xs \<and> e' \<notin> set xs \<and> e \<noteq> e' \<and> e' \<notin> set ys"
  apply(induct t rule: rev_induct)
  apply(auto split: firstOccOrd_splits)
  apply(case_tac "x \<in> set xs")
  apply(simp_all)
  apply(force)
  apply(erule disjE)
  apply(force)
  apply(clarsimp)
  apply(drule split_list_first)
  apply(clarsimp)
  apply(auto)
  done


lemma append_eq_append_before_first:
  "\<lbrakk> vs @ y#ws = xs @ y#ys; y \<notin> set vs; y \<notin> set xs;
     x \<in> set xs \<rbrakk>
   \<Longrightarrow> x \<in> set vs"
  apply(simp add: append_eq_append_conv2)
  apply(auto)
  apply(case_tac us)
  apply(auto)
  done

lemma firstOccOrd_appendD1: 
  "\<lbrakk> (e,e') \<in> firstOccOrd (t@t'); e' \<in> set t \<rbrakk> \<Longrightarrow> (e,e') \<in> firstOccOrd t"
  apply(drule firstOccOrd_decomp)
  apply(clarsimp)
  apply(drule split_list_first)
  apply(clarsimp)
  apply(rule firstOccOrd_appendI2)
  apply(simp_all)
  apply(simp add: append_eq_append_conv2)
  apply(auto)
  apply(case_tac us, auto)
  apply(case_tac us, auto)
  done

lemma learn_appendI1: 
  "learn (t,r,s) e m \<Longrightarrow> learn (t@t', r', s) e m"
  by(auto simp: learn_def dest: firstOccOrd_appendD1)

lemma learn_Snoc_MkTup [simp]:
  "learn (t@[MkTup x y],r,s) = learn (t,r,s)"
  apply(rule ext, rule ext, rename_tac e m, case_tac e)
  by(auto simp: learn_def split: firstOccOrd_splits)

lemma learn_Snoc_MkUnt [simp]:
  "learn (t@[MkUnt x y],r,s) = learn (t,r,s)"
  apply(rule ext, rule ext, rename_tac e m, case_tac e)
  by(auto simp: learn_def split: firstOccOrd_splits)
 
lemma runs_free_args:
  "runs (t',r,s') = runs (t,r,s)"
  by(rule ext,rule ext, simp add: runs_def)

(* TODO: Using Isar this lemma should be removed *)
lemma chain_Snoc_MkTup_aux [rule_format]:
  "q = (t,r,s) \<longrightarrow> 
   chain (t@[MkTup x y],r,s) tid c = chain q tid c"
  by(induct c rule: chain.induct, auto)

lemma chain_Snoc_MkTup [simp]:
  "chain (t@[MkTup x y],r,s) = chain (t,r,s)"
  by(rule ext, rule ext, auto intro!: chain_Snoc_MkTup_aux)

thm kn_def

lemma learn:
  "\<lbrakk> (t,r,s) \<in> reachable P; kn (t,r,s) m' \<rbrakk> \<Longrightarrow>
   subst s m' \<in> IK0 \<or>
   (\<exists> m.   m' = Hash m   \<and> learn (t,r,s) (DoHash m)   (Hash m)) \<or>
   (\<exists> m k. m' = Enc  m k \<and> learn (t,r,s) (DoEncr m k) (Enc m k)) \<or>
   (\<exists> R \<in> P. \<exists> l msg. Send l msg \<in> roleEvs R \<and>
      (\<exists> c \<in> set (msgChains msg). \<exists> tid.
         runs (t,r,s) tid R \<and> 
         learn (t,r,s) (DoStep tid (Send l msg)) 
                       (spec2exec (chainStart c) tid) \<and>
         chain (t,r,s) tid c \<and>
         subst s m' = subst s (spec2exec (chainEnd c) tid)
      )
   )"
proof (induct arbitrary: m' rule: reachable.induct)
  case init thus ?case by(simp add: kn_def)
next
  case (tuple t r s x y) thus ?case
    apply(simp)
    apply(subst runs_free_args[where t=t and s=s])


next
  case (hash t r s m) thus ?case
    apply(insert kn_append_cases[OF prems(4)])
    apply(erule disjE)
    apply(drule prems(2))
    apply(erule disjE)
    apply(simp)
    apply(erule disjE)
    apply(rule disjI2, rule disjI1)
    apply(simp add: learn_def)
    apply(clarsimp)



    apply(insert prems(1))
    apply(rule disjI2, rule disjI1)



  case (create t r s tid R \<alpha>) show ?case using prems(1,7)
    apply(drule_tac r=r in kn_rolemap_inv)
    apply(simp)
    apply(drule prems(2))
    apply(erule disjE)
    apply(subst (asm) subst_subdomain)
    apply(force)
    apply(simp)
    apply(erule disjE)
    apply(rule disjI2,rule disjI1)
    apply(clarsimp)
    apply(cases m')
    apply(simp_all)
    apply(erule disjE)
    apply(rule disjI2, rule disjI2, rule disjI1)
    apply(cases m')
    apply(simp_all)
    apply(rule disjI2, rule disjI2, rule disjI2)
    apply(clarsimp)
    apply(case_tac "tida = tid")
    apply(clarsimp)
    apply(insert prems(3))
    apply(force simp: runs_def dom_def split: option.splits)
    apply(rule bexI)
    apply(rule exI, rule exI, rule conjI)
    apply(assumption)
    apply(rule_tac x="(a,b)" in bexI)
    apply(rule_tac x="tida" in exI)
    apply(simp add: runs_def)
    sorry
next



thm reachable_eout_extend_wts


    apply(simp add: kn_def out_conv_eout)
  sorry

lemma learn_Hash:
  "\<lbrakk> q \<in> reachable P; kn q (Hash m) \<rbrakk> \<Longrightarrow>
   learn q (DoHash m) (Hash m) \<or>
   (\<exists> R \<in> P. \<exists> l msg. Send l msg \<in> roleEvs R \<and>
      (\<exists> c \<in> set (msgChains msg). \<exists> tid.
         runs q tid R \<and> 
         learn q (DoStep tid (Send l msg)) (spec2exec (chainStart c) tid) \<and>
         chain q tid c \<and>
         Hash (subst (sts q) m)  = subst (sts q) (spec2exec (chainEnd c) tid)
      )
   )"
  apply(drule learn, assumption)
  by(auto simp: IK0_def)

lemma learn_SK:
  "\<lbrakk> q \<in> reachable P; kn q (SK a) \<rbrakk> \<Longrightarrow>
   subst (sts q) a = Lit Eve"
  apply(drule learn, assumption)
  apply(auto)
  apply(force simp: IK0_def)
  apply(case_tac b, case_tac lit)
  apply(simp_all)
  apply(insert Rep_wt_subst_welltyped[of "sts q"])
  apply(simp add: welltyped_def)
  apply(drule_tac x="EVar varid tid" in spec)
  apply(force)
  apply(simp add: roleEvs_def)
  apply(drule Rep_role_Send_no_ltkeys)
  apply(drule no_ltkeys_chainEnd)
  apply(assumption)
  apply(force)
  done