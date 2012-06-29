theory WelltypedSubst
imports ExecMessage
begin


subsection{* Well-typed Ground Atomic Substitutions *}

text{* 
  TODO: Revamp proofs and tool setup, because the current setup is too ad-hoc.
*}

definition groundSubst :: "(execlit \<Rightarrow> execmsg) \<Rightarrow> bool"
where "groundSubst s \<equiv> \<forall> l. s l \<noteq> Lit l \<longrightarrow> ground (s l)"

definition welltyped :: "(execlit \<Rightarrow> execmsg) \<Rightarrow> bool"
where 
"welltyped s \<equiv> \<forall> l. s l \<noteq> Lit l \<longrightarrow>
   (\<exists> varid tid. l = EVar varid tid \<and> 
     (
       (\<exists> a. varid = (AVar a) \<and> 
             (s l = Lit Eve \<or> (\<exists> n. s l = Lit (EHonest n)))
        ) \<or>
       (\<exists> v. varid = (MVar v) \<and> 
             ((\<exists> n tid'. s l = Lit (ENonce n tid')) \<or>
              (\<exists> n. s l = Lit (EveNonce n)))
        )
      )
    )"

typedef wt_subst = "\<lambda> s. s \<in> welltyped \<and> s \<in> groundSubst"
  by(auto simp: mem_def welltyped_def groundSubst_def ran_def)


fun subst :: "wt_subst \<Rightarrow> execmsg \<Rightarrow> execmsg"
where
  "subst s (Lit l)   = Rep_wt_subst s l"
| "subst s (Tup x y) = Tup  (subst s x) (subst s y)"
| "subst s (Enc m k) = Enc  (subst s m) (subst s k)"
| "subst s (Hash m)  = Hash (subst s m)"
| "subst s (K a b)   = K    (subst s a) (subst s b)"
| "subst s (PK a)    = PK   (subst s a)"
| "subst s (SK a)    = SK   (subst s a)"


definition empty_wts :: "wt_subst"
where "empty_wts \<equiv> Abs_wt_subst Lit"

definition extend_wts :: "wt_subst \<Rightarrow> wt_subst \<Rightarrow> wt_subst"
where "extend_wts s1 s2 \<equiv> Abs_wt_subst (subst s2 o Rep_wt_subst s1)"

definition dom_wts :: "wt_subst \<Rightarrow> execlit set"
where "dom_wts s \<equiv> { l. Rep_wt_subst s l \<noteq> Lit l }"

definition ran_wts :: "wt_subst \<Rightarrow> execmsg set"
where "ran_wts s \<equiv> { Rep_wt_subst s l | l. Rep_wt_subst s l \<noteq> Lit l }"


subsubsection{* Properties *}

lemma Rep_wt_subst_welltyped: "welltyped (Rep_wt_subst s)"
  by(insert Rep_wt_subst, simp add: wt_subst_def mem_def)


lemma Rep_wt_subst_groundSubst: "groundSubst (Rep_wt_subst s)"
  by(insert Rep_wt_subst, simp add: wt_subst_def mem_def)

lemma Rep_wt_subst_ground [simp]: 
  "l \<in> dom_wts s \<Longrightarrow> ground (Rep_wt_subst s l)"
  apply(insert Rep_wt_subst_groundSubst[of s])
  by(auto simp: dom_wts_def groundSubst_def)

lemma Rep_wt_subst_EVar_notin_dom [simp]: 
  "EVar v tid \<notin> dom_wts s \<Longrightarrow> 
   Rep_wt_subst s (EVar v tid) = Lit (EVar v tid)"
  apply(insert Rep_wt_subst_groundSubst[of s])
  by(auto simp: dom_wts_def groundSubst_def)

lemma Rep_wt_subst_simps [simp]: 
  "Rep_wt_subst s (EConst c)     = Lit (EConst c)"
  "Rep_wt_subst s (EHonest a)    = Lit (EHonest a)"
  "Rep_wt_subst s (ENonce n tid) = Lit (ENonce n tid)"
  "Rep_wt_subst s (Eve)          = Lit (Eve)"
  "Rep_wt_subst s (EveNonce n)   = Lit (EveNonce n)"
  by(insert Rep_wt_subst_welltyped[of s], auto simp: welltyped_def)

lemma Rep_wt_subst_MVar_splits:
  "P (Rep_wt_subst s (EVar (MVar v) tid)) = (
   (          Rep_wt_subst s (EVar (MVar v) tid) = (Lit (EVar (MVar v) tid)) \<longrightarrow> P (Lit (EVar (MVar v) tid))) \<and> 
   (\<forall> n tid'. Rep_wt_subst s (EVar (MVar v) tid) = (Lit (ENonce n tid'))     \<longrightarrow> P (Lit (ENonce n tid'))) \<and>
   (\<forall> n.      Rep_wt_subst s (EVar (MVar v) tid) = (Lit (EveNonce n))        \<longrightarrow> P (Lit (EveNonce n))))"
  apply(insert Rep_wt_subst_welltyped[of s])
  apply(simp add: welltyped_def)
  apply(drule_tac x="EVar (MVar v) tid" in spec)
  by(auto)

lemma Rep_wt_subst_AVar_splits:
  "P (Rep_wt_subst s (EVar (AVar a) tid)) = (
   (     Rep_wt_subst s (EVar (AVar a) tid) = (Lit (EVar (AVar a) tid)) \<longrightarrow> P (Lit (EVar (AVar a) tid))) \<and> 
   (\<forall> n. Rep_wt_subst s (EVar (AVar a) tid) = (Lit (EHonest n))         \<longrightarrow> P (Lit (EHonest n))) \<and>
   (\<forall> n. Rep_wt_subst s (EVar (AVar a) tid) = (Lit Eve)                 \<longrightarrow> P (Lit Eve)))"
  apply(insert Rep_wt_subst_welltyped[of s])
  apply(simp add: welltyped_def)
  apply(drule_tac x="EVar (AVar a) tid" in spec)
  by(auto)

lemma Rep_wt_subst_AVar_cases:
  "(     Rep_wt_subst s (EVar (AVar a) tid) = (Lit (EVar (AVar a) tid))) \<or>
   (\<exists> n. Rep_wt_subst s (EVar (AVar a) tid) = (Lit (EHonest n))) \<or>
   (Rep_wt_subst s (EVar (AVar a) tid) = (Lit Eve))"
  apply(insert Rep_wt_subst_welltyped[of s])
  by(auto simp: welltyped_def)

lemma subst_ground_msg [simp]: "ground m \<Longrightarrow> subst s m = m"
  by(induct m, case_tac lit, auto)

lemma subst_idem [simp]: "subst s (subst s m) = subst s m"
  apply(induct m, case_tac lit, simp_all)
  apply(case_tac "EVar varid nat \<in> dom_wts s", simp+)
  done

lemma subst_Rep_wt_subst_idem [simp]:
  "subst s (Rep_wt_subst s l) = Rep_wt_subst s l"
  apply(rule_tac s="subst s (Lit l)" in subst)
  apply(simp, rule subst_idem)
  done

lemma Abs_wt_subst_extend_wts_inverse [simp]:
  "Rep_wt_subst (Abs_wt_subst (subst s' o Rep_wt_subst s)) = subst s' o Rep_wt_subst s"
  apply(subst Abs_wt_subst_inverse)
  apply(insert Rep_wt_subst_welltyped[of s])
  apply(insert Rep_wt_subst_welltyped[of s'])
  apply(simp add: welltyped_def groundSubst_def o_def wt_subst_def mem_def)
  apply(safe)
  apply(drule_tac x=l in spec)+
  defer 1
  apply(drule_tac x=l in spec)+
  apply(auto)
  done

lemma extend_wts_conv_subst: 
  "subst (extend_wts s s') m = subst s' (subst s m)"
  by(induct m, induct_tac lit, auto simp: extend_wts_def)


lemma dom_wts_empty_wts [simp]: "dom_wts empty_wts = {}"
  by(simp add: dom_wts_def empty_wts_def wt_subst_def
               Abs_wt_subst_inverse welltyped_def groundSubst_def mem_def)

lemma dom_wts_extend_wts [simp]: "dom_wts (extend_wts s s') = dom_wts s \<union> dom_wts s'"
  apply(auto simp: dom_wts_def extend_wts_def)
  apply(insert Rep_wt_subst_welltyped[of s])
  apply(insert Rep_wt_subst_welltyped[of s'])
  apply(simp add: welltyped_def groundSubst_def o_def wt_subst_def mem_def)
  apply(drule_tac x=x in spec)+
  apply(auto)
  done


lemma Abs_wt_subst_empty_wts_inverse [simp]: 
  "Rep_wt_subst (Abs_wt_subst Lit) = Lit"
  by(simp add: mem_def welltyped_def wt_subst_def 
               groundSubst_def Abs_wt_subst_inverse)

lemma subst_empty_wts [simp]: "subst empty_wts m = m"
  by(induct m, auto simp: empty_wts_def)

lemma unpair_subst_distr: "x \<in> unpair m \<Longrightarrow> subst s x \<in> unpair (subst s m)"
  apply(induct m rule: subst.induct, auto)
  apply(subgoal_tac "welltyped (Rep_wt_subst s)") defer 1
  apply(rule Rep_wt_subst_welltyped)
  apply(simp add: welltyped_def)
  apply(drule_tac x=l in spec)
  apply(auto)
  done

lemma inv_subst_comm [simp]: 
  "subst s (inv m) = inv (subst s m)"
  apply(induct m rule: subst.induct, auto)
  apply(subgoal_tac "welltyped (Rep_wt_subst s)")
  apply(simp add: welltyped_def)
  apply(drule_tac x=l in spec)
  apply(auto simp: Rep_wt_subst_welltyped)
  done


lemma ground_subst_s2e_conv_FV: 
  "ground (subst s (s2e msg tid)) = (\<forall> v \<in> FV msg. EVar v tid \<in> dom_wts s)"
  apply(induct msg, induct_tac lit)
  apply(simp_all)
  apply(case_tac "EVar varid tid \<in> dom_wts s")
  apply(auto)
  done

lemma subst_subdomain: 
  "dom_wts s' \<subseteq> dom_wts s \<Longrightarrow> subst s' (subst s m) = subst s m"
  apply(induct m rule: subst.induct, simp_all)
  apply(case_tac "l \<in> dom_wts s")
  apply(auto simp: dom_wts_def)
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

lemma Rep_wt_subst_AV_noteq [simp]:
  "Rep_wt_subst s (EVar (AVar a) tid) \<noteq> Lit (EConst c)"
  "Rep_wt_subst s (EVar (AVar a) tid) \<noteq> Lit (ENonce n' tid')"
  apply(insert Rep_wt_subst_AVar_cases[of "s" a tid])
  apply(auto)
  done

lemma subst_notin_dom_wts [iff]:
  "(Rep_wt_subst s x = Lit x) = (x \<notin> dom_wts s)"
  by(auto simp: dom_wts_def)

(* NOTE: makes unfolding dom_wts using simp loop *)
lemma subst_in_dom_wts [iff]:
  "(Rep_wt_subst s x \<noteq> Lit x) = (x \<in> dom_wts s)"
 by(simp)

lemma Rep_wt_subst_AVar_in_IK0 [intro!, simp]:
  "EVar (AVar a) tid \<in> dom_wts s \<Longrightarrow>
   Rep_wt_subst s (EVar (AVar a) tid) \<in> IK0"
  by(insert Rep_wt_subst_AVar_cases[of s a tid], auto)

lemma EVar_ground_imp_in_dom_wts [iff]:
  "(ground (Rep_wt_subst s (EVar v tid))) = (EVar v tid \<in> dom_wts s)"
  apply(case_tac "(Rep_wt_subst s (EVar v tid)) = Lit ( (EVar v tid))")
  apply(auto)
  done

lemma unpair_Rep_wt_subst_AVar [simp]:
  "unpair (Rep_wt_subst s (EVar (AVar a) tid))= 
   {Rep_wt_subst s (EVar (AVar a) tid)}"
  by(insert Rep_wt_subst_atomic[of s "EVar (AVar a) tid"], auto)

lemma unpair_Rep_wt_subst_MVar [simp]:
  "unpair (Rep_wt_subst s (EVar (MVar n) tid))= 
   {Rep_wt_subst s (EVar (MVar n) tid)}"
  by(insert Rep_wt_subst_atomic[of s "EVar (MVar n) tid"], auto)

declare Rep_wt_subst_noteq_simps[THEN neq_commute[THEN iffD1], iff]


lemma Rep_wt_subst_reorient_Lit [iff]:
  "(Lit l = Rep_wt_subst s l') = (Rep_wt_subst s l' = Lit l)"
  by(auto)

lemma pairParts_Rep_wt_subst_AVar [simp]:
  "pairParts (Rep_wt_subst s (EVar (AVar a) tid))= 
   {Rep_wt_subst s (EVar (AVar a) tid)}"
  by(insert Rep_wt_subst_atomic[of s "EVar (AVar a) tid"], auto)

lemma pairParts_Rep_wt_subst_MVar [simp]:
  "pairParts (Rep_wt_subst s (EVar (MVar n) tid))= 
   {Rep_wt_subst s (EVar (MVar n) tid)}"
  by(insert Rep_wt_subst_atomic[of s "EVar (MVar n) tid"], auto)


end