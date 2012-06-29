theory Subst
imports ExecMessage
begin


section{* Substitutions *}

definition varsOnly :: "(execlit \<Rightarrow> execmsg) \<Rightarrow> bool"
where "varsOnly s \<equiv> \<forall> l. s l \<noteq> Lit l \<longrightarrow> (\<exists> varid i. l = EVar varid i)"

definition groundSubst :: "(execlit \<Rightarrow> execmsg) \<Rightarrow> bool"
where "groundSubst s \<equiv> \<forall> l. s l \<noteq> Lit l \<longrightarrow> ground (s l)"

typedef subst = "\<lambda> s. s \<in> varsOnly \<and> s \<in> groundSubst"
  by(auto simp: mem_def varsOnly_def groundSubst_def ran_def)

notation (xsymbols) Rep_subst ("_(_)" [1000, 0] 58)

text{* 
We additionally support ASCII notation for applying
a substitution in order to make the certificate output of
Scyther readable in a text editor without the support for
Isabelle's math symbols.
*}
notation            Rep_subst ("_'(|_|')" [1000, 0] 58)


fun applyS :: "subst \<Rightarrow> execmsg \<Rightarrow> execmsg"
where
  "applyS s (Lit l)   = Rep_subst s l"
| "applyS s (Tup x y) = Tup  (applyS s x) (applyS s y)"
| "applyS s (Enc m k) = Enc  (applyS s m) (applyS s k)"
| "applyS s (Hash m)  = Hash (applyS s m)"
| "applyS s (K a b)   = K    (applyS s a) (applyS s b)"
| "applyS s (PK a)    = PK   (applyS s a)"
| "applyS s (SK a)    = SK   (applyS s a)"


definition emptyS :: "subst"
where "emptyS \<equiv> Abs_subst Lit"

definition extendS :: "subst \<Rightarrow> subst \<Rightarrow> subst"
where "extendS s1 s2 \<equiv> Abs_subst (applyS s2 o Rep_subst s1)"

definition domS :: "subst \<Rightarrow> execlit set"
where "domS s \<equiv> { l. Rep_subst s l \<noteq> Lit l }"

definition ranS :: "subst \<Rightarrow> execmsg set"
where "ranS s \<equiv> { Rep_subst s l | l. Rep_subst s l \<noteq> Lit l }"

fun inst :: "subst \<Rightarrow> i \<Rightarrow> pattern \<Rightarrow> execmsg"
where
  "inst s i (PConst c)   = Lit (EConst c)"
| "inst s i (PFresh n)   = Lit (ENonce  n i)"
| "inst s i (PVar   v)   = s(EVar v i)"
| "inst s i (PTup x y)   = Tup (inst s i x) (inst s i y)"
| "inst s i (PEnc m k)   = Enc (inst s i m) (inst s i k)"
| "inst s i (PSign m k)  = 
     Tup (inst s i m) 
         (Enc  (inst s i m) (inv (inst s i k)))"
| "inst s i (PHash m)    = Hash (inst s i m)"
| "inst s i (PSymK a b)  = K    (inst s i a) (inst s i b)"
| "inst s i (PAsymPK a)  = PK   (inst s i a)"
| "inst s i (PAsymSK a)  = SK   (inst s i a)"



subsection{* Properties *}


lemma notin_domS_conv [iff]:
  "(x \<notin> domS s) = (Rep_subst s x = Lit x)"
  by(auto simp: domS_def)

lemma applyS_in_domS_conv []:
  "(x \<in> domS s) = (Rep_subst s x \<noteq> Lit x)"
 by(auto simp: domS_def)


subsubsection{* Substitutions *}

text{* TODO: Make order in this bunch of rules. *}

lemma Rep_subst_varsOnly [simp,intro!]: "varsOnly (Rep_subst s)"
  by(insert Rep_subst, simp add: subst_def mem_def)

lemma Rep_subst_groundSubst [simp,intro!]: "groundSubst (Rep_subst s)"
  by(insert Rep_subst, simp add: subst_def mem_def)

lemma Rep_subst_ground [simp]: 
  "Rep_subst s l \<noteq> Lit l \<Longrightarrow> ground (Rep_subst s l)"
  apply(insert Rep_subst_groundSubst[of s])
  apply(auto simp: groundSubst_def)
  done

lemma Rep_subst_simps [simp]: 
  "Rep_subst s (EConst c)     = Lit (EConst c)"
  "Rep_subst s (EHonest a)    = Lit (EHonest a)"
  "Rep_subst s (ENonce n i) = Lit (ENonce n i)"
  "Rep_subst s (Eve a)        = Lit (Eve a)"
  "Rep_subst s (EveNonce n)   = Lit (EveNonce n)"
  by(insert Rep_subst_varsOnly[of s], auto simp: varsOnly_def)

lemma applyS_ground_msg [simp]: "ground m \<Longrightarrow> applyS s m = m"
  by(induct m, case_tac lit, auto)

lemma applyS_idem [simp]: "applyS s (applyS s m) = applyS s m"
  apply(induct m, case_tac lit, simp_all)
  apply(case_tac "Rep_subst s (EVar varid nat) = Lit (EVar varid nat)")
  apply(auto)
  done

lemma applyS_Rep_subst_idem [simp]:
  "applyS s (Rep_subst s l) = Rep_subst s l"
  apply(rule_tac s="applyS s (Lit l)" in subst)
  apply(simp, rule applyS_idem)
  done


lemma Rep_subst_varsOnlyE:
  "\<lbrakk> Rep_subst s l \<noteq> Lit l; \<And> v i. l = EVar v i \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply(insert Rep_subst_varsOnly[of s])
  unfolding varsOnly_def
  apply(drule_tac x=l in spec)
  apply(auto)
  done

lemma varsOnlyI [intro!]: 
  "\<lbrakk> \<And> l. s l \<noteq> Lit l \<Longrightarrow> \<exists> v i. l = EVar v i \<rbrakk> \<Longrightarrow> varsOnly s"
  by(auto simp: varsOnly_def)

lemma groundSubstI [intro!]:
  "\<lbrakk> \<And> l. s l \<noteq> Lit l \<Longrightarrow> ground (s l) \<rbrakk> \<Longrightarrow> groundSubst s"
  by(auto simp: groundSubst_def)

lemma substI [intro!]:
  "\<lbrakk> groundSubst s; varsOnly s \<rbrakk> \<Longrightarrow> s \<in> subst"
  by(auto simp: subst_def mem_def)

lemma Abs_subst_extend_wts_inverse [simp]:
  "Rep_subst (Abs_subst (applyS s' o Rep_subst s)) = applyS s' o Rep_subst s"
  apply(subst Abs_subst_inverse, auto)
  apply(case_tac "Rep_subst s l = Lit l", simp, simp)
  apply(case_tac "Rep_subst s l = Lit l")
  apply(auto elim!: Rep_subst_varsOnlyE)
  done

lemma extendS_conv_applyS [simp]: 
  "applyS (extendS s s') m = applyS s' (applyS s m)"
  by(induct m, induct_tac lit, auto simp: extendS_def)


lemma Abs_subst_emptyS_inverse [simp]: 
  "Rep_subst (Abs_subst Lit) = Lit"
  by(subst Abs_subst_inverse, auto)

lemma domS_emptyS [simp]: "domS emptyS = {}"
  by(auto simp: domS_def emptyS_def)

lemma domS_extendS [simp]: "domS (extendS s s') = domS s \<union> domS s'"
  apply(auto simp: domS_def extendS_def)
  apply(case_tac "Rep_subst s x = Lit x")
  apply(auto elim!: Rep_subst_varsOnlyE)
  done

lemma applyS_emptyS [simp]: "applyS emptyS m = m"
  by(induct m, auto simp: emptyS_def)

lemma ground_inst_conv_FV: 
  "ground (inst s i pt) = (\<forall> v \<in> FV pt. EVar v i \<in> domS s)"
  apply(induct pt)
  apply(simp_all)
  apply(case_tac "s(EVar varid i) = Lit (EVar varid i)")
  apply(auto simp: domS_def)
  done

lemma applyS_subdomain: 
  "domS s' \<subseteq> domS s \<Longrightarrow> applyS s' (applyS s m) = applyS s m"
  apply(induct m rule: applyS.induct, simp_all)
  apply(case_tac "l \<in> domS s")
  apply(auto simp: domS_def)
  done

lemma Rep_subst_reorient [iff]:
  "(Lit l = Rep_subst s l') = (Rep_subst s l' = Lit l)"
  "(Lit l \<noteq> Rep_subst s l') = (Rep_subst s l' \<noteq> Lit l)"
  "(Tup x y = Rep_subst s l) = (Rep_subst s l = Tup x y)"
  "(Enc m k = Rep_subst s l) = (Rep_subst s l = Enc m k)"
  "(Hash m = Rep_subst s l) = (Rep_subst s l = Hash m)"
  "(K a b = Rep_subst s l) = (Rep_subst s l = K a b)"
  "(PK a = Rep_subst s l) = (Rep_subst s l = PK a)"
  "(SK a = Rep_subst s l) = (Rep_subst s l = SK a)"
  by auto

lemma sort_Rep_subst_eqs [simp]: 
  "(Rep_subst s x = Rep_subst s y) = (Rep_subst s y = Rep_subst s x)"
  by auto

lemma Rep_subst_emptyS [simp]: "Rep_subst emptyS = Lit"
  by(rule ext, auto simp: emptyS_def)

lemma extendS_empty [simp]: 
  "extendS s emptyS = s"
  "extendS emptyS s = s"
  by(auto simp: extendS_def Rep_subst_inverse o_def)

lemma Rep_subst_extendS_conv: 
  "Rep_subst (extendS s s') m = applyS s' (Rep_subst s m)"
  by(simp add: extendS_def)

lemma applyS_Rep_subst_domS [simp]:
  "l \<in> domS s \<Longrightarrow> applyS s' (Rep_subst s l) = Rep_subst s l"
  by(simp add: applyS_in_domS_conv)

lemma extendS_assoc [simp]: 
  "extendS (extendS s s') s'' = extendS s (extendS s' s'')"
  apply(simp add: extendS_def)
  apply(subst Abs_subst_inject)
  apply(safe)
  apply(case_tac "l \<in> domS s", simp)
  apply(case_tac "l \<in> domS s'", simp)
  apply(case_tac "l \<in> domS s''", simp)
  apply(simp)
  apply(case_tac "l \<in> domS s", simp, erule Rep_subst_varsOnlyE, simp)
  apply(case_tac "l \<in> domS s'", simp, erule Rep_subst_varsOnlyE, simp)
  apply(case_tac "l \<in> domS s''", simp, erule Rep_subst_varsOnlyE, simp)
  apply(simp)
  apply(case_tac "l \<in> domS s", simp)
  apply(case_tac "l \<in> domS s'", simp)
  apply(case_tac "l \<in> domS s''", simp)
  apply(simp)
  apply(case_tac "l \<in> domS s", simp, erule Rep_subst_varsOnlyE, simp)
  apply(case_tac "l \<in> domS s'", simp, erule Rep_subst_varsOnlyE, simp)
  apply(case_tac "l \<in> domS s''", simp, erule Rep_subst_varsOnlyE, simp)
  apply(simp)
  apply(rule ext)
  apply(case_tac "x \<in> domS s")
  apply(simp+)
  done

lemma ranSD: "\<lbrakk> ranS s \<subseteq> X; l \<in> domS s \<rbrakk> \<Longrightarrow> Rep_subst s l \<in> X"
  by(auto simp: ranS_def domS_def)


lemma inst_extendS_conv_applyS [simp]:
  "ground (inst s i pt) \<Longrightarrow>
   inst (extendS s s') i pt = inst s i pt"
  by(induct pt, auto simp: Rep_subst_extendS_conv)

end