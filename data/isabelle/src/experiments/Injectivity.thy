theory Injectivity
imports Main
begin

lemma test:
  assumes auth_eq: "\<And> r x y. auth x r = auth y r \<Longrightarrow> x = y"
  and     auth_ex: "\<And> i. i \<in> I \<Longrightarrow> \<exists> r. auth i r"
  shows "\<exists> f. inj_on f I \<and> (\<forall> i \<in> I. auth i (f i))"
  apply(rule_tac x="\<lambda> i. SOME r. auth i r" in exI)
  apply(safe)
  apply(simp add: inj_on_def)
  apply(safe)
  apply(rule_tac r="(SOME r. auth x r)" in auth_eq)
  apply(drule auth_ex)+
  apply(clarify)
  apply(rule iffI)
  apply(simp)
  apply(rule someI, assumption)+
  apply(drule auth_ex)+
  apply(clarify)
  apply(rule someI, assumption)+
  done

lemma iagree_to_niagree:
  assumes niagree: "\<forall> i. prem i \<longrightarrow> (\<exists> j. conc i j)"
  and     conc_inj: "\<forall> i1 i2 j. conc i1 j = conc i2 j \<longrightarrow> i1 = i2"
  shows "let prems = prem; 
             concs = conc
         in \<exists>f. inj_on f prems \<and> (\<forall>i. prems i \<longrightarrow> concs i (f i))"
proof -
  have "\<exists> f. inj_on f prem \<and> (\<forall> i \<in> prem. conc i (f i))"
    by(rule test, auto simp: conc_inj[rule_format] niagree[rule_format] mem_def)
  thus ?thesis
    by(force simp: Let_def mem_def)
qed

definition smaller (* :: 'a set \<Rightarrow> 'a set \<Rightarrow> bool" *)
where "smaller A B = (\<exists> f. inj_on f A \<and> (\<forall> x \<in> A. f(x) \<in> B \<and> (f(x) \<in> A \<longrightarrow>  x \<in> B)))"

lemma smaller_refl [iff]: "smaller A A"
  apply(clarsimp simp: smaller_def inj_on_def)
  apply(auto)
  done

lemma smaller_mono: "\<lbrakk> smaller A B; B \<subseteq> C \<rbrakk> \<Longrightarrow> smaller A C"
  apply(clarsimp simp: smaller_def)
  apply(auto)
  done

lemma smaller_compl: "smaller (- A) (- B) \<Longrightarrow> smaller B A"
  apply(clarsimp simp: smaller_def)
  apply(rule_tac x="\<lambda> x. if x \<in> A then x else f(x)" in exI)
  apply(auto)
  apply(auto simp: inj_on_def)
  done
  
lemma smaller_image: "inj_on f A \<Longrightarrow> smaller A (f ` A)"
  apply(clarsimp simp: smaller_def image_def)
  apply(rule_tac x="f" in exI)
  apply(safe)
  apply(force)
  apply(erule contrapos_pp)
  apply(clarsimp simp: inj_on_def)
(* hmm that doesn't really work. let's call it a day and use the restricted version of
   niagree_to_iagree, which is actually just fine in practice.
*)

  apply(
  apply(auto)
  apply(rule_tac x="inv_into A f x" in bexI)
  apply(rule sym)
  apply(rule f_inv_into_f)
  apply(simp add: image_def)
  apply(subst f_inv_into_f)
  apply(force)
  apply(auto simp: image_def inj_on_def)
  done

lemma inj_on_extend: "inj_on (f :: 'a \<Rightarrow> 'a) A \<Longrightarrow> \<exists> g. inj g \<and> (\<forall> x \<in> A. g x = f x)"

lemma blah: "SOME f. False"
  apply(rule someI) back
ML_prf{*
  case @{term X} of
    Free (_,ty) => Term.dest_Type ty |> snd |> hd |> dest_Type
*}
ML_prf{* dest_fun *}
  apply(rule someI)
thm someI

lemma test3:
  "(\<exists> f. inj_on f A \<and> (\<forall> a \<in> A. P a (f a))) \<Longrightarrow>
   (\<exists> f. X f \<and> (\<forall> a \<in> A. P a (f a)))"

apply(clarsimp)
apply(rule_tac x="(SOME g. X g)" in exI)
thm someI
apply(rule conjI)
apply(rule someI) back
apply(assumption)

apply(rule_tac x="(SOME g. inj g \<and> (\<forall> a \<in> A. g a = f a))" in exI)

apply(clarsimp)
apply(clarsimp simp: inj_on_def)

apply(rule_tac x="\<lambda> x. if x \<in> A then f x else
                       (SOME y. h


lemma test2:
  assumes auth_eq: "\<And> r x y. auth r x = auth r y \<Longrightarrow> x = y"
  and     inj_ex: "\<exists> f. inj_on f I \<and> (\<forall> i \<in> I. auth (f i) i)"
  and     in_I: "i \<in> I"
  shows "\<exists> r. auth r i"
using inj_ex in_I
apply(clarsimp simp: inj_on_def)
apply(rule_tac x="f i" in exI)
apply(fast)
done

lemma test:
  " (\<forall> i \<in> I. 
              (\<exists> r. auth i r \<and> (\<forall> j \<in> I. auth j r \<longrightarrow> j = i)))
   \<Longrightarrow> (\<exists> f. inj_on f I \<and> (\<forall> i \<in> I. auth i (f i))) "
  apply(rule_tac x="\<lambda> i. THE r. auth i r" in exI)
  apply(simp add: inj_on_def)
  apply(rule conjI)
  apply(clarsimp) prefer 2
  apply(clarsimp)
  apply(drule bspec, assumption)
  apply(clarify)
  apply(rule theI, assumption)
  apply(drule bspec, assumption)
  apply(frule bspec, assumption)
  apply(drule bspec, assumption) back
  apply(clarify)
  apply(force)