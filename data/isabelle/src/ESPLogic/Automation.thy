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
theory Automation
imports
  Syntax
  InferenceRules
  WeakTyping
keywords "role" "protocol" "type_invariant" :: thy_decl
  and "prefix_close" :: prf_decl
begin

ML_file "espl_definitions.ML"
ML_file "espl_methods.ML"

section{* Automation *}

subsection{* Setup of ISAR commands *}

setup{* ESPL_Definitions.KnowsCasesCache.setup *}

method_setup sources =
  {* ESPL_Methods.sourcesP >> 
       (fn ((minimal, msg_t), opt_rule) => fn ctxt =>
         METHOD_CASES (fn facts =>
           Seq.DETERM (HEADGOAL (
            ESPL_Methods.sources_tac ctxt 
             minimal msg_t opt_rule facts))))
  *}
  "enumerate the possible sources of a term known to the intruder"

attribute_setup completeness_cases_rule = 
  {* Scan.succeed (Thm.rule_attribute 
       ESPL_Methods.completeness_cases_attrib) *}
  "conversion to a completeness cases rule"

attribute_setup type_elim_rule = 
  {* Scan.succeed (Thm.declaration_attribute 
       (fn th => fn ctxt =>
          if member Thm.eq_thm (ESPL_Definitions.TypeElimRulesData.get ctxt) th
          then ctxt
          else ESPL_Definitions.TypeElimRulesData.map (fn ths => th::ths) ctxt)) *}
  "marks a theorem as a rule that should be used for type information eliminitation"

declare (in typed_state) decrChain_SumT_KnownTE[type_elim_rule]
declare (in typed_state) decrChain_KnownTE[type_elim_rule]
declare (in typed_state) decrChain_AgentE[type_elim_rule]



subsection{* Setting up Isabelle built-in Tools *}

text{*
  The unification based on ordered rewritting is somewhat fragile.
  We have to see what equations we still have to add to avoid
  looping in the simplifier.
*}
lemma tid_eq_commute [simp]: "((i1::tid) = i2) = (i2 = i1)"
  by (rule eq_commute)

lemma all_imp_insert [simp]: 
  "(\<forall> a. (a = x \<longrightarrow> P a) \<and> Q a) = (P x \<and> (\<forall> a. Q a))"
  by(auto)

lemma all2_imp_insert [simp]: 
  "(\<forall> a b. ((a = x \<and> b = y) \<longrightarrow> P a b) \<and> Q a b) = (P x y \<and> (\<forall> a b. Q a b))"
  by fast


lemma ball_Un_pairParts [iff]:
  "(\<forall> im \<in> pairParts x \<union> pairParts y. P im) =
   ((\<forall> im \<in> pairParts x. P im) \<and> (\<forall> im \<in> pairParts y. P im))"
  by fast

lemma ball_pairParts_Rep_subst_Var [dest!]:
  "\<forall> im \<in> pairParts (Rep_subst s (EVar v i)). P im \<Longrightarrow>
   P (Rep_subst s (EVar v i))"
  by fast

lemma (in reachable_state) decrChain_Rep_subst_AVar [iff]:
  "from \<noteq> {} \<Longrightarrow> 
  \<not> decrChain path t from (s (AVar v, i)) m"
  using inst_AVar_cases[of v i] 
  by (auto simp: Agent_def)

lemma (in reachable_state) remove_trivial_predOrd [dest!]:
  "Ln (Lit (EConst c)) \<prec> y \<Longrightarrow> True"
  "Ln (s (AVar v, i)) \<prec> y \<Longrightarrow> True"
  "Ln (Lit (EAgent a)) \<prec> y \<Longrightarrow> True"
  "Ln (Lit (EveNonce n)) \<prec> y \<Longrightarrow> True"
  "Ln (PK m) \<prec> y \<Longrightarrow> True"
  by auto

(* FIXME: Remove this lemma, automation should cope otherwise *)
lemma (in reachable_state) extract_knows_hyps:
  "Ln m \<prec> St e \<Longrightarrow> m \<in> knows t"
  "St e \<prec> Ln m \<Longrightarrow> m \<in> knows t"
  "LKR a \<prec> Ln m \<Longrightarrow> m \<in> knows t"
  "Ln m \<prec> LKR a \<Longrightarrow> m \<in> knows t"
  "Ln m \<prec> Ln m' \<Longrightarrow> m \<in> knows t \<and> m' \<in> knows t"
  by (auto intro: event_predOrdI)

declare (in reachable_state) conjE[OF split_before, elim!]
declare (in reachable_state) conjE[OF split_knows, elim!]

lemma (in reachable_state) reorient_store_eqs [iff]:
  "(Lit l' =  s l) = (s l = Lit l')"
  "(Lit l' \<noteq>  s l) = (s l \<noteq> Lit l')"
  "(Tup x y = s l) = (s l = Tup x y)"
  "(Enc m k = s l) = (s l = Enc m k)"
  "(Hash m = s l) = (s l = Hash m)"
  "(K a b = s l) = (s l = K a b)"
  "(PK a = s l) = (s l = PK a)"
  "(SK a = s l) = (s l = SK a)"
  by auto

lemma (in reachable_state) reorient_store_eq_store_fixed [simp]: 
  "(s (AV a i) = s (MV v j)) = (s (MV v j) = s (AV a i))"
  "(s (AV a i) = s (AV v j)) = (s (AV v j) = s (AV a i))"
  "(s (MV a i) = s (MV v j)) = (s (MV v j) = s (MV a i))"
  by auto

text{* Required by \verb|note_unified| *}
lemma (in reachable_state) reorient_store_eq_store: 
  "(s x = s y) = (s y = s x)"
  by auto

text{* Removes all impossible cases for lkreveals and LKR*}
lemma (in reachable_state) remove_predOrd_LKR [dest!]:
  "(LKR (Tup x y)) \<prec> e \<Longrightarrow> False"
  "e \<prec> (LKR (Tup x y)) \<Longrightarrow> False"
  "(LKR (Enc m k)) \<prec> e \<Longrightarrow> False"
  "e \<prec> (LKR (Enc m k)) \<Longrightarrow> False"
  "(LKR (Hash m)) \<prec> e \<Longrightarrow> False"
  "e \<prec> (LKR (Hash m)) \<Longrightarrow> False"
  "(LKR (K a b)) \<prec> e \<Longrightarrow> False"
  "e \<prec> (LKR (K a b)) \<Longrightarrow> False"
  "(LKR (SK a)) \<prec> e \<Longrightarrow> False"
  "e \<prec> (LKR (SK a)) \<Longrightarrow> False"  
  "(LKR (PK a)) \<prec> e \<Longrightarrow> False"
  "e \<prec> (LKR (PK a)) \<Longrightarrow> False"
  "(LKR (Lit (EConst i))) \<prec> e \<Longrightarrow> False"
  "e \<prec> (LKR (Lit (EConst i))) \<Longrightarrow> False"
  "(LKR (Lit (ENonce i j))) \<prec> e \<Longrightarrow> False"
  "e \<prec> (LKR (Lit (ENonce i j))) \<Longrightarrow> False"
    "(LKR (Lit (EveNonce i))) \<prec> e \<Longrightarrow> False"
  "e \<prec> (LKR (Lit (EveNonce i))) \<Longrightarrow> False"
by(auto dest: predOrd_LKR_agent1 predOrd_LKR_agent2)

end
