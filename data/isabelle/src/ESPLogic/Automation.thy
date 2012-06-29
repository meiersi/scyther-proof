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
uses
  espl_definitions
  espl_methods
begin

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


subsection{* Testing the Infrastructure *}


(*
text{*
  Commented out because new ISAR syntax comes only active after
  the theory file that defines them.
*}

role C
where "C =
  [ Send ''1'' ( PEnc ( sN ''k'' ) ( sPK ''S'' ) )
  , Recv ''2'' ( PHash ( sN ''k'' ) )
  , Note ''3'' SessKey (sN ''k'')
  ]"

role S
where "S =
  [ Recv ''1'' ( PEnc ( sMV ''k'' ) ( sPK ''S'' ) )
  , Send ''2'' ( PHash ( sMV ''k'' ) )
  ]"

protocol CR
where "CR = { C, S }"

locale restricted_CR_state = CR_state

type_invariant auto_msc_typing for CR
where "auto_msc_typing = mk_typing
  [ ((S, ''k''), (SumT (KnownT S_1) (NonceT C ''k'')))
  ]"


lemma additional_reveal_order:
  assumes facts:
    "predOrd t (LKR a) c"
  shows 
    "a \<in> lkreveals t \<and> predOrd t (LKR a) c"
using facts
by(auto intro: event_predOrdI)

sublocale CR_state < auto_msc_typing_state
proof -
  have "(t,r,s) : approx auto_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF auto_msc_typing.monoTyp, completeness_cases_rule])
    case (S_1_k t r s tid0) note facts = this
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc ( s(MV ''k'' tid0) ) ( PK ( s(AV ''S'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits) | (fastsimp intro: event_predOrdI split: if_splits))+)?
  qed
  thus "auto_msc_typing_state t r s" by unfold_locales auto
qed

lemma (in restricted_CR_state) C_k_order_raw:
   assumes facts:
     "roleMap r tid0 = Some C"
   shows
     "LN ''k'' tid0 \<in> knows t \<longrightarrow>
     (LKR (s(AV ''S'' tid0))) \<prec> (Ln (LN ''k'' tid0)) \<or> 
     (St (tid0, C_3) \<prec> (Ln (LN ''k'' tid0)))" 
     (is "?knows \<longrightarrow> ?order")
proof
  assume "?knows"
  thus "?order" using facts
  proof (sources "LN ''k'' tid0")
    case C_1_k
    thus ?thesis
      by (sources "SK (s (AV ''S'' tid0))")  (fastsimp intro: event_predOrdI)+
  qed auto
qed

(*
lemmas (in restricted_CR_state) C_k_order = C_k_order_raw[rule_format, THEN additional_reveal_order]
*)

lemma (in restricted_CR_state) C_k_secrecy:
  assumes facts:
    "roleMap r tid0 = Some C"
    "s(AV ''S'' tid0) ~: lkreveals t"
    "(tid0, C_3) \<notin> steps t"
    "LN ''k'' tid0 : knows t"
  shows "False"
using facts 
by(fastsimp dest: C_k_order_raw[rule_format] 
           intro: event_predOrdI)


*)


(*
text{*
  Commented out because new ISAR syntax comes only active after
  the theory file that defines them.
*}

text{* Testing the role definition command *}
role I
where "I \<equiv> 
  [ Send ''0'' (PEnc \<langle>sLC ''0'', sAV ''I'', sN ''ni''\<rangle> (sPK ''R''))
  , Recv ''1'' (PEnc \<langle>sLC ''1'', sAV ''R'', sN ''ni'', sMV ''nr''\<rangle> (sPK ''I''))
  , Send ''2'' (PEnc \<langle>sLC ''2'', sMV ''nr''\<rangle> (sPK ''R''))
  ]"

text{* A few of the proven theorems: *}
thm I.weakly_atomic_convs
thm I_def
thm I.unfold
thm I.wf_role
thm I.distinct_steps
thm I.in_set_conv
thm I.zip_conv
thm I.prefixClose_convs

thm I_1_def
thm I_1.unfold
thm I_1_pt_def
thm I_1.inst_conv
thm I_1.sendStep_conv
thm I_1.stepPat_conv
thm I_1.FV_conv
thm I_1.FMV_conv

text{* 
  Note that you should not need to use these theorems manually as the 
  simplifier and the classical reasoner are already setup such that
  they are used when appropriate.

  The general design idea behind the rules is such that wherever possible
  constants are not unfolded, as this simplifies proof states.
*}

text{* An additional role for testing purposes. *}
role R
where "R \<equiv>
  [ Recv ''0'' (PEnc \<langle>sLC ''0'', sLAV ''I'', sLMV ''ni''\<rangle> (sPK ''R''))
  , Send ''1'' (PEnc \<langle>sLC ''1'', sLAV ''R'', sLMV ''ni'', sLN ''nr''\<rangle> (sPK ''I''))
  , Recv ''2'' (PEnc \<langle>sLC ''2'', sLN ''nr''\<rangle> (sPK ''R''))
  ]"

thm R.weakly_atomic_convs

protocol nsl
where "nsl = {I, R}"

text{* Testing the protocol definition command; the generated theorems: *}
thm nsl_def
thm nsl.unfold
thm nsl.wf_proto
thm nsl.distinct_roles
thm nsl.in_set_conv

type_invariant typed_nsl for nsl
where "typed_nsl = mk_typing
   [ ((R, ''ni''), (SumT (KnownT R_0) (NonceT I ''ni'')))
   , ((I, ''nr''), (SumT (KnownT I_1) (NonceT R ''nr'')))
   ]"


sublocale nsl_state \<subseteq> typed_nsl_state
proof -
  have "(t,r,s) \<in> approx typed_nsl"
  proof(cases rule: reachable_in_approxI_ext
                    [OF typed_nsl.monoTyp, completeness_cases_rule])
    case (I_1_nr t r s i)
    then interpret state: typed_nsl_state t r s
      by unfold_locales auto
    show ?case using I_1_nr
    proof(sources "inst s i I_1_pt")
    qed (fastsimp intro: event_predOrdI split: if_splits)+
  next
    case (R_0_ni t r s i)
    then interpret state: typed_nsl_state t r s
      by unfold_locales auto
    show ?case using R_0_ni
    proof(sources "inst s i R_0_pt")
    qed (fastsimp intro: event_predOrdI split: if_splits)+
  qed
  thus "typed_nsl_state t r s" by unfold_locales auto
qed

context nsl_state begin
  lemma longterm_private_key_secrecy:
    assumes facts:
      "SK m : knows t"
      "m ~: Compromised"
    shows "False"
  using facts by (sources "SK m")

  lemma longterm_shared_key_secrecy:
    assumes facts:
      "K m1 m2 : knows t"
      "m1 ~: Compromised"
      "m2 ~: Compromised"
    shows "False"
  using facts by (sources "K m1 m2")

  lemmas ltk_secrecy =
    longterm_shared_key_secrecy
    longterm_shared_key_secrecy[OF in_knows_predOrd1]
    longterm_private_key_secrecy
    longterm_private_key_secrecy[OF in_knows_predOrd1]
end

lemma (in nsl_state) I_ni_secrecy:
  assumes facts:
    "roleMap r i = Some I"
    "LN ''ni'' i \<in> knows t"
    "s (AV ''I'' i) \<notin> lkreveals t"
    "s (AV ''R'' i) \<notin> lkreveals t"   
  shows "False"
using facts proof(sources " LN ''ni'' tid0 ")
  case I_0_ni thus ?thesis by (fastsimp dest!: ltk_secrecy)
next
  case (R_1_ni tid1) thus ?thesis 
  proof(sources "inst s tid1 R_0_pt")
    case I_0_enc thus ?thesis 
      by (fastsimp dest!: ltk_secrecy)
  qed (insert facts, (((clarsimp, order?) | order))+)?
qed


*)


end
