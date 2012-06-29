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

theory "CR_paper_acm"
imports
  "../ESPLogic"
begin

section{* CR Paper as testing ground for acm *}

subsection{* Protocol Specificiation *}

role C
where "C =
  [ 
    Note ''1'' State <| sN ''k'', sAV ''S'' |>
  , Send ''2'' ( PEnc ( sN ''k'' ) ( sPK ''S'' ) )
  , Note ''3'' State <| PHash ( sN ''k'' ), sAV ''S'' |>
  , Recv ''4'' ( PHash ( sN ''k'' ) )
  , Note ''5'' SessKey (sN ''k'')
  ]"

role S
where "S =
  [ Recv ''1'' ( PEnc ( sMV ''k'' ) ( sPK ''S'' ) )
  , Note ''2'' State <| sMV ''k'', sAV ''S'', PEnc ( sMV ''k'' ) ( sPK ''S'' ), PHash ( sMV ''k'' ) |>
  , Send ''3'' ( PHash ( sMV ''k'' ) )
  , Note ''4'' SessKey (sMV ''k'')
  ]"

protocol CR
where "CR = { C, S }"




(* TODO remove *)
declare (in CR_state) C_1_def[simp]
declare (in CR_state) C_3_def[simp]
declare (in CR_state) C_5_def[simp]
declare (in CR_state) S_2_def[simp]
declare (in CR_state) S_4_def[simp]



subsection {* Typing Definition *}
type_invariant auto_msc_typing for CR
where "auto_msc_typing = mk_typing
  [ ((S, ''k''), (SumT (KnownT S_1) (NonceT C ''k'')))
  ]"


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

subsection{* Partnering Definition *}

definition
  CR_trusted :: "partnering"
where
  "CR_trusted q = 
    Id \<union>
    mk_partnering C S {(sN  ''k'' ,sMV ''k'',S_1),
                       (sAV ''S'', sAV ''S'',S_1)} q \<union> 
    mk_partnering S C {(sMV ''k'', sN  ''k'', C_2),
                       (sAV ''S'', sAV ''S'', C_2)} q"

lemmas (in CR_state) CR_trusted_conv = 
  setEqImpTupleIn[OF CR_trusted_def, of _ _ "(t,r,s)", simplified]

lemmas (in CR_state) CR_trustedI[intro!] = CR_trusted_conv[THEN iffD2,simplified mk_partnering_conv,simplified]


subsection{* Adversary Compromise Model Definitions *}

definition (in CR_state) ADVprod :: "tid \<Rightarrow> state set"
where
  "ADVprod i = acm {LKRprotected i {AVar ''S''}}"

locale CR_state_ADVprod =  CR_state +
  fixes test :: tid
  assumes compromiseModel [simp,intro!]: "(t,r,s) \<in> ADVprod test"
begin
  lemmas allowed_reveals = acm_to_caps[OF compromiseModel[simplified ADVprod_def], simplified]
end



definition (in CR_state) ADVint :: "tid \<Rightarrow> state set"
where 
  "ADVint i = acm {LKRothers i}"

locale CR_state_ADVint =  CR_state +
  fixes test :: tid
  assumes compromiseModel [simp,intro!]: "(t,r,s) \<in> ADVint test"
begin
  lemmas allowed_reveals = acm_to_caps[OF compromiseModel[simplified ADVint_def], simplified]
end



definition (in CR_state) ADVsessKey :: "tid \<Rightarrow> state set"
where
"ADVsessKey i = acm {SkR i CR_trusted}"

locale CR_state_ADVsessKey =  CR_state +
  fixes test :: tid
  assumes compromiseModel [simp,intro!]: "(t,r,s) \<in> ADVsessKey test"
begin
  lemmas allowed_reveals = acm_to_caps[OF compromiseModel[simplified ADVsessKey_def], simplified]
end



definition (in CR_state) ADVstate :: "tid \<Rightarrow> state set"
where
"ADVstate i = acm {StR i CR_trusted}"

locale CR_state_ADVstate =  CR_state +
  fixes test :: tid
  assumes compromiseModel [simp,intro!]: "(t,r,s) \<in> ADVstate test"
begin
  lemmas allowed_reveals = acm_to_caps[OF compromiseModel[simplified ADVstate_def], simplified]
end


definition (in CR_state) ADVcaC :: "tid \<Rightarrow> state set"
where
"ADVcaC i = acm {LKRactor i (AVar ''C'')}"

locale CR_state_ADVcaC =  CR_state +
  fixes test :: tid
  assumes compromiseModel [simp,intro!]: "(t,r,s) \<in> ADVcaC test"
begin
  lemmas allowed_reveals = acm_to_caps[OF compromiseModel[simplified ADVcaC_def], simplified]
end



definition (in CR_state) ADVall :: "tid \<Rightarrow> state set"
where
"ADVall i = acm {
  LKRactor i (AVar ''C''), 
  SkR i CR_trusted, 
  StR i CR_trusted, 
  LKRactor i (AVar ''C'') }"

locale CR_state_ADVall =  CR_state +
  fixes test :: tid
  assumes compromiseModel [simp,intro!]: "(t,r,s) \<in> ADVall test"
begin
  lemmas allowed_reveals = acm_to_caps[OF compromiseModel[simplified ADVall_def], simplified]
end


section{* Security Proofs *}

subsection{* Origin Proofs *}
lemma (in CR_state) C_k_origin [rule_format]:
   assumes facts:
     "roleMap r test = Some C"
   shows
     "LN ''k'' test \<in> knows t \<longrightarrow>
     RLKR (s(AV ''S'' test)) \<in> reveals t\<or>
     (\<exists> j. (test,j) \<in> CR_trusted (t,r,s) \<and> RCompr SessKey j \<in> reveals t)  \<or>
     (\<exists> j. (test,j) \<in> CR_trusted (t,r,s) \<and> RCompr State j \<in> reveals t) "
       (is "?knows \<longrightarrow> ?origins")
proof
  assume "?knows"
  thus "?origins" using facts
  proof (sources "LN ''k'' test")
    case C_1_k
    thus ?thesis
      by(auto intro: compr_predOrdI)  
  next
    case C_2_k
    thus ?thesis
      by (sources "SK (s (AV ''S'' test))")  (auto intro: compr_predOrdI)
  next 
    case (S_2_k tid1')
    thus ?thesis
    proof(sources "Enc (LN ''k'' test) (PK (s (AV ''S'' tid1')))")
      case C_2_enc
      thus ?thesis
        by  (auto intro: compr_predOrdI)
    qed
  next
    case (S_4_k tid')
    thus ?thesis
    proof(sources "Enc (LN ''k'' test) (PK (s (AV ''S'' tid')))")
      case C_2_enc
      thus ?thesis 
        by (fastsimp dest: compr_predOrdI)
    qed
  next
    case C_5_k
    thus ?thesis
      by (fastsimp dest: compr_predOrdI)
  qed
qed


subsection{* Secrecy Proofs *}

lemma (in CR_state_ADVprod) C_k_secrecy_protected:
  assumes facts:
    "roleMap r test = Some C"
    "LN ''k'' test \<in> knows t"
  shows
    False
using facts
by(fastsimp dest: C_k_origin allowed_reveals)

lemma (in CR_state_ADVint) C_k_secrecy_others:
  assumes facts:
    "roleMap r test = Some C"
    "LN ''k'' test \<in> knows t"
  shows
    False
using facts
apply -
apply(frule C_k_origin, assumption)
by(auto dest: allowed_reveals)


lemma (in CR_state_ADVsessKey) C_k_secrecy_sessKey:
  assumes facts:
    "roleMap r test = Some C"
    "LN ''k'' test \<in> knows t"
  shows
    False
using facts
apply -
apply(frule C_k_origin, assumption)
by(auto dest: allowed_reveals)


lemma (in CR_state_ADVstate) C_k_secrecy_state:
  assumes facts:
    "roleMap r test = Some C"
    "LN ''k'' test \<in> knows t"
  shows
    False
using facts
apply -
apply(frule C_k_origin, assumption)
by(auto dest: allowed_reveals)


lemma (in CR_state_ADVcaC) C_k_secrecy_actor:
  assumes facts:
    "roleMap r test = Some C"
    "LN ''k'' test \<in> knows t"
  shows
    False
using facts
apply -
apply(frule C_k_origin, assumption)
by(auto dest: allowed_reveals)

lemma (in CR_state_ADVall) C_k_secrecy_all:
  assumes facts:
    "roleMap r test = Some C"
    "LN ''k'' test \<in> knows t"
  shows
    False
using facts
apply -
apply(frule C_k_origin, assumption)
by(auto dest: allowed_reveals)


subsection{* Authentication Proofs *}

lemma (in CR_state_ADVprod) C_ni_synch_protected:
  assumes facts:
    "roleMap r test = Some C"
    "( test, C_4 ) \<in> steps t"
  shows
    "(\<exists>  tid2.
        roleMap r tid2 = Some S \<and>
        s(AV ''S'' test) = s(AV ''S'' tid2) \<and>
        LN ''k'' test = s(MV ''k'' tid2) \<and>
        St( test, C_2 ) \<prec> St( tid2, S_1 ) \<and>
        St( tid2, S_1 ) \<prec> St( tid2, S_3 ) \<and>
        St( tid2, S_3 ) \<prec> St( test, C_4 ))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis
  proof(sources "Hash ( LN ''k'' test )")
    case fake
    thus ?thesis 
      by(fastsimp dest: C_k_secrecy_protected intro: event_predOrdI)
  next
    case (S_3_hash tid2)
    thus ?thesis
    proof(sources "Enc (LN ''k'' test) (PK (s (AV ''S'' tid2)))")
      case C_2_enc
      thus ?thesis by force
    next
      case fake
      thus ?thesis
        by (fastsimp dest: C_k_secrecy_protected intro: event_predOrdI)
    qed
  next
    case C_3_hash
    thus ?thesis
      by(fastsimp dest: compr_predOrdI allowed_reveals)
  next
    case (S_2_hash tid2)
    thus ?thesis
    proof(sources "Enc (LN ''k'' test) (PK (s (AV ''S'' tid2)))")
      case fake
      thus ?thesis
        by (fastsimp dest: C_k_secrecy_protected intro: event_predOrdI)
    next
      case C_2_enc
      thus ?thesis
        by(fastsimp dest: compr_predOrdI allowed_reveals)
    qed
  qed
qed


lemma (in CR_state_ADVint) C_ni_synch_others:
  assumes facts:
    "roleMap r test = Some C"
    "( test, C_4 ) \<in> steps t"
  shows
    "(\<exists> tid2.
        roleMap r tid2 = Some S \<and>
        s(AV ''S'' test) = s(AV ''S'' tid2) \<and>
        LN ''k'' test = s(MV ''k'' tid2) \<and>
        St( test, C_2 ) \<prec> St( tid2, S_1 ) \<and>
        St( tid2, S_1 ) \<prec> St( tid2, S_3 ) \<and>
        St( tid2, S_3 ) \<prec> St( test, C_4 ))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis
  proof(sources "Hash ( LN ''k'' test )")
    case fake
    thus ?thesis 
      by(fastsimp dest: C_k_secrecy_others intro: event_predOrdI)
  next
    case (S_3_hash tid2)
    thus ?thesis
    proof(sources "Enc (LN ''k'' test) (PK (s (AV ''S'' tid2)))")
      case C_2_enc
      thus ?thesis by force
    next
      case fake
      thus ?thesis
        by (fastsimp dest: C_k_secrecy_others intro: event_predOrdI)
    qed
  next
    case C_3_hash
    thus ?thesis
      by(fastsimp dest: compr_predOrdI allowed_reveals)
  next
    case (S_2_hash tid2)
    thus ?thesis
    proof(sources "Enc (LN ''k'' test) (PK (s (AV ''S'' tid2)))")
      case fake
      thus ?thesis
        by (fastsimp dest: C_k_secrecy_others intro: event_predOrdI)
    next
      case C_2_enc
      thus ?thesis
        by(fastsimp dest: compr_predOrdI allowed_reveals)
    qed
  qed
qed

lemma (in CR_state_ADVsessKey) C_ni_synch_sessKey:
  assumes facts:
    "roleMap r test = Some C"
    "( test, C_4 ) \<in> steps t"
  shows
    "(\<exists> tid2.
        roleMap r tid2 = Some S \<and>
        s(AV ''S'' test) = s(AV ''S'' tid2) \<and>
        LN ''k'' test = s(MV ''k'' tid2) \<and>
        St( test, C_2 ) \<prec> St( tid2, S_1 ) \<and>
        St( tid2, S_1 ) \<prec> St( tid2, S_3 ) \<and>
        St( tid2, S_3 ) \<prec> St( test, C_4 ))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis
  proof(sources "Hash ( LN ''k'' test )")
    case fake
    thus ?thesis 
      by(fastsimp dest: C_k_secrecy_sessKey intro: event_predOrdI)
  next
    case (S_3_hash tid2)
    thus ?thesis
    proof(sources "Enc (LN ''k'' test) (PK (s (AV ''S'' tid2)))")
      case C_2_enc
      thus ?thesis by force
    next
      case fake
      thus ?thesis
        by (fastsimp dest: C_k_secrecy_sessKey intro: event_predOrdI)
    qed
  next
    case C_3_hash
    thus ?thesis
      by(fastsimp dest: compr_predOrdI allowed_reveals)
  next
    case (S_2_hash tid2)
    thus ?thesis
    proof(sources "Enc (LN ''k'' test) (PK (s (AV ''S'' tid2)))")
      case fake
      thus ?thesis
        by (fastsimp dest: C_k_secrecy_sessKey intro: event_predOrdI)
    next
      case C_2_enc
      thus ?thesis
        by(fastsimp dest: compr_predOrdI allowed_reveals)
    qed
  qed
qed

lemma (in CR_state_ADVstate) C_ni_synch_state:
  assumes facts:
    "roleMap r test = Some C"
    "( test, C_4 ) \<in> steps t"
  shows
    "(\<exists> tid2.
        roleMap r tid2 = Some S \<and>
        s(AV ''S'' test) = s(AV ''S'' tid2) \<and>
        LN ''k'' test = s(MV ''k'' tid2) \<and>
        St( test, C_2 ) \<prec> St( tid2, S_1 ) \<and>
        St( tid2, S_1 ) \<prec> St( tid2, S_3 ) \<and>
        St( tid2, S_3 ) \<prec> St( test, C_4 ))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis
  proof(sources "Hash ( LN ''k'' test )")
    case fake
    thus ?thesis 
      by(fastsimp dest: C_k_secrecy_state intro: event_predOrdI)
  next
    case (S_3_hash tid2)
    thus ?thesis
    proof(sources "Enc (LN ''k'' test) (PK (s (AV ''S'' tid2)))")
      case C_2_enc
      thus ?thesis by force
    next
      case fake
      thus ?thesis
        by (fastsimp dest: C_k_secrecy_state intro: event_predOrdI)
    qed
  next
    case C_3_hash
    thus ?thesis
      by(fastsimp dest: compr_predOrdI allowed_reveals)
  next
    case (S_2_hash tid2)
    thus ?thesis
    proof(sources "Enc (LN ''k'' test) (PK (s (AV ''S'' tid2)))")
      case fake
      thus ?thesis
        by (fastsimp dest: C_k_secrecy_state intro: event_predOrdI)
    next
      case C_2_enc
      thus ?thesis
        by(fastsimp dest: compr_predOrdI allowed_reveals)
    qed
  qed
qed

lemma (in CR_state_ADVcaC) C_ni_synch_actor:
  assumes facts:
    "roleMap r test = Some C"
    "( test, C_4 ) \<in> steps t"
  shows
    "(\<exists> tid2.
        roleMap r tid2 = Some S \<and>
        s(AV ''S'' test) = s(AV ''S'' tid2) \<and>
        LN ''k'' test = s(MV ''k'' tid2) \<and>
        St( test, C_2 ) \<prec> St( tid2, S_1 ) \<and>
        St( tid2, S_1 ) \<prec> St( tid2, S_3 ) \<and>
        St( tid2, S_3 ) \<prec> St( test, C_4 ))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis
  proof(sources "Hash ( LN ''k'' test )")
    case fake
    thus ?thesis 
      by(fastsimp dest: C_k_secrecy_actor intro: event_predOrdI)
  next
    case (S_3_hash tid2)
    thus ?thesis
    proof(sources "Enc (LN ''k'' test) (PK (s (AV ''S'' tid2)))")
      case C_2_enc
      thus ?thesis by force
    next
      case fake
      thus ?thesis
        by (fastsimp dest: C_k_secrecy_actor intro: event_predOrdI)
    qed
  next
    case C_3_hash
    thus ?thesis
      by(fastsimp dest: compr_predOrdI allowed_reveals)
  next
    case (S_2_hash tid2)
    thus ?thesis
    proof(sources "Enc (LN ''k'' test) (PK (s (AV ''S'' tid2)))")
      case fake
      thus ?thesis
        by (fastsimp dest: C_k_secrecy_actor intro: event_predOrdI)
    next
      case C_2_enc
      thus ?thesis
        by(fastsimp dest: compr_predOrdI allowed_reveals)
    qed
  qed
qed



lemma (in CR_state_ADVall) C_ni_synch_all:
  assumes facts:
    "roleMap r test = Some C"
    "( test, C_4 ) \<in> steps t"
  shows
    "(\<exists> tid2.
        roleMap r tid2 = Some S \<and>
        s(AV ''S'' test) = s(AV ''S'' tid2) \<and>
        LN ''k'' test = s(MV ''k'' tid2) \<and>
        St( test, C_2 ) \<prec> St( tid2, S_1 ) \<and>
        St( tid2, S_1 ) \<prec> St( tid2, S_3 ) \<and>
        St( tid2, S_3 ) \<prec> St( test, C_4 ))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis
  proof(sources "Hash ( LN ''k'' test )")
    case fake
    thus ?thesis 
      by(fastsimp dest: C_k_secrecy_all intro: event_predOrdI)
  next
    case (S_3_hash tid2)
    thus ?thesis
    proof(sources "Enc (LN ''k'' test) (PK (s (AV ''S'' tid2)))")
      case C_2_enc
      thus ?thesis by force
    next
      case fake
      thus ?thesis
        by (fastsimp dest: C_k_secrecy_all intro: event_predOrdI)
    qed
  next
    case C_3_hash
    thus ?thesis
      by(fastsimp dest: compr_predOrdI allowed_reveals)
  next
    case (S_2_hash tid2)
    thus ?thesis
    proof(sources "Enc (LN ''k'' test) (PK (s (AV ''S'' tid2)))")
      case fake
      thus ?thesis
        by (fastsimp dest: C_k_secrecy_all intro: event_predOrdI)
    next
      case C_2_enc
      thus ?thesis
        by(fastsimp dest: compr_predOrdI allowed_reveals)
    qed
  qed
qed

end
