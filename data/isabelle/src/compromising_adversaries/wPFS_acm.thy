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

theory "wPFS_acm"
imports
  "../ESPLogic"
begin

section{* Security Proofs for a protocol guaranteeing wPFS *}

subsection{* Protocol Specificiation *}

role A
where "A =
  [ 
   Note ''N0'' State \<langle> sN ''sid'', sAV ''B'', sAV ''A'', PAsymPK ( sN ''na'' ), sN ''na'', PAsymSK ( sN ''na'' ) \<rangle> 
  , Send ''1'' ( PEnc \<langle> sC ''1'', sN ''sid'', sAV ''B'', PAsymPK ( sN ''na'' ) \<rangle>
                      ( sSK ''A'' )
               )
  , Note ''N1'' State \<langle> PAsymPK ( sN ''na'' ), sN ''na'', sN ''sid'',  sAV ''B'', sAV ''A'', PAsymSK ( sN ''na'' ) \<rangle> 
  , Recv ''2'' ( PEnc ( PEnc \<langle> sC ''2'', sN ''sid'', sAV ''A'', sMV ''k'' \<rangle>
                             ( sSK ''B'' )
                      )
                      ( PAsymPK ( sN ''na'' ) )
               )
  , Note ''N2'' State \<langle> sMV ''k'', sN ''sid'', sAV ''B'', sAV ''A'' \<rangle>
  , Note ''3'' SessKey (sMV ''k'')
  ]"

role B
where "B =
  [ Recv ''1'' ( PEnc \<langle> sC ''1'', sMV ''sid'', sAV ''B'', sMV ''pkNa'' \<rangle>
                      ( sSK ''A'' )
               )
  , Note ''N1'' State \<langle> sN ''k'', sMV ''pkNa'', sN ''sid'', sAV ''B'', sAV ''A''\<rangle>
  , Send ''2'' ( PEnc ( PEnc \<langle> sC ''2'', sMV ''sid'', sAV ''A'', sN ''k'' \<rangle>
                             ( sSK ''B'' )
                      )
                      ( sMV ''pkNa'' )
               )
  , Note ''N2'' State \<langle> sN ''k'', sMV ''sid'', sAV ''B'', sAV ''A'' \<rangle> 
  , Note ''3'' SessKey (sN ''k'')
  ]"

protocol wPFS
where "wPFS = { A, B }"

(* TODO remove *)
declare (in wPFS_state) A_3_def[simp]
declare (in wPFS_state) B_3_def[simp]
declare (in wPFS_state) A_N0_def[simp]
declare (in wPFS_state) A_N1_def[simp]
declare (in wPFS_state) B_N1_def[simp]
declare (in wPFS_state) A_N2_def[simp]
declare (in wPFS_state) B_N2_def[simp]

subsection {* Typing Definition *}
type_invariant auto_msc_typing for wPFS
where "auto_msc_typing = mk_typing
  [ ((A, ''k''), (SumT (KnownT A_2) (NonceT B ''k'')))
  , ((B, ''pkNa''), (SumT (KnownT B_1) (PKT (NonceT A ''na''))))
  , ((B, ''sid''), (SumT (KnownT B_1) (NonceT A ''sid'')))
  ]"

sublocale wPFS_state \<subseteq> auto_msc_typing_state
proof -
  have "(t,r,s) \<in> approx auto_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF auto_msc_typing.monoTyp, completeness_cases_rule])
    case (A_2_k t r s tid0) note facts = this
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc ( Enc \<lbrace> LC ''2'', LN ''sid'' tid0, s(AV ''A'' tid0),
                    s(MV ''k'' tid0)
                  \<rbrace>
                  ( SK ( s(AV ''B'' tid0) ) )
            )
            ( PK ( LN ''na'' tid0 ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc \<lbrace> LC ''2'', LN ''sid'' tid0, s(AV ''A'' tid0), s(MV ''k'' tid0)
                           \<rbrace>
                           ( SK ( s(AV ''B'' tid0) ) ) ")
      qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits) | (fastforce intro: event_predOrdI split: if_splits))+)?
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (B_1_pkNa t r s tid0) note facts = this
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc \<lbrace> LC ''1'', s(MV ''sid'' tid0), s(AV ''B'' tid0),
              s(MV ''pkNa'' tid0)
            \<rbrace>
            ( SK ( s(AV ''A'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits) | (fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (B_1_sid t r s tid0) note facts = this
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc \<lbrace> LC ''1'', s(MV ''sid'' tid0), s(AV ''B'' tid0),
              s(MV ''pkNa'' tid0)
            \<rbrace>
            ( SK ( s(AV ''A'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits) | (fastforce intro: event_predOrdI split: if_splits))+)?
  qed
  thus "auto_msc_typing_state t r s" by unfold_locales auto
qed

subsection{* Partnering Definition *}

definition
  wPFS_trusted :: "partnering"
where
  "wPFS_trusted q = 
    Id \<union>
    mk_partnering A B 
         {(sAV ''A'',  sAV ''A'', B_1),
          (sAV ''B'',  sAV ''B'', B_1),
          (sMV ''k'',  sN  ''k'', B_2),
          (sN ''sid'', sMV ''sid'', B_1)} q \<union> 
    mk_partnering B A 
         {(sAV ''A'',  sAV ''A'', A_1),
          (sAV ''B'',  sAV ''B'', A_1),
          (sMV ''sid'', sN ''sid'', A_1)} q"


lemmas (in wPFS_state) wPFS_trusted_conv = 
  setEqImpTupleIn[OF wPFS_trusted_def, of _ _ "(t,r,s)", simplified]

lemmas (in wPFS_state) wPFS_trustedI[intro!] = wPFS_trusted_conv[THEN iffD2,simplified mk_partnering_conv,simplified]

subsection{* Adversary Compromise Model Definitions *}

definition (in wPFS_state) ADVall :: "tid \<Rightarrow> state set"
where
(* "ADVall i = acm {LKRothers i, LKRafterCorrect i wPFS_trusted, SkR i wPFS_trusted, StR i wPFS_trusted}" *)
"ADVall i = acm {LKRothers i, LKRafter i, SkR i wPFS_trusted, StR i wPFS_trusted}"

locale wPFS_state_ADVall = wPFS_state +
  fixes test :: tid
  assumes compromiseModel [simp,intro!]: "(t,r,s) \<in> ADVall test"
begin
  lemmas allowed_reveals = acm_to_caps[OF compromiseModel[simplified ADVall_def], simplified]
end

section {* Security Properties *}

subsection{* Origin Proofs *}

lemma (in wPFS_state) B_k_origin[rule_format]:
  assumes facts:
    "roleMap r test = Some B"
  shows
    "LN ''k'' test \<in> knows t \<longrightarrow>
    LKR (s(AV ''A'' test)) \<prec> St (test, B_1) \<or> 
    (\<exists> tid1. (test,tid1) \<in> wPFS_trusted (t,r,s) \<and> RCompr SessKey tid1 \<in> reveals t) \<or>
    (\<exists> tid1. (test,tid1) \<in> wPFS_trusted (t,r,s) \<and> RCompr State tid1 \<in> reveals t)"
  (is "?knows \<longrightarrow> ?origins")
proof
  assume "?knows"
  thus "?origins" using facts 
  proof(sources " LN ''k'' test ")
    case B_2_k
    thus ?thesis
    proof(sources "Enc \<lbrace>LC ''1'', s (MV ''sid'' test), s (AV ''B'' test), s (MV ''pkNa'' test)\<rbrace>
       (SK (s (AV ''A'' test)))")
      case fake
      thus ?thesis
        by (sources "SK (s (AV ''A'' test))") (fastforce intro: predOrd_distinct'_trans)
    next
      case (A_1_enc tid1)
      thus ?thesis 
      proof(sources " SK ( LN ''na'' tid1 ) ")
        case A_N1_SK
        thus ?thesis 
          by (fastforce intro: compr_predOrdI)
      next
        case A_N0_SK
        thus ?thesis
          by (fastforce intro: compr_predOrdI)
      qed
    qed
  next
    case B_3_k
    thus ?thesis
      by (auto intro: compr_predOrdI)
  next
    case B_N1_k
    thus ?thesis
      by (auto intro: compr_predOrdI)
  next
    case B_N2_k
    thus ?thesis
      by (auto intro: compr_predOrdI)
  next
    case (A_N2_k tid1)
    thus ?thesis
    proof(sources "Enc (Enc \<lbrace>LC ''2'', LN ''sid'' tid1, s (AV ''A'' tid1), LN ''k'' test\<rbrace> (SK (s (AV ''B'' tid1))))
       (PK (LN ''na'' tid1))")
      case fake
      thus ?thesis
      proof(sources "Enc \<lbrace>LC ''2'', LN ''sid'' tid1, s (AV ''A'' tid1), LN ''k'' test\<rbrace> (SK (s (AV ''B'' tid1)))")
        case B_2_enc_1
        thus ?thesis
          by (auto intro: compr_predOrdI)
      qed
    next
      case B_2_enc
      thus ?thesis
        by (auto intro: compr_predOrdI)
    qed
  next
    case (A_3_k tid1)
    thus ?thesis
    proof(sources "Enc (Enc \<lbrace>LC ''2'', LN ''sid'' tid1, s (AV ''A'' tid1), LN ''k'' test\<rbrace> (SK (s (AV ''B'' tid1))))
       (PK (LN ''na'' tid1))")
      case fake
      thus ?thesis
      proof(sources "Enc \<lbrace>LC ''2'', LN ''sid'' tid1, s (AV ''A'' tid1), LN ''k'' test\<rbrace> (SK (s (AV ''B'' tid1)))")
        case B_2_enc_1
        thus ?thesis
          by (auto intro: compr_predOrdI)
      qed
    next
      case B_2_enc
      thus ?thesis
        by (auto intro: compr_predOrdI)
    qed
  qed
qed



lemma (in wPFS_state) A_k_origin [rule_format]:
  assumes facts:
    "roleMap r test = Some A"
    "( test, A_2 ) \<in> steps t"
  shows
    "s(MV ''k'' test) \<in> knows t \<longrightarrow>
    LKR (s(AV ''A'' test)) \<prec> St (test, A_2) \<or> 
    LKR (s(AV ''B'' test)) \<prec> St (test, A_2) \<or> 
    (\<exists> tid1. (test,tid1) \<in> wPFS_trusted (t,r,s) \<and> RCompr SessKey tid1 \<in> reveals t) \<or>
    (\<exists> tid1. (test,tid1) \<in> wPFS_trusted (t,r,s) \<and> RCompr State tid1 \<in> reveals t)"
  (is "?knows \<longrightarrow> ?origins")
proof
  assume "?knows"
  note_prefix_closed facts = facts this
  thus "?origins"
  proof(sources "Enc (Enc \<lbrace>LC ''2'', LN ''sid'' test, s (AV ''A'' test), s (MV ''k'' test)\<rbrace> (SK (s (AV ''B'' test))))
       (PK (LN ''na'' test))")
    case fake
    thus ?thesis
    proof(sources "Enc \<lbrace>LC ''2'', LN ''sid'' test, s (AV ''A'' test), s (MV ''k'' test)\<rbrace> (SK (s (AV ''B'' test)))")
      case fake
      thus ?thesis
        by (sources "SK (s (AV ''B'' test))") (fastforce intro: predOrd_distinct'_trans)
    next
      case (B_2_enc_1 tid1)
      thus ?thesis
      proof(sources "Enc \<lbrace>LC ''1'', LN ''sid'' test, s (AV ''B'' test), s (MV ''pkNa'' tid1)\<rbrace> (SK (s (AV ''A'' test)))")
        case fake
        thus ?thesis
          by (sources "SK (s (AV ''A'' test))") (fastforce intro: predOrd_distinct'_trans)
      qed
    qed
  next
    case (B_2_enc tid1)
    thus ?thesis
    proof(sources "LN ''k'' tid1")
      case B_N1_k
      thus ?thesis
        by (auto intro: compr_predOrdI)
    next
      case B_N2_k
      thus ?thesis
        by (auto intro: compr_predOrdI)      
    next
      case B_3_k
      thus ?thesis
        by (auto intro: compr_predOrdI)
    next
      case B_2_k
      thus ?thesis
      proof(sources "SK (LN ''na'' test)")
        case A_N1_SK
        thus ?thesis
          by (auto intro: compr_predOrdI)
      next
        case A_N0_SK
        thus ?thesis
          by (auto intro: compr_predOrdI)
      qed
    next
      case (A_N2_k test')
      note_unified facts = facts this
      thus ?thesis
      proof(sources "Enc (Enc \<lbrace>LC ''2'', LN ''sid'' test', s (AV ''A'' test'), LN ''k'' tid1\<rbrace> (SK (s (AV ''B'' test'))))
       (PK (LN ''na'' test'))")
        case fake
        thus ?thesis
        by (sources "Enc \<lbrace>LC ''2'', LN ''sid'' test', s (AV ''A'' test'), LN ''k'' tid1\<rbrace>
       (SK (s (AV ''B'' test')))")
     next
       case B_2_enc
       note_unified facts = facts this
       thus ?thesis
         by (auto intro: compr_predOrdI)
     qed
    next
      case (A_3_k test')
      note_unified facts = facts this
      thus ?thesis
      proof(sources "Enc (Enc \<lbrace>LC ''2'', LN ''sid'' test', s (AV ''A'' test'), LN ''k'' tid1\<rbrace> (SK (s (AV ''B'' test'))))
       (PK (LN ''na'' test'))")
        case fake
        thus ?thesis
        by (sources "Enc \<lbrace>LC ''2'', LN ''sid'' test', s (AV ''A'' test'), LN ''k'' tid1\<rbrace>
       (SK (s (AV ''B'' test')))")
     next
       case B_2_enc
       note_unified facts = facts this
       thus ?thesis
         by (auto intro: compr_predOrdI)
     qed
    qed
  qed
qed

subsection{* Secrecy Proofs *}
lemma (in wPFS_state_ADVall) B_sec_k:
  assumes facts:
    "roleMap r test = Some B"
    "LN ''k'' test \<in> knows t"
    "(test,B_2) \<in> steps t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  moreover {
    assume "LKR (s (AV ''A'' test)) \<prec> St (test, B_1)"
    hence "?thesis" using facts
      apply -
      apply(frule lkr_in_reveals_predOrd1)
      by (auto dest: allowed_reveals)
  }
  moreover {
    assume "(\<exists>tid1. (test, tid1) \<in> wPFS_trusted (t, r, s) \<and> RCompr SessKey tid1 \<in> reveals t) \<or> 
            (\<exists>tid1. (test, tid1) \<in> wPFS_trusted (t, r, s) \<and> RCompr State tid1 \<in> reveals t)"
    hence "?thesis" using facts by(auto dest: allowed_reveals)
  }
  ultimately show ?thesis by (auto dest: B_k_origin)
qed

lemma (in wPFS_state_ADVall) A_sec_k:
  assumes facts:
    "roleMap r test = Some A"
    "( test, A_2 ) \<in> steps t"
    "s(MV ''k'' test) \<in> knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  moreover {
    assume "LKR (s (AV ''A'' test)) \<prec> St (test, A_2)"
    hence "?thesis" using facts
      apply -
      apply(frule lkr_in_reveals_predOrd1)
      by (auto dest: allowed_reveals)
  }
  moreover {
    assume "LKR (s (AV ''B'' test)) \<prec> St (test, A_2)"
    hence "?thesis" using facts
      apply -
      apply(frule lkr_in_reveals_predOrd1)
      by (auto dest: allowed_reveals)
  }  
  moreover {
    assume "(\<exists>tid1. (test, tid1) \<in> wPFS_trusted (t, r, s) \<and> RCompr SessKey tid1 \<in> reveals t) \<or> 
            (\<exists>tid1. (test, tid1) \<in> wPFS_trusted (t, r, s) \<and> RCompr State tid1 \<in> reveals t)"
    hence "?thesis" using facts by(auto dest: allowed_reveals)
  }
  ultimately show ?thesis by (auto dest: A_k_origin)
qed


subsection{* Authentication Proofs *}
lemma (in wPFS_state_ADVall) A_ni_auth:
  assumes facts:
    "roleMap r test = Some A"
    "(test, A_2) \<in> steps t"
  shows
    "\<exists> tid1. 
    roleMap r tid1 = Some B \<and>
    s(AV ''A'' test) = s(AV ''A'' tid1) \<and>
    s(AV ''B'' test) = s(AV ''B'' tid1) \<and>
    s(MV ''k'' test) = LN ''k'' tid1 \<and>
    LN ''sid'' test = s(MV ''sid'' tid1) \<and>
    PK (LN ''na'' test) = s (MV ''pkNa'' tid1) \<and>
    St (test, A_1) \<prec> St (tid1, B_1) \<and>
    St (tid1, B_2) \<prec> St (test, A_2)"
proof -
    note_prefix_closed facts = facts
    thus ?thesis
    proof(sources "Enc (Enc \<lbrace>LC ''2'', LN ''sid'' test, s (AV ''A'' test), s (MV ''k'' test)\<rbrace> (SK (s (AV ''B'' test)))) (PK (LN ''na'' test))")
      case fake
      thus ?thesis
      proof(sources "Enc \<lbrace>LC ''2'', LN ''sid'' test, s (AV ''A'' test), s (MV ''k'' test)\<rbrace> (SK (s (AV ''B'' test)))")
        case fake
        thus ?thesis
          by (fastforce dest: A_sec_k event_predOrdI)
      next
        case (B_2_enc_1 tid1)
        thus ?thesis
        proof(sources "Enc \<lbrace>LC ''1'', LN ''sid'' test, s (AV ''B'' test), s (MV ''pkNa'' tid1)\<rbrace> (SK (s (AV ''A'' test)))")
          case fake
          thus ?thesis
          proof(sources "SK (s (AV ''A'' tid1))")
            case asym_lkr
            thus ?thesis
              apply -
              apply(frule lkr_in_reveals_predOrd1)
              by (fastforce dest: allowed_reveals)
          qed
        qed
      qed
    next
      case (B_2_enc tid1)
      thus ?thesis 
        proof(sources "Enc \<lbrace>LC ''1'', LN ''sid'' test, s (AV ''B'' test), PK (LN ''na'' test)\<rbrace> (SK (s (AV ''A'' test)))")
          case fake
          thus ?thesis
          proof(sources "SK (s (AV ''A'' tid1))")
            case asym_lkr
            thus ?thesis
              apply -
              apply(frule lkr_in_reveals_predOrd1)
              by (fastforce dest: allowed_reveals)
          qed
        next
          case A_1_enc
          thus ?thesis by force
        qed      
    qed
qed

lemma (in wPFS_state_ADVall) B_ni_auth:
  assumes facts:
    "roleMap r test = Some B"
    "(test, B_2) \<in> steps t"
  shows
    "\<exists> tid1. 
    roleMap r tid1 = Some A \<and>
    s(AV ''A'' tid1) = s(AV ''A'' test) \<and>
    s(AV ''B'' tid1) = s(AV ''B'' test) \<and>
    PK (LN ''na'' tid1) = s (MV ''pkNa'' test) \<and>
    LN ''sid'' tid1 = s (MV ''sid'' test) \<and>
    St (tid1, A_1) \<prec> St (test, B_1)"
proof -
  note_prefix_closed facts = facts
  thus ?thesis
  proof(sources "Enc \<lbrace>LC ''1'', s (MV ''sid'' test), s (AV ''B'' test), s (MV ''pkNa'' test)\<rbrace>
      (SK (s (AV ''A'' test)))")
    case fake
    thus ?thesis
    proof(sources "SK (s (AV ''A'' test))")
      case asym_lkr
      thus ?thesis
        apply -
        apply(frule lkr_in_reveals_predOrd1)
        by (fastforce dest: allowed_reveals)
    qed
  next
    case (A_1_enc tid1)
    thus ?thesis
      by auto
  qed
qed

end
