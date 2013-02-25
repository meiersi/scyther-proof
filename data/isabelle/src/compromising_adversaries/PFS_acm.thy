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

theory "PFS_acm"
imports
  "../ESPLogic"
begin

section{* Security Proofs for a protocol guaranteeing PFS *}

subsection{* Protocol Specificiation *}

role A
where "A =
  [ 
    Send ''1'' ( PEnc \<langle> sC ''1'', sAV ''B'', PAsymPK ( sN ''na'' ) \<rangle>
                      ( sSK ''A'' )
               )
  , Recv ''2'' ( PEnc ( PEnc \<langle> sC ''2'', sAV ''A'', sMV ''k'' \<rangle>
                             ( sSK ''B'' )
                      )
                      ( PAsymPK ( sN ''na'' ) )
               )
  , Send ''3'' (PEnc  \<langle> sC ''3'', sAV ''B'', PHash (  sMV ''k'') \<rangle> ( sSK ''A'' ))
  , Note ''4'' SessKey (sMV ''k'')
  ]"

role B
where "B =
  [ Recv ''1'' ( PEnc \<langle> sC ''1'', sAV ''B'', sMV ''pkNa'' \<rangle>
                      ( sSK ''A'' )
               )
  , Send ''2'' ( PEnc ( PEnc \<langle> sC ''2'', sAV ''A'', sN ''k'' \<rangle>
                             ( sSK ''B'' )
                      )
                      ( sMV ''pkNa'' )
               )
  , Recv ''3'' (PEnc  \<langle> sC ''3'', sAV ''B'', PHash (  sN ''k'') \<rangle> ( sSK ''A'' ))
  , Note ''4'' SessKey (sN ''k'')
  ]"

protocol PFS
where "PFS = { A, B }"

(* TODO remove *)
declare (in PFS_state) A_4_def[simp]
declare (in PFS_state) B_4_def[simp]

subsection {* Typing Definition *}

type_invariant auto_msc_typing for PFS
where "auto_msc_typing = mk_typing
  [ ((A, ''k''), (SumT (KnownT A_2) (NonceT B ''k'')))
  , ((B, ''pkNa''), (SumT (KnownT B_1) (PKT (NonceT A ''na''))))
  ]"

sublocale PFS_state \<subseteq> auto_msc_typing_state
proof -
  have "(t,r,s) \<in> approx auto_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF auto_msc_typing.monoTyp, completeness_cases_rule])
    case (A_2_k t r s tid0) note facts = this
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc ( Enc \<lbrace> LC ''2'', s(AV ''A'' tid0), s(MV ''k'' tid0) \<rbrace>
                  ( SK ( s(AV ''B'' tid0) ) )
            )
            ( PK ( LN ''na'' tid0 ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc \<lbrace> LC ''2'', s(AV ''A'' tid0), s(MV ''k'' tid0) \<rbrace>
                           ( SK ( s(AV ''B'' tid0) ) ) ")
      qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits) | (fastforce intro: event_predOrdI split: if_splits))+)?
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (B_1_pkNa t r s tid0) note facts = this
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc \<lbrace> LC ''1'', s(AV ''B'' tid0), s(MV ''pkNa'' tid0) \<rbrace>
            ( SK ( s(AV ''A'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits) | (fastforce intro: event_predOrdI split: if_splits))+)?
  qed
  thus "auto_msc_typing_state t r s" by unfold_locales auto
qed

subsection{* Partnering Definition *}

definition
  PFS_trusted :: "partnering"
where
  "PFS_trusted q = 
    Id \<union>
    mk_partnering A B 
         {(sAV ''A'',  sAV ''A'', B_1),
          (sAV ''B'',  sAV ''B'', B_1),
          (sMV ''k'',  sN  ''k'', B_2),
          ( PAsymPK ( sN ''na'' ),  sMV ''pkNa'', B_1)} q \<union> 
    mk_partnering B A 
         {(sAV ''A'',  sAV ''A'', A_1),
          (sAV ''B'',  sAV ''B'', A_1),
          (sN  ''k'',  sMV ''k'', A_2),
          (sMV ''pkNa'', PAsymPK ( sN ''na'' ), A_1)} q"


lemmas (in PFS_state) PFS_trusted_conv = 
  setEqImpTupleIn[OF PFS_trusted_def, of _ _ "(t,r,s)", simplified]

lemmas (in PFS_state) PFS_trustedI[intro!] = PFS_trusted_conv[THEN iffD2,simplified mk_partnering_conv,simplified]

subsection{* Adversary Compromise Model Definitions *}

definition (in PFS_state) ADVall :: "tid \<Rightarrow> state set"
where
"ADVall i = acm {LKRothers i, LKRafter i, SkR i PFS_trusted}"

locale PFS_state_ADVall = PFS_state +
  fixes test :: tid
  assumes compromiseModel [simp,intro!]: "(t,r,s) \<in> ADVall test"
begin
  lemmas allowed_reveals = acm_to_caps[OF compromiseModel[simplified ADVall_def], simplified]
end

section {* Security Properties *}

subsection{* Origin Proofs *}

lemma (in PFS_state) B_k_origin [rule_format]:
  assumes facts:
    "roleMap r test = Some B"
  shows
    "LN ''k'' test \<in> knows t \<longrightarrow>
    LKR (s(AV ''A'' test)) \<prec> St (test, B_2) \<or> 
    (\<exists> tid1. (test,tid1) \<in> PFS_trusted (t,r,s) \<and> RCompr SessKey tid1 \<in> reveals t)"
  (is "?knows \<longrightarrow> ?origins")
proof
  assume "?knows"
  thus "?origins" using facts 
  proof(sources " LN ''k'' test ")
    case B_2_k
    thus ?thesis
    proof(sources "Enc \<lbrace> LC ''1'', s(AV ''B'' test), s(MV ''pkNa'' test) \<rbrace>
                       ( SK ( s(AV ''A'' test) ) ) ")
      case fake
      thus ?thesis 
      by (sources "SK (s (AV ''A'' test))") (fastforce intro: predOrd_distinct'_trans)
    next
      case (A_1_enc tid1)
      thus ?thesis 
      proof(sources " SK ( LN ''na'' tid1 ) ")
      qed
    qed
  next
    case (A_4_k tid1)
    thus ?thesis
    proof(sources "Enc (Enc \<lbrace>LC ''2'', s (AV ''A'' tid1), LN ''k'' test\<rbrace> (SK (s (AV ''B'' tid1))))
       (PK (LN ''na'' tid1))")
      case fake
      thus ?thesis
      proof(sources "Enc \<lbrace>LC ''2'', s (AV ''A'' tid1), LN ''k'' test\<rbrace> (SK (s (AV ''B'' tid1)))")
        case B_2_enc_1
        thus ?thesis
        proof(sources "Enc \<lbrace>LC ''1'', s (AV ''B'' tid1), s (MV ''pkNa'' test)\<rbrace>
       (SK (s (AV ''A'' tid1)))")
          case fake
          thus ?thesis
            by (sources "SK (s (AV ''A'' test))") (fastforce intro: predOrd_distinct'_trans)
        next
          case (A_1_enc tid1')
          thus ?thesis
          by (sources "SK (LN ''na'' tid1')")
        qed
      qed
    next
      case B_2_enc
      thus ?thesis
        by (auto intro: compr_predOrdI)
    qed
  next
    case B_4_k
    thus ?thesis
      by (auto intro: compr_predOrdI)
  qed
qed

lemma (in PFS_state) A_k_origin [rule_format]:
  assumes facts:
    "roleMap r test = Some A"
    "( test, A_3 ) \<in> steps t"
  shows
    "s(MV ''k'' test) \<in> knows t \<longrightarrow>
    LKR (s(AV ''A'' test)) \<prec> St (test, A_2) \<or> 
    LKR (s(AV ''B'' test)) \<prec> St (test, A_2) \<or> 
    (\<exists> tid1. (test,tid1) \<in> PFS_trusted (t,r,s) \<and> RCompr SessKey tid1 \<in> reveals t)"
  (is "?knows \<longrightarrow> ?origins")
proof
  assume "?knows"
  note_prefix_closed facts = facts this
  thus "?origins"
  proof(sources "Enc ( Enc \<lbrace> LC ''2'', s(AV ''A'' test), s(MV ''k'' test) \<rbrace> ( SK ( s(AV ''B'' test) ) )
                    )( PK ( LN ''na'' test ) ) ")
    case fake
    thus ?thesis
    proof(sources "Enc \<lbrace> LC ''2'', s(AV ''A'' test), s(MV ''k'' test) \<rbrace>
                       ( SK ( s(AV ''B'' test) ) ) ")
      case fake
      thus ?thesis
      by (sources "SK (s (AV ''B'' test))") (fastforce intro: predOrd_distinct'_trans)
    next
      case (B_2_enc_1 tid1)
      thus ?thesis
      proof(sources "Enc \<lbrace>LC ''1'', s (AV ''B'' test), s (MV ''pkNa'' tid1)\<rbrace>
       (SK (s (AV ''A'' test)))")
        case fake
        thus ?thesis
          by (sources "SK (s (AV ''A'' tid1))")(fastforce intro: predOrd_distinct'_trans)    next
        case (A_1_enc tid1')
        thus ?thesis
           by (sources "SK (LN ''na'' tid1')")
      qed
    qed
  next
    case (B_2_enc tid1)
    thus ?thesis 
    proof(sources "LN ''k'' tid1")
      case (A_4_k test')
      note facts = facts this
      thus ?thesis 
      proof(sources "Enc (Enc \<lbrace>LC ''2'', s (AV ''A'' test'), LN ''k'' tid1\<rbrace> (SK (s (AV ''B'' test'))))
       (PK (LN ''na'' test'))")
        case fake
        thus ?thesis
        proof(sources "Enc \<lbrace>LC ''2'', s (AV ''A'' test'), LN ''k'' tid1\<rbrace> (SK (s (AV ''B'' test')))")
          case B_2_enc_1
          thus ?thesis
            by (sources "SK (LN ''na'' test)")
        qed
      next
        case B_2_enc
        note_unified facts = facts this
        thus ?thesis
          by (auto intro: compr_predOrdI)
      qed
    next
      case B_2_k
      thus ?thesis 
        by (sources "SK (LN ''na'' test)")
    next
      case B_4_k
      thus ?thesis
      by (auto intro: compr_predOrdI)
    qed
  qed
qed


subsection{* Secrecy Proofs *}
lemma (in PFS_state_ADVall) B_sec_k:
  assumes facts:
    "roleMap r test = Some B"
    "LN ''k'' test \<in> knows t"
    "(test,B_3) \<in> steps t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  moreover {
    assume "LKR (s (AV ''A'' test)) \<prec> St (test, B_2)"
    hence "?thesis" using facts
      apply -
      apply(frule lkr_in_reveals_predOrd1)
      by (auto dest: allowed_reveals)
  }
  moreover {
    assume "(\<exists>tid1. (test, tid1) \<in> PFS_trusted (t, r, s) \<and> RCompr SessKey tid1 \<in> reveals t) \<or> 
            (\<exists>tid1. (test, tid1) \<in> PFS_trusted (t, r, s) \<and> RCompr State tid1 \<in> reveals t)"
    hence "?thesis" using facts by(auto dest: allowed_reveals)
  }
  ultimately show ?thesis by (auto dest: B_k_origin)
qed

lemma (in PFS_state_ADVall) A_sec_k:
  assumes facts:
    "roleMap r test = Some A"
    "( test, A_3 ) \<in> steps t"
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
    assume "(\<exists>tid1. (test, tid1) \<in> PFS_trusted (t, r, s) \<and> RCompr SessKey tid1 \<in> reveals t) \<or> 
            (\<exists>tid1. (test, tid1) \<in> PFS_trusted (t, r, s) \<and> RCompr State tid1 \<in> reveals t)"
    hence "?thesis" using facts by(auto dest: allowed_reveals)
  }
  ultimately show ?thesis by (auto dest: A_k_origin)
qed


subsection{* Authentication Proofs *}
lemma (in PFS_state_ADVall) A_ni_auth:
  assumes facts:
    "roleMap r test = Some A"
    "(test, A_3) \<in> steps t"
  shows
    "\<exists> tid1. 
    roleMap r tid1 = Some B \<and>
    s(AV ''A'' test) = s(AV ''A'' tid1) \<and>
    s(AV ''B'' test) = s(AV ''B'' tid1) \<and>
    s(MV ''k'' test) = LN ''k'' tid1 \<and>
    PK (LN ''na'' test) = s (MV ''pkNa'' tid1) \<and>
    St (test, A_1) \<prec> St (tid1, B_1) \<and>
    St (tid1, B_2) \<prec> St (test, A_2)"
proof -
    note_prefix_closed facts = facts
    thus ?thesis
    proof(sources "Enc (Enc \<lbrace>LC ''2'', s (AV ''A'' test), s (MV ''k'' test)\<rbrace> (SK (s (AV ''B'' test)))) (PK (LN ''na'' test))")
      case fake
      thus ?thesis
      proof(sources "Enc \<lbrace>LC ''2'', s (AV ''A'' test), s (MV ''k'' test)\<rbrace> (SK (s (AV ''B'' test)))")
        case fake
        thus ?thesis
          by (fastforce dest: A_sec_k event_predOrdI)
      next
        case (B_2_enc_1 tid1)
        thus ?thesis
        proof(sources "Enc \<lbrace>LC ''1'', s (AV ''B'' test), s (MV ''pkNa'' tid1)\<rbrace> (SK (s (AV ''A'' test)))")
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
          case (A_1_enc test)
          thus ?thesis
            by (sources "SK (LN ''na'' test)")             
        qed
      qed
    next
      case (B_2_enc tid1)
      thus ?thesis 
        proof(sources "Enc \<lbrace>LC ''1'', s (AV ''B'' test), PK (LN ''na'' test)\<rbrace> (SK (s (AV ''A'' test)))")
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

lemma (in PFS_state_ADVall) B_ni_auth:
  assumes facts:
    "roleMap r test = Some B"
    "(test, B_3) \<in> steps t"
  shows
    "\<exists> tid1. 
    roleMap r tid1 = Some A \<and>
    s(AV ''A'' tid1) = s(AV ''A'' test) \<and>
    s(AV ''B'' tid1) = s(AV ''B'' test) \<and>
    s(MV ''k'' tid1) = LN ''k'' test \<and>
    PK (LN ''na'' tid1) = s (MV ''pkNa'' test) \<and>
    St (tid1, A_1) \<prec> St (test, B_1) \<and>
    St (test, B_2) \<prec> St (tid1, A_2) \<and>
    St (tid1, A_3) \<prec> St (test, B_3)"
proof -
    note_prefix_closed facts = facts
    thus ?thesis
    proof(sources "Enc \<lbrace>LC ''3'', s (AV ''B'' test), Hash (LN ''k'' test)\<rbrace> (SK (s (AV ''A'' test)))")
      case fake
      thus ?thesis
      proof(sources "SK (s (AV ''A'' test))")
        case asym_lkr
        thus ?thesis
          apply -
          apply(frule lkr_in_reveals_predOrd1)
          by (auto dest: allowed_reveals)
      qed
    next
      case (A_3_enc tid3)
      thus ?thesis
      proof(sources "Enc (Enc \<lbrace>LC ''2'', s (AV ''A'' test), LN ''k'' test\<rbrace> (SK (s (AV ''B'' tid3)))) (PK (LN ''na'' tid3))")
        case fake
        thus ?thesis
        proof(sources "Enc \<lbrace>LC ''2'', s (AV ''A'' tid3), LN ''k'' test\<rbrace> (SK (s (AV ''B'' tid3)))")
          case fake
          thus ?thesis 
          proof(sources "SK (s (AV ''B'' tid3))")
            case asym_lkr
            thus ?thesis
              apply -
              apply(frule lkr_in_reveals_predOrd1)
              by (fastforce dest: allowed_reveals)              
          qed
        next
          case B_2_enc_1
          thus ?thesis
          proof(sources "Enc \<lbrace>LC ''1'', s (AV ''B'' tid3), s (MV ''pkNa'' test)\<rbrace> (SK (s (AV ''A'' tid3)))")
            case fake
            thus ?thesis 
            proof(sources "SK (s (AV ''A'' tid3))")
              case asym_lkr
              thus ?thesis
                apply -
                apply(frule lkr_in_reveals_predOrd1)
                by (fastforce dest: allowed_reveals)
            qed
          next
            case (A_1_enc tid2)
            thus ?thesis
              by (sources "SK (LN ''na'' tid2)")
          qed
        qed
      next
        case B_2_enc
        thus ?thesis
        proof(sources "Enc \<lbrace>LC ''1'', s (AV ''B'' tid3), PK (LN ''na'' tid3)\<rbrace> (SK (s (AV ''A'' tid3)))")
          case fake
          thus ?thesis
            proof(sources "SK (s (AV ''A'' tid3))")
              case asym_lkr
              thus ?thesis
                apply -
                apply(frule lkr_in_reveals_predOrd1)
                by (fastforce dest: allowed_reveals)
            qed
        next
          case A_1_enc
          thus ?thesis
            by force
        qed
      qed
    qed
qed

end
