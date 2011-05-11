theory BKE_cert_auto
imports
  "../ESPLogic"
begin

role I
where "I =
  [ Send ''1'' {| sLAV ''I'',
                  Enc {| sLC ''TT1'', sLN ''ni'', sLAV ''I'' |} ( sPK ''R'' )
               |}
  , Recv ''2'' ( Enc {| sLC ''TT2'', Hash ( sLN ''ni'' ),
                        sLNV ''nr'', sLAV ''R'', sLNV ''kir''
                     |}
                     ( sPK ''I'' )
               )
  , Send ''3'' ( Enc {| sLC ''TT3'', Hash ( sLNV ''nr'' ) |}
                     ( sLNV ''kir'' )
               )
  ]"

role R
where "R =
  [ Recv ''1'' {| sLAV ''I'',
                  Enc {| sLC ''TT1'', sLNV ''ni'', sLAV ''I'' |} ( sPK ''R'' )
               |}
  , Send ''2'' ( Enc {| sLC ''TT2'', Hash ( sLNV ''ni'' ),
                        sLN ''nr'', sLAV ''R'', sLN ''kir''
                     |}
                     ( sPK ''I'' )
               )
  , Recv ''3'' ( Enc {| sLC ''TT3'', Hash ( sLN ''nr'' ) |}
                     ( sLN ''kir'' )
               )
  ]"

protocol BKE
where "BKE = { I, R }"

locale atomic_BKE_state = atomic_state BKE
locale BKE_state = reachable_state BKE

lemma (in atomic_BKE_state) I_sk_I_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "SK ( s(|AV ''I'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_BKE_state) I_sk_R_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "SK ( s(|AV ''R'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! " SK ( s(|AV ''R'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_BKE_state) R_sk_I_secrecy:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "SK ( s(|AV ''I'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_BKE_state) R_sk_R_secrecy:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "SK ( s(|AV ''R'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! " SK ( s(|AV ''R'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_BKE_state) I_ni_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "LN ''ni'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''ni'' tid0 ")
  case I_1_ni note facts = facts this[simplified]
  thus ?thesis by (fastsimp dest: I_sk_R_secrecy intro: event_predOrdI)
qed

lemma (in atomic_BKE_state) R_nr_secrecy:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "LN ''nr'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''nr'' tid0 ")
  case R_2_nr note facts = facts this[simplified]
  thus ?thesis by (fastsimp dest: R_sk_I_secrecy intro: event_predOrdI)
qed

lemma (in atomic_BKE_state) R_kir_secrecy:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "LN ''kir'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''kir'' tid0 ")
  case R_2_kir note facts = facts this[simplified]
  thus ?thesis by (fastsimp dest: R_sk_I_secrecy intro: event_predOrdI)
qed

lemma (in atomic_BKE_state) I_hash_ni_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "Hash ( LN ''ni'' tid0 ) : knows t"
  shows "False"
using facts proof(sources! " Hash ( LN ''ni'' tid0 ) ")
  case fake note facts = facts this[simplified]
  thus ?thesis by (fastsimp dest: I_ni_secrecy intro: event_predOrdI)
next
  case (I_3_hash tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT2'', Hash ( LN ''ni'' tid1 ), LN ''ni'' tid0,
                          s(|AV ''R'' tid1|), s(|NV ''kir'' tid1|)
                       |}
                       ( PK ( s(|AV ''I'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: I_ni_secrecy intro: event_predOrdI)
  qed
next
  case (R_2_hash tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', LN ''ni'' tid0, s(|AV ''I'' tid1|) |}
                       ( PK ( s(|AV ''R'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: I_ni_secrecy intro: event_predOrdI)
  next
    case I_1_enc note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: I_sk_I_secrecy intro: event_predOrdI)
  qed
qed

lemma (in atomic_BKE_state) R_hash_nr_secrecy:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "Hash ( LN ''nr'' tid0 ) : knows t"
  shows "False"
using facts proof(sources! " Hash ( LN ''nr'' tid0 ) ")
  case fake note facts = facts this[simplified]
  thus ?thesis by (fastsimp dest: R_nr_secrecy intro: event_predOrdI)
next
  case (I_3_hash tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT2'', Hash ( LN ''ni'' tid1 ), LN ''nr'' tid0,
                          s(|AV ''R'' tid1|), s(|NV ''kir'' tid1|)
                       |}
                       ( PK ( s(|AV ''I'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: R_nr_secrecy intro: event_predOrdI)
  next
    case R_2_enc note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: R_kir_secrecy intro: event_predOrdI)
  qed
next
  case (R_2_hash tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', LN ''nr'' tid0, s(|AV ''I'' tid1|) |}
                       ( PK ( s(|AV ''R'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: R_nr_secrecy intro: event_predOrdI)
  qed
qed

lemma (in atomic_BKE_state) I_nr_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "(tid0, I_2) : steps t"
    "s(|NV ''nr'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT2'', Hash ( LN ''ni'' tid0 ), s(|NV ''nr'' tid0|),
                          s(|AV ''R'' tid0|), s(|NV ''kir'' tid0|)
                       |}
                       ( PK ( s(|AV ''I'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: I_hash_ni_secrecy intro: event_predOrdI)
  next
    case (R_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: R_nr_secrecy intro: event_predOrdI)
  qed
qed

lemma (in atomic_BKE_state) I_kir_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "(tid0, I_2) : steps t"
    "s(|NV ''kir'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT2'', Hash ( LN ''ni'' tid0 ), s(|NV ''nr'' tid0|),
                          s(|AV ''R'' tid0|), s(|NV ''kir'' tid0|)
                       |}
                       ( PK ( s(|AV ''I'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: I_hash_ni_secrecy intro: event_predOrdI)
  next
    case (R_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: R_kir_secrecy intro: event_predOrdI)
  qed
qed

lemma (in atomic_BKE_state) R_ni_secrecy:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "(tid0, R_3) : steps t"
    "s(|NV ''ni'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|NV ''ni'' tid0|), s(|AV ''I'' tid0|) |}
                       ( PK ( s(|AV ''R'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT3'', Hash ( LN ''nr'' tid0 ) |}
                         ( LN ''kir'' tid0 ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: R_kir_secrecy intro: event_predOrdI)
    next
      case (I_3_enc tid1) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT2'', Hash ( LN ''ni'' tid1 ), LN ''nr'' tid0,
                              s(|AV ''R'' tid1|), LN ''kir'' tid0
                           |}
                           ( PK ( s(|AV ''I'' tid1|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: R_nr_secrecy intro: event_predOrdI)
      next
        case R_2_enc note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: I_ni_secrecy intro: event_predOrdI)
      qed
    qed
  next
    case (I_1_enc tid1) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: I_ni_secrecy intro: event_predOrdI)
  qed
qed

lemma (in atomic_BKE_state) I_ni_synch:
  assumes facts:
    "roleMap r tid1 = Some I"
    "s(|AV ''I'' tid1|) ~: Compromised"
    "s(|AV ''R'' tid1|) ~: Compromised"
    "(tid1, I_3) : steps t"
  shows
    "? tid2.
       roleMap r tid2 = Some R &
       s(|AV ''I'' tid2|) = s(|AV ''I'' tid1|) &
       s(|AV ''R'' tid2|) = s(|AV ''R'' tid1|) &
       s(|NV ''kir'' tid1|) = LN ''kir'' tid2 &
       s(|NV ''ni'' tid2|) = LN ''ni'' tid1 &
       s(|NV ''nr'' tid1|) = LN ''nr'' tid2 &
       predOrd t (St(tid1, I_1)) (St(tid2, R_1)) &
       predOrd t (St(tid1, I_2)) (St(tid1, I_3)) &
       predOrd t (St(tid2, R_2)) (St(tid1, I_2)) &
       predOrd t (St(tid2, R_1)) (St(tid2, R_2))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT2'', Hash ( LN ''ni'' tid1 ), s(|NV ''nr'' tid1|),
                          s(|AV ''R'' tid1|), s(|NV ''kir'' tid1|)
                       |}
                       ( PK ( s(|AV ''I'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: I_hash_ni_secrecy intro: event_predOrdI)
  next
    case (R_2_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', LN ''ni'' tid1, s(|AV ''I'' tid1|) |}
                         ( PK ( s(|AV ''R'' tid1|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: I_ni_secrecy intro: event_predOrdI)
    next
      case I_1_enc note facts = facts this[simplified]
      thus ?thesis by force
    qed
  qed
qed

lemma (in atomic_BKE_state) R_ni_synch:
  assumes facts:
    "roleMap r tid1 = Some R"
    "s(|AV ''I'' tid1|) ~: Compromised"
    "s(|AV ''R'' tid1|) ~: Compromised"
    "(tid1, R_3) : steps t"
  shows
    "? tid2.
       roleMap r tid2 = Some I &
       s(|AV ''I'' tid2|) = s(|AV ''I'' tid1|) &
       s(|AV ''R'' tid2|) = s(|AV ''R'' tid1|) &
       s(|NV ''kir'' tid2|) = LN ''kir'' tid1 &
       s(|NV ''ni'' tid1|) = LN ''ni'' tid2 &
       s(|NV ''nr'' tid2|) = LN ''nr'' tid1 &
       predOrd t (St(tid1, R_2)) (St(tid2, I_2)) &
       predOrd t (St(tid1, R_1)) (St(tid1, R_2)) &
       predOrd t (St(tid2, I_1)) (St(tid1, R_1)) &
       predOrd t (St(tid2, I_3)) (St(tid1, R_3)) &
       predOrd t (St(tid2, I_2)) (St(tid2, I_3))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|NV ''ni'' tid1|), s(|AV ''I'' tid1|) |}
                       ( PK ( s(|AV ''R'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: R_ni_secrecy intro: event_predOrdI)
  next
    case (I_1_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT3'', Hash ( LN ''nr'' tid1 ) |}
                         ( LN ''kir'' tid1 ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: R_kir_secrecy intro: event_predOrdI)
    next
      case (I_3_enc tid3) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT2'', Hash ( LN ''ni'' tid3 ), LN ''nr'' tid1,
                              s(|AV ''R'' tid3|), LN ''kir'' tid1
                           |}
                           ( PK ( s(|AV ''I'' tid3|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: R_nr_secrecy intro: event_predOrdI)
      next
        case R_2_enc note facts = facts this[simplified]
        thus ?thesis by force
      qed
    qed
  qed
qed

lemma (in BKE_state) weak_atomicity:
  "complete (t,r,s) atomicAnn"
proof (cases rule: complete_atomicAnnI[completeness_cases_rule])
  case (I_2_kir t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state BKE t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT2'', Hash ( LN ''ni'' tid0 ), ?s'(|NV ''nr'' tid0|),
             ?s'(|AV ''R'' tid0|), ?s'(|NV ''kir'' tid0|)
          |}
          ( PK ( ?s'(|AV ''I'' tid0|) ) ) ")
  qed (insert facts, ((fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (I_2_nr t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state BKE t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT2'', Hash ( LN ''ni'' tid0 ), ?s'(|NV ''nr'' tid0|),
             ?s'(|AV ''R'' tid0|), ?s'(|NV ''kir'' tid0|)
          |}
          ( PK ( ?s'(|AV ''I'' tid0|) ) ) ")
  qed (insert facts, ((fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (R_1_ni t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state BKE t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT1'', ?s'(|NV ''ni'' tid0|), ?s'(|AV ''I'' tid0|) |}
          ( PK ( ?s'(|AV ''R'' tid0|) ) ) ")
  qed (insert facts, ((fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
qed

end