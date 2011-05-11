theory "Bilateral-Key_Exchange_cert_auto"
imports
  "../ESPLogic"
begin

role I
where "I =
  [ Send ''1'' {| sLAV ''I'',
                  Enc {| sLC ''TT1'', sLN ''ni'', sLAV ''I'' |} ( sPK ''R'' )
               |}
  , Recv ''2'' ( Enc {| sLC ''TT2'', Hash ( sLN ''ni'' ),
                        sLMV ''nr'', sLAV ''R'', sLMV ''kir''
                     |}
                     ( sPK ''I'' )
               )
  , Send ''3'' ( Enc {| sLC ''TT3'', Hash ( sLMV ''nr'' ) |}
                     ( sLMV ''kir'' )
               )
  ]"

role R
where "R =
  [ Recv ''1'' {| sLAV ''I'',
                  Enc {| sLC ''TT1'', sLMV ''ni'', sLAV ''I'' |} ( sPK ''R'' )
               |}
  , Send ''2'' ( Enc {| sLC ''TT2'', Hash ( sLMV ''ni'' ),
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

lemma (in atomic_BKE_state) auto_I_sk_I:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "SK ( s(|AV ''I'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_BKE_state) auto_I_sk_R:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "SK ( s(|AV ''R'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! " SK ( s(|AV ''R'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_BKE_state) auto_R_sk_I:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "SK ( s(|AV ''I'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_BKE_state) auto_I_sec_ni:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "(tid0, I_1) : steps t"
    "LN ''ni'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''ni'' tid0 ")
  case I_1_ni note facts = facts this[simplified]
  thus ?thesis by (fastsimp dest: auto_I_sk_R intro: event_predOrdI)
qed

lemma (in atomic_BKE_state) auto_R_sec_kir:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "(tid0, R_2) : steps t"
    "LN ''kir'' tid0 : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! " LN ''kir'' tid0 ")
    case R_2_kir note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_R_sk_I intro: event_predOrdI)
  qed
qed

lemma (in atomic_BKE_state) auto_I_sec_kir:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "(tid0, I_2) : steps t"
    "s(|MV ''kir'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT2'', Hash ( LN ''ni'' tid0 ), s(|MV ''nr'' tid0|),
                          s(|AV ''R'' tid0|), s(|MV ''kir'' tid0|)
                       |}
                       ( PK ( s(|AV ''I'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! " Hash ( LN ''ni'' tid0 ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: auto_I_sec_ni intro: event_predOrdI)
    next
      case (I_3_hash tid1) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT2'', Hash ( LN ''ni'' tid1 ), LN ''ni'' tid0,
                              s(|AV ''R'' tid1|), s(|MV ''kir'' tid1|)
                           |}
                           ( PK ( s(|AV ''I'' tid1|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: auto_I_sec_ni intro: event_predOrdI)
      qed
    next
      case (R_2_hash tid1) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', LN ''ni'' tid0, s(|AV ''I'' tid1|) |}
                           ( PK ( s(|AV ''R'' tid1|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: auto_I_sec_ni intro: event_predOrdI)
      next
        case I_1_enc note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: auto_I_sk_I intro: event_predOrdI)
      qed
    qed
  next
    case (R_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_R_sec_kir intro: event_predOrdI)
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
      Enc {| LC ''TT2'', Hash ( LN ''ni'' tid0 ), ?s'(|MV ''nr'' tid0|),
             ?s'(|AV ''R'' tid0|), ?s'(|MV ''kir'' tid0|)
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
      Enc {| LC ''TT2'', Hash ( LN ''ni'' tid0 ), ?s'(|MV ''nr'' tid0|),
             ?s'(|AV ''R'' tid0|), ?s'(|MV ''kir'' tid0|)
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
      Enc {| LC ''TT1'', ?s'(|MV ''ni'' tid0|), ?s'(|AV ''I'' tid0|) |}
          ( PK ( ?s'(|AV ''R'' tid0|) ) ) ")
  qed (insert facts, ((fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
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
  thus ?thesis by (fastsimp dest: auto_R_sk_I intro: event_predOrdI)
qed

lemma (in atomic_BKE_state) I_kir_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "(tid0, I_2) : steps t"
    "s(|MV ''kir'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis by (fastsimp dest: auto_I_sec_kir intro: event_predOrdI)
qed

lemma (in atomic_BKE_state) I_ni_auth:
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
       s(|MV ''kir'' tid1|) = LN ''kir'' tid2 &
       s(|MV ''ni'' tid2|) = LN ''ni'' tid1 &
       s(|MV ''nr'' tid1|) = LN ''nr'' tid2"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT2'', Hash ( LN ''ni'' tid1 ), s(|MV ''nr'' tid1|),
                          s(|AV ''R'' tid1|), s(|MV ''kir'' tid1|)
                       |}
                       ( PK ( s(|AV ''I'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_I_sec_kir intro: event_predOrdI)
  next
    case (R_2_enc tid2) note facts = facts this[simplified]
    thus ?thesis by force
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
       s(|MV ''kir'' tid2|) = LN ''kir'' tid1 &
       s(|MV ''ni'' tid1|) = LN ''ni'' tid2 &
       s(|MV ''nr'' tid2|) = LN ''nr'' tid1"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT3'', Hash ( LN ''nr'' tid1 ) |}
                       ( LN ''kir'' tid1 ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_R_sec_kir intro: event_predOrdI)
  next
    case (I_3_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', Hash ( LN ''ni'' tid2 ), LN ''nr'' tid1,
                            s(|AV ''R'' tid2|), LN ''kir'' tid1
                         |}
                         ( PK ( s(|AV ''I'' tid2|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: auto_R_sec_kir intro: event_predOrdI)
    next
      case R_2_enc note facts = facts this[simplified]
      thus ?thesis by force
    qed
  qed
qed

end