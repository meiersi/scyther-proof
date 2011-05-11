theory WMF_cert_auto
imports
  "../ESPLogic"
begin

role I
where "I =
  [ Send ''1'' {| sLAV ''I'',
                  Enc {| sLC ''step1'', sLN ''TimeI'', sLAV ''R'', sLN ''kIR'' |}
                      ( sK ''I'' ''S'' )
               |}
  ]"

role R
where "R =
  [ Recv ''2'' ( Enc {| sLC ''step2'', sLNV ''TimeS'', sLAV ''I'',
                        sLNV ''kIR''
                     |}
                     ( sK ''R'' ''S'' )
               )
  ]"

role S
where "S =
  [ Recv ''1'' {| sLAV ''I'',
                  Enc {| sLC ''step1'', sLNV ''TimeI'', sLAV ''R'', sLNV ''kIR'' |}
                      ( sK ''I'' ''S'' )
               |}
  , Send ''2'' ( Enc {| sLC ''step2'', sLN ''TimeS'', sLAV ''I'',
                        sLNV ''kIR''
                     |}
                     ( sK ''R'' ''S'' )
               )
  ]"

protocol WMF
where "WMF = { I, R, S }"

locale atomic_WMF_state = atomic_state WMF
locale WMF_state = reachable_state WMF

lemma (in atomic_WMF_state) I_ltk_I_S_sec:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_WMF_state) I_ltk_R_S_sec:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_WMF_state) R_ltk_I_S_sec:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_WMF_state) R_ltk_R_S_sec:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_WMF_state) I_kIR_sec:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "LN ''kIR'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''kIR'' tid0 ")
  case I_1_kIR note facts = facts this[simplified]
  thus ?thesis by (fastsimp dest: I_ltk_I_S_sec intro: event_predOrdI)
next
  case (S_2_kIR tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''step1'', s(|NV ''TimeI'' tid1|), s(|AV ''R'' tid1|),
                          LN ''kIR'' tid0
                       |}
                       ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
    case I_1_enc note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: I_ltk_R_S_sec intro: event_predOrdI)
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_WMF_state) S_kIR_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, S_1) : steps t"
    "s(|NV ''kIR'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''step1'', s(|NV ''TimeI'' tid0|), s(|AV ''R'' tid0|),
                          s(|NV ''kIR'' tid0|)
                       |}
                       ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (I_1_enc tid1) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: I_kIR_sec intro: event_predOrdI)
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_WMF_state) R_kIR_sec:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, R_2) : steps t"
    "s(|NV ''kIR'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''step2'', s(|NV ''TimeS'' tid0|), s(|AV ''I'' tid0|),
                          s(|NV ''kIR'' tid0|)
                       |}
                       ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: R_ltk_R_S_sec intro: event_predOrdI)
  next
    case (S_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: S_kIR_sec intro: event_predOrdI)
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_WMF_state) R_ni_synch:
  assumes facts:
    "roleMap r tid2 = Some R"
    "s(|AV ''I'' tid2|) ~: Compromised"
    "s(|AV ''R'' tid2|) ~: Compromised"
    "s(|AV ''S'' tid2|) ~: Compromised"
    "(tid2, R_2) : steps t"
  shows
    "? tid1 tid3.
       roleMap r tid1 = Some I &
       roleMap r tid3 = Some S &
       s(|AV ''I'' tid2|) = s(|AV ''I'' tid1|) &
       s(|AV ''I'' tid3|) = s(|AV ''I'' tid1|) &
       s(|AV ''R'' tid2|) = s(|AV ''R'' tid1|) &
       s(|AV ''R'' tid3|) = s(|AV ''R'' tid1|) &
       s(|AV ''S'' tid2|) = s(|AV ''S'' tid1|) &
       s(|AV ''S'' tid3|) = s(|AV ''S'' tid1|) &
       s(|NV ''TimeI'' tid3|) = LN ''TimeI'' tid1 &
       s(|NV ''TimeS'' tid2|) = LN ''TimeS'' tid3 &
       s(|NV ''kIR'' tid2|) = LN ''kIR'' tid1 &
       s(|NV ''kIR'' tid3|) = LN ''kIR'' tid1 &
       predOrd t (St(tid1, I_1)) (St(tid3, S_1)) &
       predOrd t (St(tid3, S_2)) (St(tid2, R_2)) &
       predOrd t (St(tid3, S_1)) (St(tid3, S_2))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''step2'', s(|NV ''TimeS'' tid2|), s(|AV ''I'' tid2|),
                          s(|NV ''kIR'' tid2|)
                       |}
                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: R_ltk_R_S_sec intro: event_predOrdI)
  next
    case (S_2_enc tid3) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''step1'', s(|NV ''TimeI'' tid3|), s(|AV ''R'' tid2|),
                            s(|NV ''kIR'' tid2|)
                         |}
                         ( K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: R_ltk_I_S_sec intro: event_predOrdI)
    next
      case (I_1_enc tid4) note facts = facts this[simplified]
      thus ?thesis by force
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in WMF_state) weak_atomicity:
  "complete (t,r,s) atomicAnn"
proof (cases rule: complete_atomicAnnI[completeness_cases_rule])
  case (R_2_TimeS t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state WMF t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''step2'', ?s'(|NV ''TimeS'' tid0|),
             ?s'(|AV ''I'' tid0|), ?s'(|NV ''kIR'' tid0|)
          |}
          ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (R_2_kIR t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state WMF t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''step2'', ?s'(|NV ''TimeS'' tid0|),
             ?s'(|AV ''I'' tid0|), ?s'(|NV ''kIR'' tid0|)
          |}
          ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
    case (S_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''step1'', s(|NV ''TimeI'' tid1|), ?s'(|AV ''R'' tid0|),
                            ?s'(|NV ''kIR'' tid0|)
                         |}
                         ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
    qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (S_1_TimeI t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state WMF t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''step1'', ?s'(|NV ''TimeI'' tid0|),
             ?s'(|AV ''R'' tid0|), ?s'(|NV ''kIR'' tid0|)
          |}
          ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (S_1_kIR t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state WMF t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''step1'', ?s'(|NV ''TimeI'' tid0|),
             ?s'(|AV ''R'' tid0|), ?s'(|NV ''kIR'' tid0|)
          |}
          ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
qed

end