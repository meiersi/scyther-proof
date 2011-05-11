theory "WideMouthFrog_cert_auto"
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
  [ Recv ''2'' ( Enc {| sLC ''step2'', sLMV ''TimeS'', sLAV ''I'',
                        sLMV ''kIR''
                     |}
                     ( sK ''R'' ''S'' )
               )
  ]"

role S
where "S =
  [ Recv ''1'' {| sLAV ''I'',
                  Enc {| sLC ''step1'', sLMV ''TimeI'', sLAV ''R'', sLMV ''kIR'' |}
                      ( sK ''I'' ''S'' )
               |}
  , Send ''2'' ( Enc {| sLC ''step2'', sLN ''TimeS'', sLAV ''I'',
                        sLMV ''kIR''
                     |}
                     ( sK ''R'' ''S'' )
               )
  ]"

protocol WMF
where "WMF = { I, R, S }"

locale atomic_WMF_state = atomic_state WMF
locale WMF_state = reachable_state WMF

lemma (in atomic_WMF_state) auto_I_k_I_S:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_WMF_state) auto_I_k_R_S:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_WMF_state) auto_R_k_I_S:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_WMF_state) auto_R_k_R_S:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_WMF_state) auto_S_k_I_S:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_WMF_state) auto_I_sec_kIR:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, I_1) : steps t"
    "LN ''kIR'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''kIR'' tid0 ")
  case I_1_kIR note facts = facts this[simplified]
  thus ?thesis by (fastsimp dest: auto_I_k_I_S intro: event_predOrdI)
next
  case (S_2_kIR tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''step1'', s(|MV ''TimeI'' tid1|), s(|AV ''R'' tid1|),
                          LN ''kIR'' tid0
                       |}
                       ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
    case I_1_enc note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_I_k_R_S intro: event_predOrdI)
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_WMF_state) auto_S_sec_kIR:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, S_1) : steps t"
    "s(|MV ''kIR'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''step1'', s(|MV ''TimeI'' tid0|), s(|AV ''R'' tid0|),
                          s(|MV ''kIR'' tid0|)
                       |}
                       ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_S_k_I_S intro: event_predOrdI)
  next
    case (I_1_enc tid1) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_I_sec_kIR intro: event_predOrdI)
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_WMF_state) auto_R_sec_kIR:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, R_2) : steps t"
    "s(|MV ''kIR'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''step2'', s(|MV ''TimeS'' tid0|), s(|AV ''I'' tid0|),
                          s(|MV ''kIR'' tid0|)
                       |}
                       ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_R_k_R_S intro: event_predOrdI)
  next
    case (S_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_S_sec_kIR intro: event_predOrdI)
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
      Enc {| LC ''step2'', ?s'(|MV ''TimeS'' tid0|),
             ?s'(|AV ''I'' tid0|), ?s'(|MV ''kIR'' tid0|)
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
      Enc {| LC ''step2'', ?s'(|MV ''TimeS'' tid0|),
             ?s'(|AV ''I'' tid0|), ?s'(|MV ''kIR'' tid0|)
          |}
          ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
    case (S_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''step1'', s(|MV ''TimeI'' tid1|), ?s'(|AV ''R'' tid0|),
                            ?s'(|MV ''kIR'' tid0|)
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
      Enc {| LC ''step1'', ?s'(|MV ''TimeI'' tid0|),
             ?s'(|AV ''R'' tid0|), ?s'(|MV ''kIR'' tid0|)
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
      Enc {| LC ''step1'', ?s'(|MV ''TimeI'' tid0|),
             ?s'(|AV ''R'' tid0|), ?s'(|MV ''kIR'' tid0|)
          |}
          ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
qed

lemma (in atomic_WMF_state) I_kIR_sec:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, I_1) : steps t"
    "LN ''kIR'' tid0 : knows t"
  shows "False"
using facts by (fastsimp dest: auto_I_sec_kIR intro: event_predOrdI)

lemma (in atomic_WMF_state) R_kIR_sec:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, R_2) : steps t"
    "s(|MV ''kIR'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis by (fastsimp dest: auto_R_sec_kIR intro: event_predOrdI)
qed

lemma (in atomic_WMF_state) R_ni_agree:
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
       s(|MV ''TimeI'' tid3|) = LN ''TimeI'' tid1 &
       s(|MV ''TimeS'' tid2|) = LN ''TimeS'' tid3 &
       s(|MV ''kIR'' tid2|) = LN ''kIR'' tid1 &
       s(|MV ''kIR'' tid3|) = LN ''kIR'' tid1"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''step2'', s(|MV ''TimeS'' tid2|), s(|AV ''I'' tid2|),
                          s(|MV ''kIR'' tid2|)
                       |}
                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_R_k_R_S intro: event_predOrdI)
  next
    case (S_2_enc tid3) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''step1'', s(|MV ''TimeI'' tid3|), s(|AV ''R'' tid2|),
                            s(|MV ''kIR'' tid2|)
                         |}
                         ( K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: auto_R_k_I_S intro: event_predOrdI)
    next
      case (I_1_enc tid4) note facts = facts this[simplified]
      thus ?thesis by force
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

end