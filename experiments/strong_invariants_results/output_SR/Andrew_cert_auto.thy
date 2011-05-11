theory "Andrew_cert_auto"
imports
  "../ESPLogic"
begin

role I
where "I =
  [ Send ''1'' {| sLAV ''I'',
                  Enc {| sLC ''TT1'', sLN ''ni'' |} ( sK ''I'' ''R'' )
               |}
  , Send ''2'' ( Enc {| sLC ''TT2'',
                        Hash {| sLC ''TT1'', sLN ''ni'' |}, sLN ''nr''
                     |}
                     ( sK ''I'' ''R'' )
               )
  , Send ''3'' ( Enc {| sLC ''TT3'',
                        Hash {| sLC ''TT1'', sLN ''nr'' |}
                     |}
                     ( sK ''I'' ''R'' )
               )
  , Recv ''4'' ( Enc {| sLC ''TT4'', sLMV ''kIR'', sLMV ''nr2'' |}
                     ( sK ''I'' ''R'' )
               )
  ]"

role R
where "R =
  [ Recv ''1'' {| sLAV ''I'',
                  Enc {| sLC ''TT1'', sLMV ''ni'' |} ( sK ''I'' ''R'' )
               |}
  , Recv ''2'' ( Enc {| sLC ''TT2'',
                        Hash {| sLC ''TT1'', sLMV ''ni'' |}, sLMV ''nr''
                     |}
                     ( sK ''I'' ''R'' )
               )
  , Recv ''3'' ( Enc {| sLC ''TT3'',
                        Hash {| sLC ''TT1'', sLMV ''nr'' |}
                     |}
                     ( sK ''I'' ''R'' )
               )
  , Send ''4'' ( Enc {| sLC ''TT4'', sLN ''kIR'', sLN ''nr2'' |}
                     ( sK ''I'' ''R'' )
               )
  ]"

protocol Andrew
where "Andrew = { I, R }"

locale atomic_Andrew_state = atomic_state Andrew
locale Andrew_state = reachable_state Andrew

lemma (in atomic_Andrew_state) auto_I_k_I_R:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''R'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''R'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_Andrew_state) auto_R_k_I_R:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''R'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''R'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_Andrew_state) auto_R_sec_kIR:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "(tid0, R_4) : steps t"
    "LN ''kIR'' tid0 : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! " LN ''kIR'' tid0 ")
    case R_4_kIR note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_R_k_I_R intro: event_predOrdI)
  qed
qed

lemma (in atomic_Andrew_state) auto_I_sec_kIR:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "(tid0, I_4) : steps t"
    "s(|MV ''kIR'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT4'', s(|MV ''kIR'' tid0|), s(|MV ''nr2'' tid0|) |}
                       ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''R'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_I_k_I_R intro: event_predOrdI)
  next
    case (R_4_enc tid1) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_R_sec_kIR intro: event_predOrdI)
  qed
qed

lemma (in Andrew_state) weak_atomicity:
  "complete (t,r,s) atomicAnn"
proof (cases rule: complete_atomicAnnI[completeness_cases_rule])
  case (I_4_kIR t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state Andrew t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT4'', ?s'(|MV ''kIR'' tid0|), ?s'(|MV ''nr2'' tid0|)
          |}
          ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''R'' tid0|) ) ) ")
  qed (insert facts, ((fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (I_4_nr2 t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state Andrew t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT4'', ?s'(|MV ''kIR'' tid0|), ?s'(|MV ''nr2'' tid0|)
          |}
          ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''R'' tid0|) ) ) ")
  qed (insert facts, ((fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (R_1_ni t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state Andrew t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT1'', ?s'(|MV ''ni'' tid0|) |}
          ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''R'' tid0|) ) ) ")
  qed (insert facts, ((fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (R_2_nr t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state Andrew t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT2'', Hash {| LC ''TT1'', ?s'(|MV ''ni'' tid0|) |},
             ?s'(|MV ''nr'' tid0|)
          |}
          ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''R'' tid0|) ) ) ")
  qed (insert facts, ((fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
qed

lemma (in atomic_Andrew_state) I_sec_kIR:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "(tid0, I_4) : steps t"
    "s(|MV ''kIR'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis by (fastsimp dest: auto_I_sec_kIR intro: event_predOrdI)
qed

lemma (in atomic_Andrew_state) R_sec_kIR:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "(tid0, R_4) : steps t"
    "LN ''kIR'' tid0 : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis by (fastsimp dest: auto_R_sec_kIR intro: event_predOrdI)
qed

lemma (in atomic_Andrew_state) I_ni_agree:
  assumes facts:
    "roleMap r tid1 = Some I"
    "s(|AV ''I'' tid1|) ~: Compromised"
    "s(|AV ''R'' tid1|) ~: Compromised"
    "(tid1, I_4) : steps t"
  shows
    "? tid2.
       roleMap r tid2 = Some R &
       s(|AV ''I'' tid2|) = s(|AV ''I'' tid1|) &
       s(|AV ''R'' tid2|) = s(|AV ''R'' tid1|) &
       s(|MV ''kIR'' tid1|) = LN ''kIR'' tid2 &
       s(|MV ''nr2'' tid1|) = LN ''nr2'' tid2"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT4'', s(|MV ''kIR'' tid1|), s(|MV ''nr2'' tid1|) |}
                       ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''R'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_I_k_I_R intro: event_predOrdI)
  next
    case (R_4_enc tid2) note facts = facts this[simplified]
    thus ?thesis by force
  qed
qed

lemma (in atomic_Andrew_state) R_ni_agree:
  assumes facts:
    "roleMap r tid1 = Some R"
    "s(|AV ''I'' tid1|) ~: Compromised"
    "s(|AV ''R'' tid1|) ~: Compromised"
    "(tid1, R_4) : steps t"
  shows
    "? tid2.
       roleMap r tid2 = Some I &
       s(|AV ''I'' tid2|) = s(|AV ''I'' tid1|) &
       s(|AV ''R'' tid2|) = s(|AV ''R'' tid1|) &
       s(|MV ''ni'' tid1|) = LN ''ni'' tid2 &
       s(|MV ''nr'' tid1|) = LN ''nr'' tid2"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT2'', Hash {| LC ''TT1'', s(|MV ''ni'' tid1|) |},
                          s(|MV ''nr'' tid1|)
                       |}
                       ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''R'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_R_k_I_R intro: event_predOrdI)
  next
    case (I_2_enc tid2) note facts = facts this[simplified]
    thus ?thesis by force
  qed
qed

end