theory "Denning-Sacco_cert_auto"
imports
  "../ESPLogic"
begin

role I
where "I =
  [ Send ''1'' {| sLAV ''I'', sLAV ''R'' |}
  , Recv ''2'' ( Enc {| sLC ''TT1'', sLAV ''R'', sLMV ''kIR'',
                        sLMV ''T'',
                        Enc {| sLC ''TT2'', sLAV ''I'', sLMV ''SomekIR'', sLMV ''SomeT'' |}
                            ( sK ''R'' ''S'' )
                     |}
                     ( sK ''I'' ''S'' )
               )
  , Send ''3'' ( Enc {| sLC ''TT2'', sLAV ''I'', sLMV ''SomekIR'',
                        sLMV ''SomeT''
                     |}
                     ( sK ''R'' ''S'' )
               )
  , Recv ''4'' ( Enc {| sLC ''TT3'', sLMV ''Payload'' |}
                     ( sLMV ''kIR'' )
               )
  ]"

role R
where "R =
  [ Recv ''3'' ( Enc {| sLC ''TT2'', sLAV ''I'', sLMV ''kIR'',
                        sLMV ''T''
                     |}
                     ( sK ''R'' ''S'' )
               )
  , Send ''4'' ( Enc {| sLC ''TT3'', sLN ''Payload'' |}
                     ( sLMV ''kIR'' )
               )
  ]"

role S
where "S =
  [ Recv ''1'' {| sLAV ''I'', sLAV ''R'' |}
  , Send ''2'' ( Enc {| sLC ''TT1'', sLAV ''R'', sLN ''kIR'',
                        sLN ''T'',
                        Enc {| sLC ''TT2'', sLAV ''I'', sLN ''kIR'', sLN ''T'' |}
                            ( sK ''R'' ''S'' )
                     |}
                     ( sK ''I'' ''S'' )
               )
  ]"

protocol DenningSacco
where "DenningSacco = { I, R, S }"

locale atomic_DenningSacco_state = atomic_state DenningSacco
locale DenningSacco_state = reachable_state DenningSacco

lemma (in atomic_DenningSacco_state) auto_I_k_I_S:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_DenningSacco_state) auto_I_k_R_S:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_DenningSacco_state) auto_R_k_I_S:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_DenningSacco_state) auto_R_k_R_S:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_DenningSacco_state) auto_S_k_I_S:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_DenningSacco_state) auto_S_sec_kIR:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, S_2) : steps t"
    "LN ''kIR'' tid0 : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! " LN ''kIR'' tid0 ")
    case (I_3_SomekIR tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', s(|AV ''R'' tid1|), s(|MV ''kIR'' tid1|),
                            s(|MV ''T'' tid1|),
                            Enc {| LC ''TT2'', s(|AV ''I'' tid1|), LN ''kIR'' tid0,
                                   s(|MV ''SomeT'' tid1|)
                                |}
                                ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) )
                         |}
                         ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
      case S_2_enc note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: auto_I_k_R_S intro: event_predOrdI)
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (I_3_SomeT tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', s(|AV ''R'' tid1|), s(|MV ''kIR'' tid1|),
                            s(|MV ''T'' tid1|),
                            Enc {| LC ''TT2'', s(|AV ''I'' tid1|), s(|MV ''SomekIR'' tid1|),
                                   LN ''kIR'' tid0
                                |}
                                ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) )
                         |}
                         ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case S_2_kIR note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_S_k_I_S intro: event_predOrdI)
  next
    case S_2_kIR_1 note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_S_k_I_S intro: event_predOrdI)
  qed
qed

lemma (in atomic_DenningSacco_state) auto_R_sec_Payload:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, R_4) : steps t"
    "LN ''Payload'' tid0 : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! " LN ''Payload'' tid0 ")
    case (I_3_SomekIR tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', s(|AV ''R'' tid1|), s(|MV ''kIR'' tid1|),
                            s(|MV ''T'' tid1|),
                            Enc {| LC ''TT2'', s(|AV ''I'' tid1|), LN ''Payload'' tid0,
                                   s(|MV ''SomeT'' tid1|)
                                |}
                                ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) )
                         |}
                         ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (I_3_SomeT tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', s(|AV ''R'' tid1|), s(|MV ''kIR'' tid1|),
                            s(|MV ''T'' tid1|),
                            Enc {| LC ''TT2'', s(|AV ''I'' tid1|), s(|MV ''SomekIR'' tid1|),
                                   LN ''Payload'' tid0
                                |}
                                ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) )
                         |}
                         ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case R_4_Payload note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', s(|AV ''I'' tid0|), s(|MV ''kIR'' tid0|),
                            s(|MV ''T'' tid0|)
                         |}
                         ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: auto_R_k_R_S intro: event_predOrdI)
    next
      case (I_3_enc tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', s(|AV ''R'' tid0|), s(|MV ''kIR'' tid2|),
                              s(|MV ''T'' tid2|),
                              Enc {| LC ''TT2'', s(|AV ''I'' tid0|), s(|MV ''SomekIR'' tid2|),
                                     s(|MV ''SomeT'' tid2|)
                                  |}
                                  ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) )
                           |}
                           ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
        case (S_2_enc tid3) note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: auto_S_sec_kIR intro: event_predOrdI)
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_2_enc tid2) note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: auto_R_k_I_S intro: event_predOrdI)
    qed (insert facts, ((clarsimp, order?))+)?
  qed
qed

lemma (in atomic_DenningSacco_state) auto_I_sec_Payload:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, I_4) : steps t"
    "s(|MV ''Payload'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|AV ''R'' tid0|), s(|MV ''kIR'' tid0|),
                          s(|MV ''T'' tid0|),
                          Enc {| LC ''TT2'', s(|AV ''I'' tid0|), s(|MV ''SomekIR'' tid0|),
                                 s(|MV ''SomeT'' tid0|)
                              |}
                              ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) )
                       |}
                       ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_I_k_I_S intro: event_predOrdI)
  next
    case (S_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT3'', s(|MV ''Payload'' tid0|) |}
                         ( LN ''kIR'' tid1 ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: auto_S_sec_kIR intro: event_predOrdI)
    next
      case (R_4_enc tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT2'', s(|AV ''I'' tid2|), LN ''kIR'' tid1,
                              s(|MV ''T'' tid2|)
                           |}
                           ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: auto_S_sec_kIR intro: event_predOrdI)
      next
        case (I_3_enc tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT1'', s(|AV ''R'' tid2|), s(|MV ''kIR'' tid3|),
                                s(|MV ''T'' tid3|),
                                Enc {| LC ''TT2'', s(|AV ''I'' tid2|), LN ''kIR'' tid1,
                                       s(|MV ''SomeT'' tid3|)
                                    |}
                                    ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) )
                             |}
                             ( K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
          case S_2_enc note facts = facts this[simplified]
          thus ?thesis by (fastsimp dest: auto_R_sec_Payload intro: event_predOrdI)
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case S_2_enc note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: auto_I_k_I_S intro: event_predOrdI)
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in DenningSacco_state) weak_atomicity:
  "complete (t,r,s) atomicAnn"
proof (cases rule: complete_atomicAnnI[completeness_cases_rule])
  case (I_2_SomeT t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state DenningSacco t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT1'', ?s'(|AV ''R'' tid0|), ?s'(|MV ''kIR'' tid0|),
             ?s'(|MV ''T'' tid0|),
             Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|),
                    ?s'(|MV ''SomekIR'' tid0|), ?s'(|MV ''SomeT'' tid0|)
                 |}
                 ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) )
          |}
          ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|),
                            ?s'(|MV ''SomekIR'' tid0|), ?s'(|MV ''SomeT'' tid0|)
                         |}
                         ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
      case (I_3_enc tid1) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', ?s'(|AV ''R'' tid0|), s(|MV ''kIR'' tid1|),
                              s(|MV ''T'' tid1|),
                              Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|),
                                     ?s'(|MV ''SomekIR'' tid0|), ?s'(|MV ''SomeT'' tid0|)
                                  |}
                                  ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) )
                           |}
                           ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
      qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
    qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (I_2_SomekIR t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state DenningSacco t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT1'', ?s'(|AV ''R'' tid0|), ?s'(|MV ''kIR'' tid0|),
             ?s'(|MV ''T'' tid0|),
             Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|),
                    ?s'(|MV ''SomekIR'' tid0|), ?s'(|MV ''SomeT'' tid0|)
                 |}
                 ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) )
          |}
          ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|),
                            ?s'(|MV ''SomekIR'' tid0|), ?s'(|MV ''SomeT'' tid0|)
                         |}
                         ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
      case (I_3_enc tid1) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', ?s'(|AV ''R'' tid0|), s(|MV ''kIR'' tid1|),
                              s(|MV ''T'' tid1|),
                              Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|),
                                     ?s'(|MV ''SomekIR'' tid0|), ?s'(|MV ''SomeT'' tid0|)
                                  |}
                                  ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) )
                           |}
                           ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
      qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
    qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (I_2_T t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state DenningSacco t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT1'', ?s'(|AV ''R'' tid0|), ?s'(|MV ''kIR'' tid0|),
             ?s'(|MV ''T'' tid0|),
             Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|),
                    ?s'(|MV ''SomekIR'' tid0|), ?s'(|MV ''SomeT'' tid0|)
                 |}
                 ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) )
          |}
          ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (I_2_kIR t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state DenningSacco t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT1'', ?s'(|AV ''R'' tid0|), ?s'(|MV ''kIR'' tid0|),
             ?s'(|MV ''T'' tid0|),
             Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|),
                    ?s'(|MV ''SomekIR'' tid0|), ?s'(|MV ''SomeT'' tid0|)
                 |}
                 ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) )
          |}
          ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (I_4_Payload t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state DenningSacco t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT3'', ?s'(|MV ''Payload'' tid0|) |}
          ( ?s'(|MV ''kIR'' tid0|) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (R_3_T t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state DenningSacco t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|), ?s'(|MV ''kIR'' tid0|),
             ?s'(|MV ''T'' tid0|)
          |}
          ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (R_3_kIR t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state DenningSacco t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|), ?s'(|MV ''kIR'' tid0|),
             ?s'(|MV ''T'' tid0|)
          |}
          ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
qed

lemma (in atomic_DenningSacco_state) R_Payload_secrecy:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "LN ''Payload'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''Payload'' tid0 ")
  case (I_3_SomekIR tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|AV ''R'' tid1|), s(|MV ''kIR'' tid1|),
                          s(|MV ''T'' tid1|),
                          Enc {| LC ''TT2'', s(|AV ''I'' tid1|), LN ''Payload'' tid0,
                                 s(|MV ''SomeT'' tid1|)
                              |}
                              ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) )
                       |}
                       ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (I_3_SomeT tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|AV ''R'' tid1|), s(|MV ''kIR'' tid1|),
                          s(|MV ''T'' tid1|),
                          Enc {| LC ''TT2'', s(|AV ''I'' tid1|), s(|MV ''SomekIR'' tid1|),
                                 LN ''Payload'' tid0
                              |}
                              ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) )
                       |}
                       ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
next
  case R_4_Payload note facts = facts this[simplified]
  thus ?thesis by (fastsimp dest: auto_R_sec_Payload intro: event_predOrdI)
qed

lemma (in atomic_DenningSacco_state) I_Payload_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, I_4) : steps t"
    "s(|MV ''Payload'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis by (fastsimp dest: auto_I_sec_Payload intro: event_predOrdI)
qed

lemma (in atomic_DenningSacco_state) I_auth:
  assumes facts:
    "roleMap r tid1 = Some I"
    "s(|AV ''I'' tid1|) ~: Compromised"
    "s(|AV ''R'' tid1|) ~: Compromised"
    "s(|AV ''S'' tid1|) ~: Compromised"
    "(tid1, I_4) : steps t"
  shows
    "? tid2 tid3.
       roleMap r tid2 = Some R &
       roleMap r tid3 = Some S &
       s(|AV ''I'' tid2|) = s(|AV ''I'' tid1|) &
       s(|AV ''I'' tid3|) = s(|AV ''I'' tid1|) &
       s(|AV ''R'' tid2|) = s(|AV ''R'' tid1|) &
       s(|AV ''R'' tid3|) = s(|AV ''R'' tid1|) &
       s(|AV ''S'' tid2|) = s(|AV ''S'' tid1|) &
       s(|AV ''S'' tid3|) = s(|AV ''S'' tid1|) &
       s(|MV ''Payload'' tid1|) = LN ''Payload'' tid2 &
       s(|MV ''T'' tid1|) = LN ''T'' tid3 &
       s(|MV ''T'' tid2|) = LN ''T'' tid3 &
       s(|MV ''kIR'' tid1|) = LN ''kIR'' tid3 &
       s(|MV ''kIR'' tid2|) = LN ''kIR'' tid3"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|AV ''R'' tid1|), s(|MV ''kIR'' tid1|),
                          s(|MV ''T'' tid1|),
                          Enc {| LC ''TT2'', s(|AV ''I'' tid1|), s(|MV ''SomekIR'' tid1|),
                                 s(|MV ''SomeT'' tid1|)
                              |}
                              ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) )
                       |}
                       ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_I_k_I_S intro: event_predOrdI)
  next
    case (S_2_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT3'', s(|MV ''Payload'' tid1|) |}
                         ( LN ''kIR'' tid2 ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: auto_S_sec_kIR intro: event_predOrdI)
    next
      case (R_4_enc tid3) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT2'', s(|AV ''I'' tid3|), LN ''kIR'' tid2,
                              s(|MV ''T'' tid3|)
                           |}
                           ( K ( s(|AV ''R'' tid3|) ) ( s(|AV ''S'' tid3|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: auto_S_sec_kIR intro: event_predOrdI)
      next
        case (I_3_enc tid4) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT1'', s(|AV ''R'' tid3|), s(|MV ''kIR'' tid4|),
                                s(|MV ''T'' tid4|),
                                Enc {| LC ''TT2'', s(|AV ''I'' tid3|), LN ''kIR'' tid2,
                                       s(|MV ''SomeT'' tid4|)
                                    |}
                                    ( K ( s(|AV ''R'' tid3|) ) ( s(|AV ''S'' tid3|) ) )
                             |}
                             ( K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid3|) ) ) ")
          case S_2_enc note facts = facts this[simplified]
          thus ?thesis by force
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case S_2_enc note facts = facts this[simplified]
        thus ?thesis by force
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_DenningSacco_state) R_auth:
  assumes facts:
    "roleMap r tid2 = Some R"
    "s(|AV ''I'' tid2|) ~: Compromised"
    "s(|AV ''R'' tid2|) ~: Compromised"
    "s(|AV ''S'' tid2|) ~: Compromised"
    "(tid2, R_4) : steps t"
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
       s(|MV ''T'' tid1|) = LN ''T'' tid3 &
       s(|MV ''T'' tid2|) = LN ''T'' tid3 &
       s(|MV ''kIR'' tid1|) = LN ''kIR'' tid3 &
       s(|MV ''kIR'' tid2|) = LN ''kIR'' tid3"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT2'', s(|AV ''I'' tid2|), s(|MV ''kIR'' tid2|),
                          s(|MV ''T'' tid2|)
                       |}
                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_R_k_R_S intro: event_predOrdI)
  next
    case (I_3_enc tid3) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', s(|AV ''R'' tid2|), s(|MV ''kIR'' tid3|),
                            s(|MV ''T'' tid3|),
                            Enc {| LC ''TT2'', s(|AV ''I'' tid2|), s(|MV ''SomekIR'' tid3|),
                                   s(|MV ''SomeT'' tid3|)
                                |}
                                ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) )
                         |}
                         ( K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      case (S_2_enc tid4) note facts = facts this[simplified]
      thus ?thesis by force
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_2_enc tid3) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_R_k_I_S intro: event_predOrdI)
  qed (insert facts, ((clarsimp, order?))+)?
qed

end