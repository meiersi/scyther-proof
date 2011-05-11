theory DenningSacco_cert_auto
imports
  "../ESPLogic"
begin

role I
where "I =
  [ Send ''1'' {| sLAV ''I'', sLAV ''R'' |}
  , Recv ''2'' ( Enc {| sLC ''TT1'', sLAV ''R'', sLNV ''kIR'',
                        sLNV ''T'',
                        Enc {| sLC ''TT2'', sLAV ''I'', sLNV ''SomekIR'', sLNV ''SomeT'' |}
                            ( sK ''R'' ''S'' )
                     |}
                     ( sK ''I'' ''S'' )
               )
  , Send ''3'' ( Enc {| sLC ''TT2'', sLAV ''I'', sLNV ''SomekIR'',
                        sLNV ''SomeT''
                     |}
                     ( sK ''R'' ''S'' )
               )
  , Recv ''4'' ( Enc {| sLC ''TT3'', sLNV ''Payload'' |}
                     ( sLNV ''kIR'' )
               )
  ]"

role R
where "R =
  [ Recv ''3'' ( Enc {| sLC ''TT2'', sLAV ''I'', sLNV ''kIR'',
                        sLNV ''T''
                     |}
                     ( sK ''R'' ''S'' )
               )
  , Send ''4'' ( Enc {| sLC ''TT3'', sLN ''Payload'' |}
                     ( sLNV ''kIR'' )
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

lemma (in atomic_DenningSacco_state) I_ltk_I_S_sec:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_DenningSacco_state) I_ltk_R_S_sec:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_DenningSacco_state) R_ltk_I_S_sec:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_DenningSacco_state) R_ltk_R_S_sec:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_DenningSacco_state) S_ltk_I_S_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_DenningSacco_state) S_ltk_R_S_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_DenningSacco_state) S_kIR_secrecy:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "LN ''kIR'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''kIR'' tid0 ")
  case (I_3_SomekIR tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|AV ''R'' tid1|), s(|NV ''kIR'' tid1|),
                          s(|NV ''T'' tid1|),
                          Enc {| LC ''TT2'', s(|AV ''I'' tid1|), LN ''kIR'' tid0,
                                 s(|NV ''SomeT'' tid1|)
                              |}
                              ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) )
                       |}
                       ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
    case S_2_enc note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: I_ltk_R_S_sec intro: event_predOrdI)
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (I_3_SomeT tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|AV ''R'' tid1|), s(|NV ''kIR'' tid1|),
                          s(|NV ''T'' tid1|),
                          Enc {| LC ''TT2'', s(|AV ''I'' tid1|), s(|NV ''SomekIR'' tid1|),
                                 LN ''kIR'' tid0
                              |}
                              ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) )
                       |}
                       ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
next
  case S_2_kIR note facts = facts this[simplified]
  thus ?thesis by (fastsimp dest: S_ltk_I_S_sec intro: event_predOrdI)
next
  case S_2_kIR_1 note facts = facts this[simplified]
  thus ?thesis by (fastsimp dest: S_ltk_I_S_sec intro: event_predOrdI)
qed

lemma (in atomic_DenningSacco_state) I_kIR_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, I_2) : steps t"
    "s(|NV ''kIR'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|AV ''R'' tid0|), s(|NV ''kIR'' tid0|),
                          s(|NV ''T'' tid0|),
                          Enc {| LC ''TT2'', s(|AV ''I'' tid0|), s(|NV ''SomekIR'' tid0|),
                                 s(|NV ''SomeT'' tid0|)
                              |}
                              ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) )
                       |}
                       ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: I_ltk_I_S_sec intro: event_predOrdI)
  next
    case (S_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: S_kIR_secrecy intro: event_predOrdI)
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_DenningSacco_state) R_kIR_secrecy:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, R_3) : steps t"
    "s(|NV ''kIR'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT2'', s(|AV ''I'' tid0|), s(|NV ''kIR'' tid0|),
                          s(|NV ''T'' tid0|)
                       |}
                       ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: R_ltk_R_S_sec intro: event_predOrdI)
  next
    case (I_3_enc tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', s(|AV ''R'' tid0|), s(|NV ''kIR'' tid1|),
                            s(|NV ''T'' tid1|),
                            Enc {| LC ''TT2'', s(|AV ''I'' tid0|), s(|NV ''SomekIR'' tid1|),
                                   s(|NV ''SomeT'' tid1|)
                                |}
                                ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) )
                         |}
                         ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
      case (S_2_enc tid2) note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: S_kIR_secrecy intro: event_predOrdI)
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: R_ltk_I_S_sec intro: event_predOrdI)
  qed (insert facts, ((clarsimp, order?))+)?
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
                   Enc {| LC ''TT1'', s(|AV ''R'' tid1|), s(|NV ''kIR'' tid1|),
                          s(|NV ''T'' tid1|),
                          Enc {| LC ''TT2'', s(|AV ''I'' tid1|), LN ''Payload'' tid0,
                                 s(|NV ''SomeT'' tid1|)
                              |}
                              ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) )
                       |}
                       ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (I_3_SomeT tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|AV ''R'' tid1|), s(|NV ''kIR'' tid1|),
                          s(|NV ''T'' tid1|),
                          Enc {| LC ''TT2'', s(|AV ''I'' tid1|), s(|NV ''SomekIR'' tid1|),
                                 LN ''Payload'' tid0
                              |}
                              ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) )
                       |}
                       ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
next
  case R_4_Payload note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT2'', s(|AV ''I'' tid0|), s(|NV ''kIR'' tid0|),
                          s(|NV ''T'' tid0|)
                       |}
                       ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: R_ltk_R_S_sec intro: event_predOrdI)
  next
    case (I_3_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', s(|AV ''R'' tid0|), s(|NV ''kIR'' tid2|),
                            s(|NV ''T'' tid2|),
                            Enc {| LC ''TT2'', s(|AV ''I'' tid0|), s(|NV ''SomekIR'' tid2|),
                                   s(|NV ''SomeT'' tid2|)
                                |}
                                ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) )
                         |}
                         ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
      case (S_2_enc tid3) note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: S_kIR_secrecy intro: event_predOrdI)
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_2_enc tid2) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: R_ltk_I_S_sec intro: event_predOrdI)
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_DenningSacco_state) I_Payload_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, I_4) : steps t"
    "s(|NV ''Payload'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|AV ''R'' tid0|), s(|NV ''kIR'' tid0|),
                          s(|NV ''T'' tid0|),
                          Enc {| LC ''TT2'', s(|AV ''I'' tid0|), s(|NV ''SomekIR'' tid0|),
                                 s(|NV ''SomeT'' tid0|)
                              |}
                              ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) )
                       |}
                       ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: I_ltk_I_S_sec intro: event_predOrdI)
  next
    case (S_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT3'', s(|NV ''Payload'' tid0|) |}
                         ( LN ''kIR'' tid1 ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: S_kIR_secrecy intro: event_predOrdI)
    next
      case (R_4_enc tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT2'', s(|AV ''I'' tid2|), LN ''kIR'' tid1,
                              s(|NV ''T'' tid2|)
                           |}
                           ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: S_kIR_secrecy intro: event_predOrdI)
      next
        case (I_3_enc tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT1'', s(|AV ''R'' tid2|), s(|NV ''kIR'' tid3|),
                                s(|NV ''T'' tid3|),
                                Enc {| LC ''TT2'', s(|AV ''I'' tid2|), LN ''kIR'' tid1,
                                       s(|NV ''SomeT'' tid3|)
                                    |}
                                    ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) )
                             |}
                             ( K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
          case S_2_enc note facts = facts this[simplified]
          thus ?thesis by (fastsimp dest: R_Payload_secrecy intro: event_predOrdI)
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case S_2_enc note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: I_ltk_I_S_sec intro: event_predOrdI)
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
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
       s(|NV ''Payload'' tid1|) = LN ''Payload'' tid2 &
       s(|NV ''T'' tid1|) = LN ''T'' tid3 &
       s(|NV ''T'' tid2|) = LN ''T'' tid3 &
       s(|NV ''kIR'' tid1|) = LN ''kIR'' tid3 &
       s(|NV ''kIR'' tid2|) = LN ''kIR'' tid3 &
       predOrd t (St(tid2, R_4)) (St(tid1, I_4)) &
       predOrd t (St(tid2, R_3)) (St(tid2, R_4)) &
       predOrd t (St(tid3, S_2)) (St(tid1, I_2))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|AV ''R'' tid1|), s(|NV ''kIR'' tid1|),
                          s(|NV ''T'' tid1|),
                          Enc {| LC ''TT2'', s(|AV ''I'' tid1|), s(|NV ''SomekIR'' tid1|),
                                 s(|NV ''SomeT'' tid1|)
                              |}
                              ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) )
                       |}
                       ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: I_ltk_I_S_sec intro: event_predOrdI)
  next
    case (S_2_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT3'', s(|NV ''Payload'' tid1|) |}
                         ( LN ''kIR'' tid2 ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: S_kIR_secrecy intro: event_predOrdI)
    next
      case (R_4_enc tid3) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT2'', s(|AV ''I'' tid3|), LN ''kIR'' tid2,
                              s(|NV ''T'' tid3|)
                           |}
                           ( K ( s(|AV ''R'' tid3|) ) ( s(|AV ''S'' tid3|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: S_kIR_secrecy intro: event_predOrdI)
      next
        case (I_3_enc tid4) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT1'', s(|AV ''R'' tid3|), s(|NV ''kIR'' tid4|),
                                s(|NV ''T'' tid4|),
                                Enc {| LC ''TT2'', s(|AV ''I'' tid3|), LN ''kIR'' tid2,
                                       s(|NV ''SomeT'' tid4|)
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
       s(|NV ''T'' tid1|) = LN ''T'' tid3 &
       s(|NV ''T'' tid2|) = LN ''T'' tid3 &
       s(|NV ''kIR'' tid1|) = LN ''kIR'' tid3 &
       s(|NV ''kIR'' tid2|) = LN ''kIR'' tid3 &
       predOrd t (St(tid1, I_3)) (St(tid2, R_3)) &
       predOrd t (St(tid1, I_2)) (St(tid1, I_3)) &
       predOrd t (St(tid2, R_3)) (St(tid2, R_4)) &
       predOrd t (St(tid3, S_2)) (St(tid1, I_2)) &
       predOrd t (St(tid3, S_1)) (St(tid3, S_2))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT2'', s(|AV ''I'' tid2|), s(|NV ''kIR'' tid2|),
                          s(|NV ''T'' tid2|)
                       |}
                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: R_ltk_R_S_sec intro: event_predOrdI)
  next
    case (I_3_enc tid3) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', s(|AV ''R'' tid2|), s(|NV ''kIR'' tid3|),
                            s(|NV ''T'' tid3|),
                            Enc {| LC ''TT2'', s(|AV ''I'' tid2|), s(|NV ''SomekIR'' tid3|),
                                   s(|NV ''SomeT'' tid3|)
                                |}
                                ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) )
                         |}
                         ( K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      case (S_2_enc tid4) note facts = facts this[simplified]
      thus ?thesis by force
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_2_enc tid3) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: R_ltk_I_S_sec intro: event_predOrdI)
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
      Enc {| LC ''TT1'', ?s'(|AV ''R'' tid0|), ?s'(|NV ''kIR'' tid0|),
             ?s'(|NV ''T'' tid0|),
             Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|),
                    ?s'(|NV ''SomekIR'' tid0|), ?s'(|NV ''SomeT'' tid0|)
                 |}
                 ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) )
          |}
          ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|),
                            ?s'(|NV ''SomekIR'' tid0|), ?s'(|NV ''SomeT'' tid0|)
                         |}
                         ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
      case (I_3_enc tid1) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', ?s'(|AV ''R'' tid0|), s(|NV ''kIR'' tid1|),
                              s(|NV ''T'' tid1|),
                              Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|),
                                     ?s'(|NV ''SomekIR'' tid0|), ?s'(|NV ''SomeT'' tid0|)
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
      Enc {| LC ''TT1'', ?s'(|AV ''R'' tid0|), ?s'(|NV ''kIR'' tid0|),
             ?s'(|NV ''T'' tid0|),
             Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|),
                    ?s'(|NV ''SomekIR'' tid0|), ?s'(|NV ''SomeT'' tid0|)
                 |}
                 ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) )
          |}
          ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|),
                            ?s'(|NV ''SomekIR'' tid0|), ?s'(|NV ''SomeT'' tid0|)
                         |}
                         ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
      case (I_3_enc tid1) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', ?s'(|AV ''R'' tid0|), s(|NV ''kIR'' tid1|),
                              s(|NV ''T'' tid1|),
                              Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|),
                                     ?s'(|NV ''SomekIR'' tid0|), ?s'(|NV ''SomeT'' tid0|)
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
      Enc {| LC ''TT1'', ?s'(|AV ''R'' tid0|), ?s'(|NV ''kIR'' tid0|),
             ?s'(|NV ''T'' tid0|),
             Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|),
                    ?s'(|NV ''SomekIR'' tid0|), ?s'(|NV ''SomeT'' tid0|)
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
      Enc {| LC ''TT1'', ?s'(|AV ''R'' tid0|), ?s'(|NV ''kIR'' tid0|),
             ?s'(|NV ''T'' tid0|),
             Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|),
                    ?s'(|NV ''SomekIR'' tid0|), ?s'(|NV ''SomeT'' tid0|)
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
      Enc {| LC ''TT3'', ?s'(|NV ''Payload'' tid0|) |}
          ( ?s'(|NV ''kIR'' tid0|) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (R_3_T t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state DenningSacco t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|), ?s'(|NV ''kIR'' tid0|),
             ?s'(|NV ''T'' tid0|)
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
      Enc {| LC ''TT2'', ?s'(|AV ''I'' tid0|), ?s'(|NV ''kIR'' tid0|),
             ?s'(|NV ''T'' tid0|)
          |}
          ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
qed

end