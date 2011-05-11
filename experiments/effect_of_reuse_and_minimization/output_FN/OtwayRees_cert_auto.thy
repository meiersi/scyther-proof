theory OtwayRees_cert_auto
imports
  "../ESPLogic"
begin

role I
where "I =
  [ Send ''1'' {| sLN ''ni'', sLAV ''I'', sLAV ''R'',
                  Enc {| sLC ''TT1'', sLN ''ni'', sLAV ''I'', sLAV ''R'' |}
                      ( sK ''I'' ''S'' )
               |}
  , Recv ''4'' {| sLN ''ni'',
                  Enc {| sLC ''TT3'', sLN ''ni'', sLNV ''kIR'' |} ( sK ''I'' ''S'' )
               |}
  ]"

role R
where "R =
  [ Recv ''1'' {| sLNV ''ni'', sLAV ''I'', sLAV ''R'',
                  sLNV ''Ticket1''
               |}
  , Send ''2'' {| sLNV ''ni'', sLAV ''I'', sLAV ''R'',
                  sLNV ''Ticket1'',
                  Enc {| sLC ''TT2'', sLNV ''ni'', sLN ''nr'', sLAV ''I'', sLAV ''R''
                      |}
                      ( sK ''R'' ''S'' )
               |}
  , Recv ''3'' {| sLNV ''ni'', sLNV ''Ticket2'',
                  Enc {| sLC ''TT3'', sLN ''nr'', sLNV ''kIR'' |} ( sK ''R'' ''S'' )
               |}
  , Send ''4'' {| sLNV ''ni'', sLNV ''Ticket2'' |}
  ]"

role S
where "S =
  [ Recv ''2'' {| sLNV ''ni'', sLAV ''I'', sLAV ''R'',
                  Enc {| sLC ''TT1'', sLNV ''ni'', sLAV ''I'', sLAV ''R'' |}
                      ( sK ''I'' ''S'' ),
                  Enc {| sLC ''TT2'', sLNV ''ni'', sLNV ''nr'', sLAV ''I'',
                         sLAV ''R''
                      |}
                      ( sK ''R'' ''S'' )
               |}
  , Send ''3'' {| sLNV ''ni'',
                  Enc {| sLC ''TT3'', sLNV ''ni'', sLN ''kIR'' |} ( sK ''I'' ''S'' ),
                  Enc {| sLC ''TT3'', sLNV ''nr'', sLN ''kIR'' |} ( sK ''R'' ''S'' )
               |}
  ]"

protocol OtwayRees
where "OtwayRees = { I, R, S }"

locale atomic_OtwayRees_state = atomic_state OtwayRees
locale OtwayRees_state = reachable_state OtwayRees

lemma (in atomic_OtwayRees_state) I_ltk_I_S_sec:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_OtwayRees_state) I_ltk_R_S_sec:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_OtwayRees_state) R_ltk_I_S_sec:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_OtwayRees_state) R_ltk_R_S_sec:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_OtwayRees_state) S_ltk_I_S_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_OtwayRees_state) S_ltk_R_S_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_OtwayRees_state) S_kIR_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "LN ''kIR'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''kIR'' tid0 ")
  case S_3_kIR note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|NV ''ni'' tid0|), s(|AV ''I'' tid0|),
                          s(|AV ''R'' tid0|)
                       |}
                       ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', s(|NV ''ni'' tid0|), s(|NV ''nr'' tid0|),
                            s(|AV ''I'' tid0|), s(|AV ''R'' tid0|)
                         |}
                         ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (R_2_enc tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (I_1_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (S_3_nr tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|NV ''ni'' tid1|), s(|AV ''I'' tid1|),
                          s(|AV ''R'' tid1|)
                       |}
                       ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', s(|NV ''ni'' tid1|), LN ''kIR'' tid0,
                            s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                         |}
                         ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (I_1_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
      case ik0 note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''ni'' tid2 ")
        case I_1_ni note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', LN ''ni'' tid2, LN ''kIR'' tid0,
                                s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                             |}
                             ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case I_1_ni_1 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
          case ik0 note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', LN ''ni'' tid2, LN ''kIR'' tid0,
                                  s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                               |}
                               ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case ik0_1 note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', LN ''ni'' tid2, LN ''kIR'' tid0,
                                  s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                               |}
                               ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (S_3_nr tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', LN ''ni'' tid2, LN ''kIR'' tid0,
                                s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                             |}
                             ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case ik0_1 note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''ni'' tid2 ")
        case I_1_ni note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', LN ''ni'' tid2, LN ''kIR'' tid0,
                                s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                             |}
                             ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case I_1_ni_1 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', LN ''ni'' tid2, LN ''kIR'' tid0,
                                s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                             |}
                             ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (S_3_nr tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', LN ''ni'' tid2, LN ''kIR'' tid0,
                                s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                             |}
                             ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
next
  case S_3_kIR_1 note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|NV ''ni'' tid0|), s(|AV ''I'' tid0|),
                          s(|AV ''R'' tid0|)
                       |}
                       ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', s(|NV ''ni'' tid0|), s(|NV ''nr'' tid0|),
                            s(|AV ''I'' tid0|), s(|AV ''R'' tid0|)
                         |}
                         ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (R_2_enc tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (I_1_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_OtwayRees_state) R_kIR_sec:
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
                   Enc {| LC ''TT3'', LN ''nr'' tid0, s(|NV ''kIR'' tid0|) |}
                       ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''nr'' tid0 ")
      case R_2_nr note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_nr tid1) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_3_enc tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''nr'' tid0 ")
      case R_2_nr note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', LN ''nr'' tid0, s(|AV ''I'' tid1|),
                              s(|AV ''R'' tid1|)
                           |}
                           ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! " LN ''kIR'' tid1 ")
          case S_3_kIR note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', LN ''nr'' tid0, s(|NV ''nr'' tid1|),
                                  s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                               |}
                               ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid0|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (R_2_enc tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (S_3_nr tid3) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', LN ''nr'' tid0, s(|NV ''nr'' tid1|),
                                  s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                               |}
                               ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid0|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (R_2_enc tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case S_3_kIR_1 note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', LN ''nr'' tid0, s(|NV ''nr'' tid1|),
                                  s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                               |}
                               ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid0|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (R_2_enc tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_nr tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', LN ''nr'' tid0, s(|AV ''I'' tid1|),
                              s(|AV ''R'' tid1|)
                           |}
                           ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! " LN ''kIR'' tid1 ")
          case S_3_kIR note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', LN ''nr'' tid0, s(|NV ''nr'' tid1|),
                                  s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                               |}
                               ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid0|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (R_2_enc tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (S_3_nr tid3) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', LN ''nr'' tid0, s(|NV ''nr'' tid1|),
                                  s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                               |}
                               ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid0|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (R_2_enc tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case S_3_kIR_1 note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', LN ''nr'' tid0, s(|NV ''nr'' tid1|),
                                  s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                               |}
                               ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid0|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (R_2_enc tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_3_enc_1 tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''kIR'' tid1 ")
      case S_3_kIR note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', s(|NV ''ni'' tid1|), s(|AV ''I'' tid1|),
                              s(|AV ''R'' tid0|)
                           |}
                           ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', s(|NV ''ni'' tid1|), LN ''nr'' tid0,
                                s(|AV ''I'' tid1|), s(|AV ''R'' tid0|)
                             |}
                             ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! " LN ''nr'' tid0 ")
            case R_2_nr note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (S_3_nr tid3) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case R_2_enc note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (I_1_enc tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ")
          case ik0 note facts = facts this[simplified]
          thus ?thesis proof(sources! " LN ''ni'' tid3 ")
            case I_1_ni note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''nr'' tid0,
                                    s(|AV ''I'' tid1|), s(|AV ''R'' tid0|)
                                 |}
                                 ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis proof(sources! " LN ''nr'' tid0 ")
                case R_2_nr note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case (S_3_nr tid5) note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case I_1_ni_1 note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''nr'' tid0,
                                    s(|AV ''I'' tid1|), s(|AV ''R'' tid0|)
                                 |}
                                 ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis proof(sources! " LN ''nr'' tid0 ")
                case R_2_nr note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case (S_3_nr tid5) note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (S_3_nr tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''nr'' tid0,
                                    s(|AV ''I'' tid1|), s(|AV ''R'' tid0|)
                                 |}
                                 ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis proof(sources! " LN ''nr'' tid0 ")
                case R_2_nr note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case (S_3_nr tid5) note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_nr tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', s(|NV ''ni'' tid1|), s(|AV ''I'' tid1|),
                              s(|AV ''R'' tid0|)
                           |}
                           ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', s(|NV ''ni'' tid1|), LN ''nr'' tid0,
                                s(|AV ''I'' tid1|), s(|AV ''R'' tid0|)
                             |}
                             ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! " LN ''nr'' tid0 ")
            case R_2_nr note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (S_3_nr tid3) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case R_2_enc note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (I_1_enc tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT1'', s(|NV ''ni'' tid2|), s(|AV ''I'' tid2|),
                                s(|AV ''R'' tid2|)
                             |}
                             ( K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', s(|NV ''ni'' tid2|), LN ''kIR'' tid1,
                                  s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                               |}
                               ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (I_1_enc tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
            case ik0 note facts = facts this[simplified]
            thus ?thesis proof(sources! " LN ''ni'' tid3 ")
              case I_1_ni note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''nr'' tid0,
                                      s(|AV ''I'' tid1|), s(|AV ''R'' tid0|)
                                   |}
                                   ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                case fake note facts = facts this[simplified]
                thus ?thesis proof(sources! " LN ''nr'' tid0 ")
                  case R_2_nr note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case (S_3_nr tid6) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case R_2_enc note facts = facts this[simplified]
                thus ?thesis proof(sources! " LN ''ni'' tid4 ")
                  case I_1_ni note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''kIR'' tid1,
                                          s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                       |}
                                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case I_1_ni_1 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
                    case ik0 note facts = facts this[simplified]
                    thus ?thesis proof(sources! "
                                     Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''kIR'' tid1,
                                            s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                         |}
                                         ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                    qed (insert facts, ((clarsimp, order?))+)?
                  next
                    case ik0_1 note facts = facts this[simplified]
                    thus ?thesis proof(sources! "
                                     Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''kIR'' tid1,
                                            s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                         |}
                                         ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                    qed (insert facts, ((clarsimp, order?))+)?
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case (S_3_nr tid7) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''kIR'' tid1,
                                          s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                       |}
                                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case I_1_ni_1 note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ")
                case ik0 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''nr'' tid0,
                                        s(|AV ''I'' tid1|), s(|AV ''R'' tid0|)
                                     |}
                                     ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                  case fake note facts = facts this[simplified]
                  thus ?thesis proof(sources! " LN ''nr'' tid0 ")
                    case R_2_nr note facts = facts this[simplified]
                    thus ?thesis proof(sources! "
                                     K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                    qed (insert facts, ((clarsimp, order?))+)?
                  next
                    case (S_3_nr tid6) note facts = facts this[simplified]
                    thus ?thesis proof(sources! "
                                     K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                    qed (insert facts, ((clarsimp, order?))+)?
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (S_3_nr tid5) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''nr'' tid0,
                                      s(|AV ''I'' tid1|), s(|AV ''R'' tid0|)
                                   |}
                                   ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                case fake note facts = facts this[simplified]
                thus ?thesis proof(sources! " LN ''nr'' tid0 ")
                  case R_2_nr note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case (S_3_nr tid6) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case R_2_enc note facts = facts this[simplified]
                thus ?thesis proof(sources! " LN ''ni'' tid4 ")
                  case I_1_ni note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''kIR'' tid1,
                                          s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                       |}
                                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case I_1_ni_1 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
                    case ik0 note facts = facts this[simplified]
                    thus ?thesis proof(sources! "
                                     Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''kIR'' tid1,
                                            s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                         |}
                                         ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                    qed (insert facts, ((clarsimp, order?))+)?
                  next
                    case ik0_1 note facts = facts this[simplified]
                    thus ?thesis proof(sources! "
                                     Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''kIR'' tid1,
                                            s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                         |}
                                         ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                    qed (insert facts, ((clarsimp, order?))+)?
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case (S_3_nr tid7) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''kIR'' tid1,
                                          s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                       |}
                                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case ik0_1 note facts = facts this[simplified]
            thus ?thesis proof(sources! " LN ''ni'' tid3 ")
              case I_1_ni note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''nr'' tid0,
                                      s(|AV ''I'' tid1|), s(|AV ''R'' tid0|)
                                   |}
                                   ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                case fake note facts = facts this[simplified]
                thus ?thesis proof(sources! " LN ''nr'' tid0 ")
                  case R_2_nr note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case (S_3_nr tid6) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case R_2_enc note facts = facts this[simplified]
                thus ?thesis proof(sources! " LN ''ni'' tid4 ")
                  case I_1_ni note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''kIR'' tid1,
                                          s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                       |}
                                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case I_1_ni_1 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''kIR'' tid1,
                                          s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                       |}
                                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case (S_3_nr tid7) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''kIR'' tid1,
                                          s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                       |}
                                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case I_1_ni_1 note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid0|) ) ")
                case ik0 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''nr'' tid0,
                                        s(|AV ''I'' tid1|), s(|AV ''R'' tid0|)
                                     |}
                                     ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                  case fake note facts = facts this[simplified]
                  thus ?thesis proof(sources! " LN ''nr'' tid0 ")
                    case R_2_nr note facts = facts this[simplified]
                    thus ?thesis proof(sources! "
                                     K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                    qed (insert facts, ((clarsimp, order?))+)?
                  next
                    case (S_3_nr tid6) note facts = facts this[simplified]
                    thus ?thesis proof(sources! "
                                     K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                    qed (insert facts, ((clarsimp, order?))+)?
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (S_3_nr tid5) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''nr'' tid0,
                                      s(|AV ''I'' tid1|), s(|AV ''R'' tid0|)
                                   |}
                                   ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                case fake note facts = facts this[simplified]
                thus ?thesis proof(sources! " LN ''nr'' tid0 ")
                  case R_2_nr note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case (S_3_nr tid6) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case R_2_enc note facts = facts this[simplified]
                thus ?thesis proof(sources! " LN ''ni'' tid4 ")
                  case I_1_ni note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''kIR'' tid1,
                                          s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                       |}
                                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case I_1_ni_1 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''kIR'' tid1,
                                          s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                       |}
                                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case (S_3_nr tid7) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''kIR'' tid1,
                                          s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                       |}
                                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case S_3_kIR_1 note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_OtwayRees_state) I_kIR_sec:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, I_4) : steps t"
    "s(|NV ''kIR'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! " LN ''ni'' tid0 ")
    case I_1_ni note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT3'', LN ''ni'' tid0, s(|NV ''kIR'' tid0|) |}
                         ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_enc tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', LN ''ni'' tid0, s(|AV ''I'' tid0|),
                              s(|AV ''R'' tid2|)
                           |}
                           ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case I_1_enc note facts = facts this[simplified]
        thus ?thesis proof(sources! " LN ''kIR'' tid2 ")
          case S_3_kIR note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (S_3_nr tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', LN ''ni'' tid0, s(|NV ''nr'' tid2|),
                                  s(|AV ''I'' tid0|), s(|AV ''R'' tid0|)
                               |}
                               ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (R_2_enc tid5) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT1'', s(|NV ''ni'' tid4|), s(|AV ''I'' tid4|),
                                    s(|AV ''R'' tid4|)
                                 |}
                                 ( K ( s(|AV ''I'' tid4|) ) ( s(|AV ''S'' tid4|) ) ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', s(|NV ''ni'' tid4|), LN ''kIR'' tid2,
                                      s(|AV ''I'' tid4|), s(|AV ''R'' tid4|)
                                   |}
                                   ( K ( s(|AV ''R'' tid4|) ) ( s(|AV ''S'' tid4|) ) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (I_1_enc tid6) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''R'' tid4|) ) ( s(|AV ''S'' tid4|) ) ")
                case ik0 note facts = facts this[simplified]
                thus ?thesis proof(sources! " LN ''ni'' tid6 ")
                  case I_1_ni note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid6, LN ''kIR'' tid2,
                                          s(|AV ''I'' tid4|), s(|AV ''R'' tid4|)
                                       |}
                                       ( K ( s(|AV ''R'' tid4|) ) ( s(|AV ''S'' tid4|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case I_1_ni_1 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''I'' tid4|) ) ( s(|AV ''S'' tid4|) ) ")
                    case ik0 note facts = facts this[simplified]
                    thus ?thesis proof(sources! "
                                     Enc {| LC ''TT2'', LN ''ni'' tid6, LN ''kIR'' tid2,
                                            s(|AV ''I'' tid4|), s(|AV ''R'' tid4|)
                                         |}
                                         ( K ( s(|AV ''R'' tid4|) ) ( s(|AV ''S'' tid4|) ) ) ")
                    qed (insert facts, ((clarsimp, order?))+)?
                  next
                    case ik0_1 note facts = facts this[simplified]
                    thus ?thesis proof(sources! "
                                     Enc {| LC ''TT2'', LN ''ni'' tid6, LN ''kIR'' tid2,
                                            s(|AV ''I'' tid4|), s(|AV ''R'' tid4|)
                                         |}
                                         ( K ( s(|AV ''R'' tid4|) ) ( s(|AV ''S'' tid4|) ) ) ")
                    qed (insert facts, ((clarsimp, order?))+)?
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case (S_3_nr tid7) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid6, LN ''kIR'' tid2,
                                          s(|AV ''I'' tid4|), s(|AV ''R'' tid4|)
                                       |}
                                       ( K ( s(|AV ''R'' tid4|) ) ( s(|AV ''S'' tid4|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case ik0_1 note facts = facts this[simplified]
                thus ?thesis proof(sources! " LN ''ni'' tid6 ")
                  case I_1_ni note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid6, LN ''kIR'' tid2,
                                          s(|AV ''I'' tid4|), s(|AV ''R'' tid4|)
                                       |}
                                       ( K ( s(|AV ''R'' tid4|) ) ( s(|AV ''S'' tid4|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case I_1_ni_1 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid6, LN ''kIR'' tid2,
                                          s(|AV ''I'' tid4|), s(|AV ''R'' tid4|)
                                       |}
                                       ( K ( s(|AV ''R'' tid4|) ) ( s(|AV ''S'' tid4|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case (S_3_nr tid7) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid6, LN ''kIR'' tid2,
                                          s(|AV ''I'' tid4|), s(|AV ''R'' tid4|)
                                       |}
                                       ( K ( s(|AV ''R'' tid4|) ) ( s(|AV ''S'' tid4|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case S_3_kIR_1 note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_enc_1 tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''kIR'' tid2 ")
        case S_3_kIR note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT1'', s(|NV ''ni'' tid2|), s(|AV ''I'' tid2|),
                                s(|AV ''I'' tid0|)
                             |}
                             ( K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid0|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', s(|NV ''ni'' tid2|), LN ''ni'' tid0,
                                  s(|AV ''I'' tid2|), s(|AV ''I'' tid0|)
                               |}
                               ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (I_1_enc tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid0|) ) ")
            case ik0 note facts = facts this[simplified]
            thus ?thesis proof(sources! " LN ''ni'' tid4 ")
              case I_1_ni note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid0,
                                      s(|AV ''I'' tid2|), s(|AV ''I'' tid0|)
                                   |}
                                   ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                case fake note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case I_1_ni_1 note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid0,
                                      s(|AV ''I'' tid2|), s(|AV ''I'' tid0|)
                                   |}
                                   ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                case fake note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (S_3_nr tid5) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid0,
                                      s(|AV ''I'' tid2|), s(|AV ''I'' tid0|)
                                   |}
                                   ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                case fake note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (S_3_nr tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT1'', s(|NV ''ni'' tid2|), s(|AV ''I'' tid2|),
                                s(|AV ''I'' tid0|)
                             |}
                             ( K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid0|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', s(|NV ''ni'' tid2|), LN ''ni'' tid0,
                                  s(|AV ''I'' tid2|), s(|AV ''I'' tid0|)
                               |}
                               ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (I_1_enc tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT1'', s(|NV ''ni'' tid3|), s(|AV ''I'' tid3|),
                                  s(|AV ''R'' tid3|)
                               |}
                               ( K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid3|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT2'', s(|NV ''ni'' tid3|), LN ''kIR'' tid2,
                                    s(|AV ''I'' tid3|), s(|AV ''R'' tid3|)
                                 |}
                                 ( K ( s(|AV ''R'' tid3|) ) ( s(|AV ''S'' tid3|) ) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (I_1_enc tid5) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''R'' tid3|) ) ( s(|AV ''S'' tid3|) ) ")
              case ik0 note facts = facts this[simplified]
              thus ?thesis proof(sources! " LN ''ni'' tid4 ")
                case I_1_ni note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid0,
                                        s(|AV ''I'' tid2|), s(|AV ''I'' tid0|)
                                     |}
                                     ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                  case fake note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case I_1_ni_1 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid0|) ) ")
                  case ik0 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid0,
                                          s(|AV ''I'' tid2|), s(|AV ''I'' tid0|)
                                       |}
                                       ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                    case fake note facts = facts this[simplified]
                    thus ?thesis proof(sources! "
                                     K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                    qed (insert facts, ((clarsimp, order?))+)?
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case (S_3_nr tid6) note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid0,
                                        s(|AV ''I'' tid2|), s(|AV ''I'' tid0|)
                                     |}
                                     ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                  case fake note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case ik0_1 note facts = facts this[simplified]
              thus ?thesis proof(sources! " LN ''ni'' tid4 ")
                case I_1_ni note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid0,
                                        s(|AV ''I'' tid2|), s(|AV ''I'' tid0|)
                                     |}
                                     ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                  case fake note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case I_1_ni_1 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid0|) ) ")
                  case ik0 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid0,
                                          s(|AV ''I'' tid2|), s(|AV ''I'' tid0|)
                                       |}
                                       ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                    case fake note facts = facts this[simplified]
                    thus ?thesis proof(sources! "
                                     K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                    qed (insert facts, ((clarsimp, order?))+)?
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case (S_3_nr tid6) note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid0,
                                        s(|AV ''I'' tid2|), s(|AV ''I'' tid0|)
                                     |}
                                     ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                  case fake note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case S_3_kIR_1 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case I_1_ni_1 note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT3'', LN ''ni'' tid0, s(|NV ''kIR'' tid0|) |}
                         ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_enc tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', LN ''ni'' tid0, s(|AV ''I'' tid0|),
                              s(|AV ''R'' tid2|)
                           |}
                           ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case I_1_enc note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_enc_1 tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_3_nr tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT3'', LN ''ni'' tid0, s(|NV ''kIR'' tid0|) |}
                         ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_enc tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', LN ''ni'' tid0, s(|AV ''I'' tid0|),
                              s(|AV ''R'' tid2|)
                           |}
                           ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case I_1_enc note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT1'', s(|NV ''ni'' tid1|), s(|AV ''I'' tid1|),
                                s(|AV ''R'' tid1|)
                             |}
                             ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', s(|NV ''ni'' tid1|), LN ''ni'' tid0,
                                  s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                               |}
                               ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (I_1_enc tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
            case ik0 note facts = facts this[simplified]
            thus ?thesis proof(sources! " LN ''kIR'' tid2 ")
              case S_3_kIR note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (S_3_nr tid5) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid0, s(|NV ''nr'' tid2|),
                                      s(|AV ''I'' tid0|), s(|AV ''R'' tid0|)
                                   |}
                                   ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                case fake note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case (R_2_enc tid6) note facts = facts this[simplified]
                thus ?thesis proof(sources! " LN ''ni'' tid4 ")
                  case I_1_ni note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid0,
                                          s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                       |}
                                       ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case I_1_ni_1 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
                    case ik0 note facts = facts this[simplified]
                    thus ?thesis proof(sources! "
                                     Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid0,
                                            s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                         |}
                                         ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                    qed (insert facts, ((clarsimp, order?))+)?
                  next
                    case ik0_1 note facts = facts this[simplified]
                    thus ?thesis proof(sources! "
                                     Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid0,
                                            s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                         |}
                                         ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                    qed (insert facts, ((clarsimp, order?))+)?
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case (S_3_nr tid7) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid0,
                                          s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                       |}
                                       ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case S_3_kIR_1 note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case ik0_1 note facts = facts this[simplified]
            thus ?thesis proof(sources! " LN ''kIR'' tid2 ")
              case S_3_kIR note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (S_3_nr tid5) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid0, s(|NV ''nr'' tid2|),
                                      s(|AV ''I'' tid0|), s(|AV ''R'' tid0|)
                                   |}
                                   ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                case fake note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case (R_2_enc tid6) note facts = facts this[simplified]
                thus ?thesis proof(sources! " LN ''ni'' tid4 ")
                  case I_1_ni note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid0,
                                          s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                       |}
                                       ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case I_1_ni_1 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid0,
                                          s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                       |}
                                       ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case (S_3_nr tid7) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid0,
                                          s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                       |}
                                       ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case S_3_kIR_1 note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_enc_1 tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', s(|NV ''ni'' tid1|), s(|AV ''I'' tid1|),
                              s(|AV ''R'' tid1|)
                           |}
                           ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', s(|NV ''ni'' tid1|), LN ''ni'' tid0,
                                s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                             |}
                             ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (I_1_enc tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
          case ik0 note facts = facts this[simplified]
          thus ?thesis proof(sources! " LN ''kIR'' tid2 ")
            case S_3_kIR note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT1'', s(|NV ''ni'' tid2|), s(|AV ''I'' tid2|),
                                    s(|AV ''I'' tid0|)
                                 |}
                                 ( K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid0|) ) ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', s(|NV ''ni'' tid2|), LN ''ni'' tid0,
                                      s(|AV ''I'' tid2|), s(|AV ''I'' tid0|)
                                   |}
                                   ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                case fake note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (I_1_enc tid5) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid0|) ) ")
                case ik0 note facts = facts this[simplified]
                thus ?thesis proof(sources! " LN ''ni'' tid3 ")
                  case I_1_ni note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid0,
                                          s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                       |}
                                       ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case I_1_ni_1 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
                    case ik0 note facts = facts this[simplified]
                    thus ?thesis proof(sources! "
                                     Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid0,
                                            s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                         |}
                                         ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                    qed (insert facts, ((clarsimp, order?))+)?
                  next
                    case ik0_1 note facts = facts this[simplified]
                    thus ?thesis proof(sources! "
                                     Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid0,
                                            s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                         |}
                                         ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                    qed (insert facts, ((clarsimp, order?))+)?
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case (S_3_nr tid6) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid0,
                                          s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                       |}
                                       ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (S_3_nr tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT1'', s(|NV ''ni'' tid2|), s(|AV ''I'' tid2|),
                                    s(|AV ''I'' tid0|)
                                 |}
                                 ( K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid0|) ) ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', s(|NV ''ni'' tid2|), LN ''ni'' tid0,
                                      s(|AV ''I'' tid2|), s(|AV ''I'' tid0|)
                                   |}
                                   ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                case fake note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (I_1_enc tid5) note facts = facts this[simplified]
              thus ?thesis proof(sources! " LN ''ni'' tid3 ")
                case I_1_ni note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid0,
                                        s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                     |}
                                     ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case I_1_ni_1 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
                  case ik0 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid0,
                                          s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                       |}
                                       ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case ik0_1 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid0,
                                          s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                       |}
                                       ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case (S_3_nr tid6) note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid0,
                                        s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                     |}
                                     ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case S_3_kIR_1 note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case ik0_1 note facts = facts this[simplified]
          thus ?thesis proof(sources! " LN ''kIR'' tid2 ")
            case S_3_kIR note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT1'', s(|NV ''ni'' tid2|), s(|AV ''I'' tid2|),
                                    s(|AV ''I'' tid0|)
                                 |}
                                 ( K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid0|) ) ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', s(|NV ''ni'' tid2|), LN ''ni'' tid0,
                                      s(|AV ''I'' tid2|), s(|AV ''I'' tid0|)
                                   |}
                                   ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                case fake note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (I_1_enc tid5) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid0|) ) ")
                case ik0 note facts = facts this[simplified]
                thus ?thesis proof(sources! " LN ''ni'' tid3 ")
                  case I_1_ni note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid0,
                                          s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                       |}
                                       ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case I_1_ni_1 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid0,
                                          s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                       |}
                                       ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case (S_3_nr tid6) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid0,
                                          s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                       |}
                                       ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (S_3_nr tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT1'', s(|NV ''ni'' tid2|), s(|AV ''I'' tid2|),
                                    s(|AV ''I'' tid0|)
                                 |}
                                 ( K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid0|) ) ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', s(|NV ''ni'' tid2|), LN ''ni'' tid0,
                                      s(|AV ''I'' tid2|), s(|AV ''I'' tid0|)
                                   |}
                                   ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
                case fake note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (I_1_enc tid5) note facts = facts this[simplified]
              thus ?thesis proof(sources! " LN ''ni'' tid3 ")
                case I_1_ni note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid0,
                                        s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                     |}
                                     ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case I_1_ni_1 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid0,
                                        s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                     |}
                                     ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case (S_3_nr tid6) note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid0,
                                        s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                     |}
                                     ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case S_3_kIR_1 note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_OtwayRees_state) ni_first_send:
  assumes facts:
    "roleMap r tid1 = Some I"
    "LN ''ni'' tid1 : knows t"
  shows "predOrd t (St(tid1, I_1)) (Ln(LN ''ni'' tid1))"
using facts proof(sources! " LN ''ni'' tid1 ")
  case I_1_ni note facts = facts this[simplified]
  thus ?thesis by force
next
  case I_1_ni_1 note facts = facts this[simplified]
  thus ?thesis by force
next
  case (S_3_nr tid2) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|NV ''ni'' tid2|), s(|AV ''I'' tid2|),
                          s(|AV ''R'' tid2|)
                       |}
                       ( K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', s(|NV ''ni'' tid2|), LN ''ni'' tid1,
                            s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                         |}
                         ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (I_1_enc tid3) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
      case ik0 note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''ni'' tid3 ")
        case I_1_ni note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid1,
                                s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                             |}
                             ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case I_1_ni_1 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
          case ik0 note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid1,
                                  s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                               |}
                               ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case ik0_1 note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid1,
                                  s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                               |}
                               ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (S_3_nr tid4) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid1,
                                s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                             |}
                             ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case ik0_1 note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''ni'' tid3 ")
        case I_1_ni note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid1,
                                s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                             |}
                             ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case I_1_ni_1 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid1,
                                s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                             |}
                             ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (S_3_nr tid4) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', LN ''ni'' tid3, LN ''ni'' tid1,
                                s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                             |}
                             ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_OtwayRees_state) I_auth:
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
       s(|NV ''kIR'' tid1|) = LN ''kIR'' tid3 &
       s(|NV ''ni'' tid2|) = LN ''ni'' tid1 &
       s(|NV ''ni'' tid3|) = LN ''ni'' tid1 &
       s(|NV ''nr'' tid3|) = LN ''nr'' tid2 &
       predOrd t (St(tid1, I_1)) (St(tid2, R_1)) &
       predOrd t (St(tid2, R_2)) (St(tid3, S_2)) &
       predOrd t (St(tid2, R_1)) (St(tid2, R_2)) &
       predOrd t (St(tid3, S_3)) (St(tid1, I_4)) &
       predOrd t (St(tid3, S_2)) (St(tid3, S_3))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! " LN ''ni'' tid1 ")
    case I_1_ni note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT3'', LN ''ni'' tid1, s(|NV ''kIR'' tid1|) |}
                         ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_enc tid3) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', LN ''ni'' tid1, s(|AV ''I'' tid1|),
                              s(|AV ''R'' tid3|)
                           |}
                           ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case I_1_enc note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', LN ''ni'' tid1, s(|NV ''nr'' tid3|),
                                s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                             |}
                             ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (R_2_enc tid5) note facts = facts this[simplified]
          thus ?thesis by force
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_enc_1 tid3) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', s(|NV ''ni'' tid3|), s(|AV ''I'' tid3|),
                              s(|AV ''I'' tid1|)
                           |}
                           ( K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid1|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', s(|NV ''ni'' tid3|), LN ''ni'' tid1,
                                s(|AV ''I'' tid3|), s(|AV ''I'' tid1|)
                             |}
                             ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (I_1_enc tid4) note facts = facts this[simplified]
        thus ?thesis proof(sources! " LN ''ni'' tid4 ")
          case I_1_ni note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid1,
                                  s(|AV ''I'' tid3|), s(|AV ''I'' tid1|)
                               |}
                               ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case I_1_ni_1 note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid1|) ) ")
            case ik0 note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid1,
                                    s(|AV ''I'' tid3|), s(|AV ''I'' tid1|)
                                 |}
                                 ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (S_3_nr tid5) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid1,
                                  s(|AV ''I'' tid3|), s(|AV ''I'' tid1|)
                               |}
                               ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case I_1_ni_1 note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT3'', LN ''ni'' tid1, s(|NV ''kIR'' tid1|) |}
                         ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_enc tid3) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', LN ''ni'' tid1, s(|AV ''I'' tid1|),
                              s(|AV ''R'' tid3|)
                           |}
                           ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case I_1_enc note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_enc_1 tid3) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_3_nr tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT3'', LN ''ni'' tid1, s(|NV ''kIR'' tid1|) |}
                         ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_enc tid3) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', LN ''ni'' tid1, s(|AV ''I'' tid1|),
                              s(|AV ''R'' tid3|)
                           |}
                           ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case I_1_enc note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT1'', s(|NV ''ni'' tid2|), s(|AV ''I'' tid2|),
                                s(|AV ''R'' tid2|)
                             |}
                             ( K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', s(|NV ''ni'' tid2|), LN ''ni'' tid1,
                                  s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                               |}
                               ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (I_1_enc tid5) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
            case ik0 note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT2'', LN ''ni'' tid1, s(|NV ''nr'' tid3|),
                                    s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                 |}
                                 ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (R_2_enc tid6) note facts = facts this[simplified]
              thus ?thesis proof(sources! " LN ''ni'' tid5 ")
                case I_1_ni note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid5, LN ''ni'' tid1,
                                        s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                     |}
                                     ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case I_1_ni_1 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
                  case ik0 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid5, LN ''ni'' tid1,
                                          s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                       |}
                                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case ik0_1 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid5, LN ''ni'' tid1,
                                          s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                       |}
                                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case (S_3_nr tid7) note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid5, LN ''ni'' tid1,
                                        s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                     |}
                                     ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case ik0_1 note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT2'', LN ''ni'' tid1, s(|NV ''nr'' tid3|),
                                    s(|AV ''I'' tid1|), s(|AV ''R'' tid1|)
                                 |}
                                 ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (R_2_enc tid6) note facts = facts this[simplified]
              thus ?thesis proof(sources! " LN ''ni'' tid5 ")
                case I_1_ni note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid5, LN ''ni'' tid1,
                                        s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                     |}
                                     ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case I_1_ni_1 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid5, LN ''ni'' tid1,
                                        s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                     |}
                                     ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case (S_3_nr tid7) note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid5, LN ''ni'' tid1,
                                        s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                     |}
                                     ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_enc_1 tid3) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', s(|NV ''ni'' tid2|), s(|AV ''I'' tid2|),
                              s(|AV ''R'' tid2|)
                           |}
                           ( K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', s(|NV ''ni'' tid2|), LN ''ni'' tid1,
                                s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                             |}
                             ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (I_1_enc tid4) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
          case ik0 note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT1'', s(|NV ''ni'' tid3|), s(|AV ''I'' tid3|),
                                  s(|AV ''I'' tid1|)
                               |}
                               ( K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid1|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT2'', s(|NV ''ni'' tid3|), LN ''ni'' tid1,
                                    s(|AV ''I'' tid3|), s(|AV ''I'' tid1|)
                                 |}
                                 ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (I_1_enc tid5) note facts = facts this[simplified]
            thus ?thesis proof(sources! " LN ''ni'' tid4 ")
              case I_1_ni note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid1,
                                      s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                   |}
                                   ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case I_1_ni_1 note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
                case ik0 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid1,
                                        s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                     |}
                                     ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case ik0_1 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid1,
                                        s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                     |}
                                     ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (S_3_nr tid6) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid1,
                                      s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                   |}
                                   ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case ik0_1 note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT1'', s(|NV ''ni'' tid3|), s(|AV ''I'' tid3|),
                                  s(|AV ''I'' tid1|)
                               |}
                               ( K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid1|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT2'', s(|NV ''ni'' tid3|), LN ''ni'' tid1,
                                    s(|AV ''I'' tid3|), s(|AV ''I'' tid1|)
                                 |}
                                 ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (I_1_enc tid5) note facts = facts this[simplified]
            thus ?thesis proof(sources! " LN ''ni'' tid4 ")
              case I_1_ni note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid1,
                                      s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                   |}
                                   ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case I_1_ni_1 note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid1,
                                      s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                   |}
                                   ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (S_3_nr tid6) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''ni'' tid1,
                                      s(|AV ''I'' tid2|), s(|AV ''R'' tid2|)
                                   |}
                                   ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_OtwayRees_state) R_ni_agree:
  assumes facts:
    "roleMap r tid2 = Some R"
    "s(|AV ''I'' tid2|) ~: Compromised"
    "s(|AV ''R'' tid2|) ~: Compromised"
    "s(|AV ''S'' tid2|) ~: Compromised"
    "(tid2, R_3) : steps t"
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
       s(|NV ''kIR'' tid2|) = LN ''kIR'' tid3 &
       s(|NV ''ni'' tid2|) = LN ''ni'' tid1 &
       s(|NV ''ni'' tid3|) = LN ''ni'' tid1 &
       s(|NV ''nr'' tid3|) = LN ''nr'' tid2 &
       predOrd t (St(tid1, I_1)) (St(tid2, R_1)) &
       predOrd t (St(tid2, R_2)) (St(tid3, S_2)) &
       predOrd t (St(tid2, R_1)) (St(tid2, R_2)) &
       predOrd t (St(tid3, S_3)) (St(tid2, R_3)) &
       predOrd t (St(tid3, S_2)) (St(tid3, S_3))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT3'', LN ''nr'' tid2, s(|NV ''kIR'' tid2|) |}
                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''nr'' tid2 ")
      case R_2_nr note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_nr tid3) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_3_enc tid3) note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''nr'' tid2 ")
      case R_2_nr note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', LN ''nr'' tid2, s(|AV ''I'' tid3|),
                              s(|AV ''R'' tid3|)
                           |}
                           ( K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid2|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', LN ''nr'' tid2, s(|NV ''nr'' tid3|),
                                s(|AV ''I'' tid3|), s(|AV ''R'' tid3|)
                             |}
                             ( K ( s(|AV ''R'' tid3|) ) ( s(|AV ''S'' tid2|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid2|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (R_2_enc tid5) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid2|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_nr tid4) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', LN ''nr'' tid2, s(|AV ''I'' tid3|),
                              s(|AV ''R'' tid3|)
                           |}
                           ( K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid2|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', LN ''nr'' tid2, s(|NV ''nr'' tid3|),
                                s(|AV ''I'' tid3|), s(|AV ''R'' tid3|)
                             |}
                             ( K ( s(|AV ''R'' tid3|) ) ( s(|AV ''S'' tid2|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid2|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (R_2_enc tid5) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid2|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_3_enc_1 tid3) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', s(|NV ''ni'' tid3|), s(|AV ''I'' tid3|),
                            s(|AV ''R'' tid2|)
                         |}
                         ( K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid2|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT2'', s(|NV ''ni'' tid3|), LN ''nr'' tid2,
                              s(|AV ''I'' tid3|), s(|AV ''R'' tid2|)
                           |}
                           ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! " LN ''nr'' tid2 ")
          case R_2_nr note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (S_3_nr tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case R_2_enc note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''I'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (I_1_enc tid4) note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''ni'' tid4 ")
        case I_1_ni note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''nr'' tid2,
                                s(|AV ''I'' tid3|), s(|AV ''R'' tid2|)
                             |}
                             ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! " LN ''nr'' tid2 ")
            case R_2_nr note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (S_3_nr tid6) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case R_2_enc note facts = facts this[simplified]
          thus ?thesis by force
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case I_1_ni_1 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid2|) ) ")
          case ik0 note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''nr'' tid2,
                                  s(|AV ''I'' tid3|), s(|AV ''R'' tid2|)
                               |}
                               ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! " LN ''nr'' tid2 ")
              case R_2_nr note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (S_3_nr tid6) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (S_3_nr tid5) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', LN ''ni'' tid4, LN ''nr'' tid2,
                                s(|AV ''I'' tid3|), s(|AV ''R'' tid2|)
                             |}
                             ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! " LN ''nr'' tid2 ")
            case R_2_nr note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (S_3_nr tid6) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case R_2_enc note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT1'', s(|NV ''ni'' tid5|), s(|AV ''I'' tid5|),
                                  s(|AV ''R'' tid5|)
                               |}
                               ( K ( s(|AV ''I'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT2'', s(|NV ''ni'' tid5|), LN ''ni'' tid4,
                                    s(|AV ''I'' tid5|), s(|AV ''R'' tid5|)
                                 |}
                                 ( K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (I_1_enc tid7) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ")
              case ik0 note facts = facts this[simplified]
              thus ?thesis proof(sources! " LN ''ni'' tid7 ")
                case I_1_ni note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid7, LN ''ni'' tid4,
                                        s(|AV ''I'' tid5|), s(|AV ''R'' tid5|)
                                     |}
                                     ( K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case I_1_ni_1 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 K ( s(|AV ''I'' tid5|) ) ( s(|AV ''S'' tid5|) ) ")
                  case ik0 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid7, LN ''ni'' tid4,
                                          s(|AV ''I'' tid5|), s(|AV ''R'' tid5|)
                                       |}
                                       ( K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case ik0_1 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''TT2'', LN ''ni'' tid7, LN ''ni'' tid4,
                                          s(|AV ''I'' tid5|), s(|AV ''R'' tid5|)
                                       |}
                                       ( K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case (S_3_nr tid8) note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid7, LN ''ni'' tid4,
                                        s(|AV ''I'' tid5|), s(|AV ''R'' tid5|)
                                     |}
                                     ( K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case ik0_1 note facts = facts this[simplified]
              thus ?thesis proof(sources! " LN ''ni'' tid7 ")
                case I_1_ni note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid7, LN ''ni'' tid4,
                                        s(|AV ''I'' tid5|), s(|AV ''R'' tid5|)
                                     |}
                                     ( K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case I_1_ni_1 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid7, LN ''ni'' tid4,
                                        s(|AV ''I'' tid5|), s(|AV ''R'' tid5|)
                                     |}
                                     ( K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case (S_3_nr tid8) note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid7, LN ''ni'' tid4,
                                        s(|AV ''I'' tid5|), s(|AV ''R'' tid5|)
                                     |}
                                     ( K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_OtwayRees_state) S_ni_agree:
  assumes facts:
    "roleMap r tid3 = Some S"
    "s(|AV ''I'' tid3|) ~: Compromised"
    "s(|AV ''R'' tid3|) ~: Compromised"
    "s(|AV ''S'' tid3|) ~: Compromised"
    "(tid3, S_2) : steps t"
  shows
    "? tid1 tid2.
       roleMap r tid1 = Some I &
       roleMap r tid2 = Some R &
       s(|AV ''I'' tid2|) = s(|AV ''I'' tid1|) &
       s(|AV ''I'' tid3|) = s(|AV ''I'' tid1|) &
       s(|AV ''R'' tid2|) = s(|AV ''R'' tid1|) &
       s(|AV ''R'' tid3|) = s(|AV ''R'' tid1|) &
       s(|AV ''S'' tid2|) = s(|AV ''S'' tid1|) &
       s(|AV ''S'' tid3|) = s(|AV ''S'' tid1|) &
       s(|NV ''ni'' tid2|) = LN ''ni'' tid1 &
       s(|NV ''ni'' tid3|) = LN ''ni'' tid1 &
       s(|NV ''nr'' tid3|) = LN ''nr'' tid2 &
       predOrd t (St(tid1, I_1)) (St(tid2, R_1)) &
       predOrd t (St(tid2, R_2)) (St(tid3, S_2)) &
       predOrd t (St(tid2, R_1)) (St(tid2, R_2))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|NV ''ni'' tid3|), s(|AV ''I'' tid3|),
                          s(|AV ''R'' tid3|)
                       |}
                       ( K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid3|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', s(|NV ''ni'' tid3|), s(|NV ''nr'' tid3|),
                            s(|AV ''I'' tid3|), s(|AV ''R'' tid3|)
                         |}
                         ( K ( s(|AV ''R'' tid3|) ) ( s(|AV ''S'' tid3|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid3|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (R_2_enc tid4) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid3|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (I_1_enc tid4) note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''ni'' tid4 ")
      case I_1_ni note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT2'', LN ''ni'' tid4, s(|NV ''nr'' tid3|),
                              s(|AV ''I'' tid3|), s(|AV ''R'' tid3|)
                           |}
                           ( K ( s(|AV ''R'' tid3|) ) ( s(|AV ''S'' tid3|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''R'' tid3|) ) ( s(|AV ''S'' tid3|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (R_2_enc tid6) note facts = facts this[simplified]
        thus ?thesis by force
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case I_1_ni_1 note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''I'' tid3|) ) ( s(|AV ''S'' tid3|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_nr tid5) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT2'', LN ''ni'' tid4, s(|NV ''nr'' tid3|),
                              s(|AV ''I'' tid3|), s(|AV ''R'' tid3|)
                           |}
                           ( K ( s(|AV ''R'' tid3|) ) ( s(|AV ''S'' tid3|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''R'' tid3|) ) ( s(|AV ''S'' tid3|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (R_2_enc tid6) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT1'', s(|NV ''ni'' tid5|), s(|AV ''I'' tid5|),
                                s(|AV ''R'' tid5|)
                             |}
                             ( K ( s(|AV ''I'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT2'', s(|NV ''ni'' tid5|), LN ''ni'' tid4,
                                  s(|AV ''I'' tid5|), s(|AV ''R'' tid5|)
                               |}
                               ( K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (I_1_enc tid7) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ")
            case ik0 note facts = facts this[simplified]
            thus ?thesis proof(sources! " LN ''ni'' tid7 ")
              case I_1_ni note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid7, LN ''ni'' tid4,
                                      s(|AV ''I'' tid5|), s(|AV ''R'' tid5|)
                                   |}
                                   ( K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case I_1_ni_1 note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''I'' tid5|) ) ( s(|AV ''S'' tid5|) ) ")
                case ik0 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid7, LN ''ni'' tid4,
                                        s(|AV ''I'' tid5|), s(|AV ''R'' tid5|)
                                     |}
                                     ( K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case ik0_1 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT2'', LN ''ni'' tid7, LN ''ni'' tid4,
                                        s(|AV ''I'' tid5|), s(|AV ''R'' tid5|)
                                     |}
                                     ( K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (S_3_nr tid8) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid7, LN ''ni'' tid4,
                                      s(|AV ''I'' tid5|), s(|AV ''R'' tid5|)
                                   |}
                                   ( K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case ik0_1 note facts = facts this[simplified]
            thus ?thesis proof(sources! " LN ''ni'' tid7 ")
              case I_1_ni note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid7, LN ''ni'' tid4,
                                      s(|AV ''I'' tid5|), s(|AV ''R'' tid5|)
                                   |}
                                   ( K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case I_1_ni_1 note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid7, LN ''ni'' tid4,
                                      s(|AV ''I'' tid5|), s(|AV ''R'' tid5|)
                                   |}
                                   ( K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (S_3_nr tid8) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT2'', LN ''ni'' tid7, LN ''ni'' tid4,
                                      s(|AV ''I'' tid5|), s(|AV ''R'' tid5|)
                                   |}
                                   ( K ( s(|AV ''R'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in OtwayRees_state) weak_atomicity:
  "complete (t,r,s) atomicAnn"
proof (cases rule: complete_atomicAnnI[completeness_cases_rule])
  case (I_4_kIR t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state OtwayRees t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! " LN ''ni'' tid0 ")
    case I_1_ni note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT3'', LN ''ni'' tid0, ?s'(|NV ''kIR'' tid0|) |}
                         ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
    qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
  next
    case I_1_ni_1 note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT3'', LN ''ni'' tid0, ?s'(|NV ''kIR'' tid0|) |}
                         ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
    qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
  next
    case (S_3_nr tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT3'', LN ''ni'' tid0, ?s'(|NV ''kIR'' tid0|) |}
                         ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
    qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (R_1_Ticket1 t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state OtwayRees t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  by (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps)
next
  case (R_1_ni t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state OtwayRees t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  by (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps)
next
  case (R_3_Ticket2 t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state OtwayRees t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  by (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps)
next
  case (R_3_kIR t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state OtwayRees t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT3'', LN ''nr'' tid0, ?s'(|NV ''kIR'' tid0|) |}
          ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (S_2_ni t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state OtwayRees t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  by (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps)
next
  case (S_2_nr t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state OtwayRees t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT1'', ?s'(|NV ''ni'' tid0|), ?s'(|AV ''I'' tid0|),
             ?s'(|AV ''R'' tid0|)
          |}
          ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', ?s'(|NV ''ni'' tid0|), ?s'(|NV ''nr'' tid0|),
                            ?s'(|AV ''I'' tid0|), ?s'(|AV ''R'' tid0|)
                         |}
                         ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
    qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
  next
    case (I_1_enc tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''ni'' tid1 ")
      case I_1_ni note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT2'', LN ''ni'' tid1, ?s'(|NV ''nr'' tid0|),
                              ?s'(|AV ''I'' tid0|), ?s'(|AV ''R'' tid0|)
                           |}
                           ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
      qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
    next
      case I_1_ni_1 note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ")
        case ik0 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', LN ''ni'' tid1, ?s'(|NV ''nr'' tid0|),
                                ?s'(|AV ''I'' tid0|), ?s'(|AV ''R'' tid0|)
                             |}
                             ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
        qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
      next
        case ik0_1 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT2'', LN ''ni'' tid1, ?s'(|NV ''nr'' tid0|),
                                ?s'(|AV ''I'' tid0|), ?s'(|AV ''R'' tid0|)
                             |}
                             ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
        qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_3_nr tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT2'', LN ''ni'' tid1, ?s'(|NV ''nr'' tid0|),
                              ?s'(|AV ''I'' tid0|), ?s'(|AV ''R'' tid0|)
                           |}
                           ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
      qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

end