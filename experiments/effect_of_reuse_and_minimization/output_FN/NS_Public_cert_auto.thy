theory NS_Public_cert_auto
imports
  "../ESPLogic"
begin

role I
where "I =
  [ Send ''1'' ( Enc {| sLC ''1'', sLN ''ni'', sLAV ''I'' |}
                     ( sPK ''R'' )
               )
  , Recv ''2'' ( Enc {| sLC ''2'', sLN ''ni'', sLNV ''nr'',
                        sLAV ''R''
                     |}
                     ( sPK ''I'' )
               )
  , Send ''3'' ( Enc {| sLC ''3'', sLNV ''nr'' |} ( sPK ''R'' ) )
  ]"

role R
where "R =
  [ Recv ''1'' ( Enc {| sLC ''1'', sLNV ''ni'', sLAV ''I'' |}
                     ( sPK ''R'' )
               )
  , Send ''2'' ( Enc {| sLC ''2'', sLNV ''ni'', sLN ''nr'',
                        sLAV ''R''
                     |}
                     ( sPK ''I'' )
               )
  , Recv ''3'' ( Enc {| sLC ''3'', sLN ''nr'' |} ( sPK ''R'' ) )
  ]"

protocol ns_public
where "ns_public = { I, R }"

locale atomic_ns_public_state = atomic_state ns_public
locale ns_public_state = reachable_state ns_public

lemma (in atomic_ns_public_state) I_sk_I_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "SK ( s(|AV ''I'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_ns_public_state) I_sk_R_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "SK ( s(|AV ''R'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! " SK ( s(|AV ''R'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_ns_public_state) R_sk_I_secrecy:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "SK ( s(|AV ''I'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_ns_public_state) R_sk_R_secrecy:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "SK ( s(|AV ''R'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! " SK ( s(|AV ''R'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_ns_public_state) I_ni_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "LN ''ni'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''ni'' tid0 ")
  case I_1_ni note facts = facts this[simplified]
  thus ?thesis proof(sources! " SK ( s(|AV ''R'' tid0|) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (I_3_nr tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''2'', LN ''ni'' tid1, LN ''ni'' tid0, s(|AV ''R'' tid1|)
                       |}
                       ( PK ( s(|AV ''I'' tid1|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (R_2_ni tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''1'', LN ''ni'' tid0, s(|AV ''I'' tid1|) |}
                       ( PK ( s(|AV ''R'' tid1|) ) ) ")
    case I_1_enc note facts = facts this[simplified]
    thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_ns_public_state) R_nr_secrecy:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "LN ''nr'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''nr'' tid0 ")
  case (I_3_nr tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''2'', LN ''ni'' tid1, LN ''nr'' tid0, s(|AV ''R'' tid1|)
                       |}
                       ( PK ( s(|AV ''I'' tid1|) ) ) ")
    case R_2_enc note facts = facts this[simplified]
    thus ?thesis proof(sources! " SK ( s(|AV ''R'' tid0|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (R_2_ni tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''1'', LN ''nr'' tid0, s(|AV ''I'' tid1|) |}
                       ( PK ( s(|AV ''R'' tid1|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
next
  case R_2_nr note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''1'', s(|NV ''ni'' tid0|), s(|AV ''I'' tid0|) |}
                       ( PK ( s(|AV ''R'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (I_1_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_ns_public_state) I_nr_secrecy:
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
                   Enc {| LC ''2'', LN ''ni'' tid0, s(|NV ''nr'' tid0|),
                          s(|AV ''R'' tid0|)
                       |}
                       ( PK ( s(|AV ''I'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''ni'' tid0 ")
      case I_1_ni note facts = facts this[simplified]
      thus ?thesis proof(sources! " SK ( s(|AV ''R'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (I_3_nr tid1) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''2'', LN ''ni'' tid1, LN ''ni'' tid0, s(|AV ''R'' tid1|)
                           |}
                           ( PK ( s(|AV ''I'' tid1|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (R_2_ni tid1) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''1'', LN ''ni'' tid0, s(|AV ''I'' tid1|) |}
                           ( PK ( s(|AV ''R'' tid1|) ) ) ")
        case I_1_enc note facts = facts this[simplified]
        thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed
  next
    case (R_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''1'', LN ''ni'' tid0, s(|AV ''I'' tid0|) |}
                         ( PK ( s(|AV ''R'' tid0|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''ni'' tid0 ")
        case (I_3_nr tid2) note facts = facts this[simplified]
        thus ?thesis proof(sources! " LN ''nr'' tid1 ")
          case (I_3_nr tid3) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''2'', LN ''ni'' tid2, LN ''ni'' tid0, s(|AV ''R'' tid2|)
                               |}
                               ( PK ( s(|AV ''I'' tid2|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (R_2_ni tid3) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''1'', LN ''nr'' tid1, s(|AV ''I'' tid3|) |}
                               ( PK ( s(|AV ''R'' tid3|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case R_2_nr note facts = facts this[simplified]
          thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed
      next
        case (R_2_ni tid2) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''1'', LN ''ni'' tid0, s(|AV ''I'' tid2|) |}
                             ( PK ( s(|AV ''R'' tid2|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case I_1_enc note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''nr'' tid1 ")
        case (I_3_nr tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''2'', LN ''ni'' tid3, LN ''nr'' tid1, s(|AV ''R'' tid3|)
                             |}
                             ( PK ( s(|AV ''I'' tid3|) ) ) ")
          case R_2_enc note facts = facts this[simplified]
          thus ?thesis proof(sources! " SK ( s(|AV ''R'' tid0|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (R_2_ni tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''1'', LN ''nr'' tid1, s(|AV ''I'' tid3|) |}
                             ( PK ( s(|AV ''R'' tid3|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case R_2_nr note facts = facts this[simplified]
        thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_ns_public_state) R_ni_secrecy:
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
                   Enc {| LC ''1'', s(|NV ''ni'' tid0|), s(|AV ''I'' tid0|) |}
                       ( PK ( s(|AV ''R'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''3'', LN ''nr'' tid0 |} ( PK ( s(|AV ''R'' tid0|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''nr'' tid0 ")
        case (I_3_nr tid1) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''2'', LN ''ni'' tid1, LN ''nr'' tid0, s(|AV ''R'' tid1|)
                             |}
                             ( PK ( s(|AV ''I'' tid1|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (R_2_ni tid1) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''1'', LN ''nr'' tid0, s(|AV ''I'' tid1|) |}
                             ( PK ( s(|AV ''R'' tid1|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case R_2_nr note facts = facts this[simplified]
        thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed
    next
      case (I_3_enc tid1) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''2'', LN ''ni'' tid1, LN ''nr'' tid0, s(|AV ''R'' tid0|)
                           |}
                           ( PK ( s(|AV ''I'' tid1|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! " LN ''nr'' tid0 ")
          case (I_3_nr tid2) note facts = facts this[simplified]
          thus ?thesis proof(sources! " LN ''ni'' tid1 ")
            case I_1_ni note facts = facts this[simplified]
            thus ?thesis proof(sources! " SK ( s(|AV ''R'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (I_3_nr tid3) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''2'', LN ''ni'' tid2, LN ''nr'' tid0, s(|AV ''R'' tid2|)
                                 |}
                                 ( PK ( s(|AV ''I'' tid2|) ) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (R_2_ni tid3) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''1'', LN ''ni'' tid1, s(|AV ''I'' tid3|) |}
                                 ( PK ( s(|AV ''R'' tid3|) ) ) ")
              case I_1_enc note facts = facts this[simplified]
              thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid1|) ) ")
                case ik0 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''2'', LN ''ni'' tid2, LN ''nr'' tid0, s(|AV ''R'' tid2|)
                                     |}
                                     ( PK ( s(|AV ''I'' tid2|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed
        next
          case (R_2_ni tid2) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''1'', LN ''nr'' tid0, s(|AV ''I'' tid2|) |}
                               ( PK ( s(|AV ''R'' tid2|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case R_2_nr note facts = facts this[simplified]
          thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed
      next
        case R_2_enc note facts = facts this[simplified]
        thus ?thesis proof(sources! " LN ''ni'' tid1 ")
          case (I_3_nr tid3) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''2'', LN ''ni'' tid3, LN ''ni'' tid1, s(|AV ''R'' tid3|)
                               |}
                               ( PK ( s(|AV ''I'' tid3|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (R_2_ni tid3) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''1'', LN ''ni'' tid1, s(|AV ''I'' tid3|) |}
                               ( PK ( s(|AV ''R'' tid3|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (I_1_enc tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''3'', LN ''nr'' tid0 |} ( PK ( s(|AV ''R'' tid0|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''nr'' tid0 ")
        case (I_3_nr tid2) note facts = facts this[simplified]
        thus ?thesis proof(sources! " LN ''ni'' tid1 ")
          case I_1_ni note facts = facts this[simplified]
          thus ?thesis proof(sources! " SK ( s(|AV ''R'' tid0|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (I_3_nr tid3) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''2'', LN ''ni'' tid2, LN ''nr'' tid0, s(|AV ''R'' tid2|)
                               |}
                               ( PK ( s(|AV ''I'' tid2|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (R_2_ni tid3) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''1'', LN ''ni'' tid1, s(|AV ''I'' tid3|) |}
                               ( PK ( s(|AV ''R'' tid3|) ) ) ")
            case I_1_enc note facts = facts this[simplified]
            thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed
      next
        case (R_2_ni tid2) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''1'', LN ''nr'' tid0, s(|AV ''I'' tid2|) |}
                             ( PK ( s(|AV ''R'' tid2|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case R_2_nr note facts = facts this[simplified]
        thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed
    next
      case (I_3_enc tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''ni'' tid1 ")
        case I_1_ni note facts = facts this[simplified]
        thus ?thesis proof(sources! " SK ( s(|AV ''R'' tid0|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (I_3_nr tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''2'', LN ''ni'' tid2, LN ''nr'' tid0, s(|AV ''R'' tid0|)
                             |}
                             ( PK ( s(|AV ''I'' tid2|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! " LN ''nr'' tid0 ")
            case (I_3_nr tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! " LN ''ni'' tid2 ")
              case I_1_ni note facts = facts this[simplified]
              thus ?thesis proof(sources! " SK ( s(|AV ''R'' tid0|) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (I_3_nr tid5) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''2'', LN ''ni'' tid3, LN ''ni'' tid1, s(|AV ''R'' tid3|)
                                   |}
                                   ( PK ( s(|AV ''I'' tid3|) ) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (R_2_ni tid5) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''1'', LN ''ni'' tid2, s(|AV ''I'' tid5|) |}
                                   ( PK ( s(|AV ''R'' tid5|) ) ) ")
                case I_1_enc note facts = facts this[simplified]
                thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid2|) ) ")
                  case ik0 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''2'', LN ''ni'' tid3, LN ''ni'' tid1,
                                          s(|AV ''R'' tid3|)
                                       |}
                                       ( PK ( s(|AV ''I'' tid3|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed
          next
            case (R_2_ni tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''1'', LN ''nr'' tid0, s(|AV ''I'' tid4|) |}
                                 ( PK ( s(|AV ''R'' tid4|) ) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case R_2_nr note facts = facts this[simplified]
            thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed
        next
          case R_2_enc note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''2'', LN ''ni'' tid3, LN ''ni'' tid1, s(|AV ''R'' tid3|)
                               |}
                               ( PK ( s(|AV ''I'' tid3|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (R_2_ni tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''1'', LN ''ni'' tid1, s(|AV ''I'' tid3|) |}
                             ( PK ( s(|AV ''R'' tid3|) ) ) ")
          case I_1_enc note facts = facts this[simplified]
          thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid0|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_ns_public_state) I_ni_synch:
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
       s(|NV ''ni'' tid2|) = LN ''ni'' tid1 &
       s(|NV ''nr'' tid1|) = LN ''nr'' tid2 &
       predOrd t (St(tid1, I_1)) (St(tid2, R_1)) &
       predOrd t (St(tid1, I_2)) (St(tid1, I_3)) &
       predOrd t (St(tid2, R_2)) (St(tid1, I_2)) &
       predOrd t (St(tid2, R_1)) (St(tid2, R_2))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''2'', LN ''ni'' tid1, s(|NV ''nr'' tid1|),
                          s(|AV ''R'' tid1|)
                       |}
                       ( PK ( s(|AV ''I'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''ni'' tid1 ")
      case I_1_ni note facts = facts this[simplified]
      thus ?thesis proof(sources! " SK ( s(|AV ''R'' tid1|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (I_3_nr tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''2'', LN ''ni'' tid2, LN ''ni'' tid1, s(|AV ''R'' tid2|)
                           |}
                           ( PK ( s(|AV ''I'' tid2|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (R_2_ni tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''1'', LN ''ni'' tid1, s(|AV ''I'' tid2|) |}
                           ( PK ( s(|AV ''R'' tid2|) ) ) ")
        case I_1_enc note facts = facts this[simplified]
        thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid1|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed
  next
    case (R_2_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''1'', LN ''ni'' tid1, s(|AV ''I'' tid1|) |}
                         ( PK ( s(|AV ''R'' tid1|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''ni'' tid1 ")
        case (I_3_nr tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''2'', LN ''ni'' tid3, LN ''ni'' tid1, s(|AV ''R'' tid3|)
                             |}
                             ( PK ( s(|AV ''I'' tid3|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (R_2_ni tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''1'', LN ''ni'' tid1, s(|AV ''I'' tid3|) |}
                             ( PK ( s(|AV ''R'' tid3|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case I_1_enc note facts = facts this[simplified]
      thus ?thesis by force
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_ns_public_state) R_ni_synch:
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
                   Enc {| LC ''1'', s(|NV ''ni'' tid1|), s(|AV ''I'' tid1|) |}
                       ( PK ( s(|AV ''R'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''3'', LN ''nr'' tid1 |} ( PK ( s(|AV ''R'' tid1|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''nr'' tid1 ")
        case (I_3_nr tid2) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''2'', LN ''ni'' tid2, LN ''nr'' tid1, s(|AV ''R'' tid2|)
                             |}
                             ( PK ( s(|AV ''I'' tid2|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (R_2_ni tid2) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''1'', LN ''nr'' tid1, s(|AV ''I'' tid2|) |}
                             ( PK ( s(|AV ''R'' tid2|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case R_2_nr note facts = facts this[simplified]
        thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid1|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed
    next
      case (I_3_enc tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''2'', LN ''ni'' tid2, LN ''nr'' tid1, s(|AV ''R'' tid1|)
                           |}
                           ( PK ( s(|AV ''I'' tid2|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! " LN ''nr'' tid1 ")
          case (I_3_nr tid3) note facts = facts this[simplified]
          thus ?thesis proof(sources! " LN ''ni'' tid2 ")
            case I_1_ni note facts = facts this[simplified]
            thus ?thesis proof(sources! " SK ( s(|AV ''R'' tid1|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (I_3_nr tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''2'', LN ''ni'' tid3, LN ''nr'' tid1, s(|AV ''R'' tid3|)
                                 |}
                                 ( PK ( s(|AV ''I'' tid3|) ) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (R_2_ni tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''1'', LN ''ni'' tid2, s(|AV ''I'' tid4|) |}
                                 ( PK ( s(|AV ''R'' tid4|) ) ) ")
              case I_1_enc note facts = facts this[simplified]
              thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid2|) ) ")
                case ik0 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''2'', LN ''ni'' tid3, LN ''nr'' tid1, s(|AV ''R'' tid3|)
                                     |}
                                     ( PK ( s(|AV ''I'' tid3|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed
        next
          case (R_2_ni tid3) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''1'', LN ''nr'' tid1, s(|AV ''I'' tid3|) |}
                               ( PK ( s(|AV ''R'' tid3|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case R_2_nr note facts = facts this[simplified]
          thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid1|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed
      next
        case R_2_enc note facts = facts this[simplified]
        thus ?thesis proof(sources! " LN ''ni'' tid2 ")
          case (I_3_nr tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''2'', LN ''ni'' tid4, LN ''ni'' tid2, s(|AV ''R'' tid4|)
                               |}
                               ( PK ( s(|AV ''I'' tid4|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (R_2_ni tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''1'', LN ''ni'' tid2, s(|AV ''I'' tid4|) |}
                               ( PK ( s(|AV ''R'' tid4|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (I_1_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''3'', LN ''nr'' tid1 |} ( PK ( s(|AV ''R'' tid1|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''nr'' tid1 ")
        case (I_3_nr tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''2'', LN ''ni'' tid3, LN ''nr'' tid1, s(|AV ''R'' tid3|)
                             |}
                             ( PK ( s(|AV ''I'' tid3|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (R_2_ni tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''1'', LN ''nr'' tid1, s(|AV ''I'' tid3|) |}
                             ( PK ( s(|AV ''R'' tid3|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case R_2_nr note facts = facts this[simplified]
        thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid1|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed
    next
      case (I_3_enc tid3) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''2'', LN ''ni'' tid3, LN ''nr'' tid1, s(|AV ''R'' tid1|)
                           |}
                           ( PK ( s(|AV ''I'' tid3|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! " LN ''nr'' tid1 ")
          case (I_3_nr tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! " LN ''ni'' tid3 ")
            case I_1_ni note facts = facts this[simplified]
            thus ?thesis proof(sources! " SK ( s(|AV ''R'' tid1|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (I_3_nr tid5) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''2'', LN ''ni'' tid4, LN ''nr'' tid1, s(|AV ''R'' tid4|)
                                 |}
                                 ( PK ( s(|AV ''I'' tid4|) ) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (R_2_ni tid5) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''1'', LN ''ni'' tid3, s(|AV ''I'' tid5|) |}
                                 ( PK ( s(|AV ''R'' tid5|) ) ) ")
              case I_1_enc note facts = facts this[simplified]
              thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid3|) ) ")
                case ik0 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''2'', LN ''ni'' tid4, LN ''nr'' tid1, s(|AV ''R'' tid4|)
                                     |}
                                     ( PK ( s(|AV ''I'' tid4|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed
        next
          case (R_2_ni tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''1'', LN ''nr'' tid1, s(|AV ''I'' tid4|) |}
                               ( PK ( s(|AV ''R'' tid4|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case R_2_nr note facts = facts this[simplified]
          thus ?thesis proof(sources! " SK ( s(|AV ''I'' tid1|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed
      next
        case R_2_enc note facts = facts this[simplified]
        thus ?thesis by force
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in ns_public_state) weak_atomicity:
  "complete (t,r,s) atomicAnn"
proof (cases rule: complete_atomicAnnI[completeness_cases_rule])
  case (I_2_nr t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state ns_public t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''2'', LN ''ni'' tid0, ?s'(|NV ''nr'' tid0|),
             ?s'(|AV ''R'' tid0|)
          |}
          ( PK ( ?s'(|AV ''I'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (R_1_ni t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state ns_public t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''1'', ?s'(|NV ''ni'' tid0|), ?s'(|AV ''I'' tid0|) |}
          ( PK ( ?s'(|AV ''R'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
qed

end