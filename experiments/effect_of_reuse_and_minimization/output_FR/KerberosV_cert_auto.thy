theory KerberosV_cert_auto
imports
  "../ESPLogic"
begin

role A
where "A =
  [ Recv ''1'' {| sLAV ''C'', sLAV ''T'', sLNV ''n1'' |}
  , Send ''2'' {| Enc {| sLC ''TT21'', sLN ''AuthKey'', sLAV ''C'' |}
                      ( sK ''T'' ''A'' ),
                  Enc {| sLC ''TT22'', sLN ''AuthKey'', sLNV ''n1'', sLAV ''T'' |}
                      ( sK ''C'' ''A'' )
               |}
  ]"

role C
where "C =
  [ Send ''1'' {| sLAV ''C'', sLAV ''T'', sLN ''n1'' |}
  , Recv ''2'' {| sLNV ''TicketGrantingTicket'',
                  Enc {| sLC ''TT22'', sLNV ''AuthKey'', sLN ''n1'', sLAV ''T'' |}
                      ( sK ''C'' ''A'' )
               |}
  , Send ''3'' {| sLNV ''TicketGrantingTicket'',
                  Enc {| sLC ''TT3'', sLAV ''C'' |} ( sLNV ''AuthKey'' ), sLAV ''C'',
                  sLAV ''S'', sLN ''n2''
               |}
  , Recv ''4'' {| sLAV ''C'', sLNV ''ServerTicket'',
                  Enc {| sLC ''TT42'', sLNV ''ServerKey'', sLN ''n2'', sLAV ''S'' |}
                      ( sLNV ''AuthKey'' )
               |}
  , Send ''5'' {| sLNV ''ServerTicket'',
                  Enc {| sLC ''TT5'', sLAV ''C'', sLN ''t'' |} ( sLNV ''ServerKey'' )
               |}
  , Recv ''6'' ( Enc {| sLC ''TT6'', sLN ''t'' |}
                     ( sLNV ''ServerKey'' )
               )
  ]"

role S
where "S =
  [ Recv ''5'' {| Enc {| sLC ''TT41'', sLNV ''ServerKey'', sLAV ''C''
                      |}
                      ( sK ''S'' ''T'' ),
                  Enc {| sLC ''TT5'', sLAV ''C'', sLNV ''t'' |}
                      ( sLNV ''ServerKey'' )
               |}
  , Send ''6'' ( Enc {| sLC ''TT6'', sLNV ''t'' |}
                     ( sLNV ''ServerKey'' )
               )
  ]"

role T
where "T =
  [ Recv ''3'' {| Enc {| sLC ''TT21'', sLNV ''AuthKey'', sLAV ''C''
                      |}
                      ( sK ''T'' ''A'' ),
                  Enc {| sLC ''TT3'', sLAV ''C'' |} ( sLNV ''AuthKey'' ), sLAV ''C'',
                  sLAV ''S'', sLNV ''n2''
               |}
  , Send ''4'' {| sLAV ''C'',
                  Enc {| sLC ''TT41'', sLN ''ServerKey'', sLAV ''C'' |}
                      ( sK ''S'' ''T'' ),
                  Enc {| sLC ''TT42'', sLN ''ServerKey'', sLNV ''n2'', sLAV ''S'' |}
                      ( sLNV ''AuthKey'' )
               |}
  ]"

protocol KerberosV
where "KerberosV = { A, C, S, T }"

locale atomic_KerberosV_state = atomic_state KerberosV
locale KerberosV_state = reachable_state KerberosV

lemma (in atomic_KerberosV_state) A_ltk_T_A_sec:
  assumes facts:
    "roleMap r tid0 = Some A"
    "s(|AV ''A'' tid0|) ~: Compromised"
    "s(|AV ''T'' tid0|) ~: Compromised"
    "K ( s(|AV ''T'' tid0|) ) ( s(|AV ''A'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''T'' tid0|) ) ( s(|AV ''A'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_KerberosV_state) A_ltk_C_A_sec:
  assumes facts:
    "roleMap r tid0 = Some A"
    "s(|AV ''A'' tid0|) ~: Compromised"
    "s(|AV ''C'' tid0|) ~: Compromised"
    "K ( s(|AV ''C'' tid0|) ) ( s(|AV ''A'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''C'' tid0|) ) ( s(|AV ''A'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_KerberosV_state) C_ltk_C_A_sec:
  assumes facts:
    "roleMap r tid0 = Some C"
    "s(|AV ''A'' tid0|) ~: Compromised"
    "s(|AV ''C'' tid0|) ~: Compromised"
    "K ( s(|AV ''C'' tid0|) ) ( s(|AV ''A'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''C'' tid0|) ) ( s(|AV ''A'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_KerberosV_state) T_ltk_T_A_sec:
  assumes facts:
    "roleMap r tid0 = Some T"
    "s(|AV ''A'' tid0|) ~: Compromised"
    "s(|AV ''T'' tid0|) ~: Compromised"
    "K ( s(|AV ''T'' tid0|) ) ( s(|AV ''A'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''T'' tid0|) ) ( s(|AV ''A'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_KerberosV_state) T_ltk_S_T_sec:
  assumes facts:
    "roleMap r tid0 = Some T"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "s(|AV ''T'' tid0|) ~: Compromised"
    "K ( s(|AV ''S'' tid0|) ) ( s(|AV ''T'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''S'' tid0|) ) ( s(|AV ''T'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_KerberosV_state) S_ltk_S_T_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "s(|AV ''T'' tid0|) ~: Compromised"
    "K ( s(|AV ''S'' tid0|) ) ( s(|AV ''T'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''S'' tid0|) ) ( s(|AV ''T'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_KerberosV_state) A_AuthKey_sec:
  assumes facts:
    "roleMap r tid0 = Some A"
    "s(|AV ''A'' tid0|) ~: Compromised"
    "s(|AV ''C'' tid0|) ~: Compromised"
    "s(|AV ''T'' tid0|) ~: Compromised"
    "LN ''AuthKey'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''AuthKey'' tid0 ")
  case A_2_AuthKey note facts = facts this[simplified]
  thus ?thesis by (fastsimp dest: A_ltk_T_A_sec intro: event_predOrdI)
next
  case A_2_AuthKey_1 note facts = facts this[simplified]
  thus ?thesis by (fastsimp dest: A_ltk_C_A_sec intro: event_predOrdI)
next
  case (S_6_t tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT41'', s(|NV ''ServerKey'' tid1|), s(|AV ''C'' tid1|)
                       |}
                       ( K ( s(|AV ''S'' tid1|) ) ( s(|AV ''T'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''AuthKey'' tid0 |}
                         ( s(|NV ''ServerKey'' tid1|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (T_4_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''ServerKey'' tid2 ")
      case (S_6_t tid3) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid2|), s(|AV ''C'' tid1|) |}
                           ( K ( s(|AV ''T'' tid1|) ) ( s(|AV ''A'' tid2|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT3'', s(|AV ''C'' tid1|) |}
                             ( s(|NV ''AuthKey'' tid2|) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''AuthKey'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (C_3_enc tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''AuthKey'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (A_2_enc tid4) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''AuthKey'' tid0 |}
                             ( LN ''ServerKey'' tid2 ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case T_4_ServerKey note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''S'' tid1|) ) ( s(|AV ''T'' tid1|) ) ")
        case ik0 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid2|), s(|AV ''C'' tid1|) |}
                             ( K ( s(|AV ''T'' tid1|) ) ( s(|AV ''A'' tid2|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT3'', s(|AV ''C'' tid1|) |}
                               ( s(|NV ''AuthKey'' tid2|) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''AuthKey'' tid0 |}
                                 ( LN ''ServerKey'' tid2 ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (C_3_enc tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''AuthKey'' tid0 |}
                                 ( LN ''ServerKey'' tid2 ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (A_2_enc tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''AuthKey'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case ik0_1 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid2|), s(|AV ''C'' tid1|) |}
                             ( K ( s(|AV ''T'' tid1|) ) ( s(|AV ''A'' tid2|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT3'', s(|AV ''C'' tid1|) |}
                               ( s(|NV ''AuthKey'' tid2|) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''AuthKey'' tid0 |}
                                 ( LN ''ServerKey'' tid2 ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (C_3_enc tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''AuthKey'' tid0 |}
                                 ( LN ''ServerKey'' tid2 ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (A_2_enc tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''AuthKey'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case T_4_ServerKey_1 note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid2|), s(|AV ''C'' tid1|) |}
                           ( K ( s(|AV ''T'' tid1|) ) ( s(|AV ''A'' tid2|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT3'', s(|AV ''C'' tid1|) |}
                             ( s(|NV ''AuthKey'' tid2|) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''AuthKey'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (C_3_enc tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''AuthKey'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (A_2_enc tid4) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''AuthKey'' tid0 |}
                             ( LN ''ServerKey'' tid2 ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_KerberosV_state) C_AuthKey_sec:
  assumes facts:
    "roleMap r tid0 = Some C"
    "s(|AV ''A'' tid0|) ~: Compromised"
    "s(|AV ''C'' tid0|) ~: Compromised"
    "s(|AV ''T'' tid0|) ~: Compromised"
    "(tid0, C_2) : steps t"
    "s(|NV ''AuthKey'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT22'', s(|NV ''AuthKey'' tid0|), LN ''n1'' tid0,
                          s(|AV ''T'' tid0|)
                       |}
                       ( K ( s(|AV ''C'' tid0|) ) ( s(|AV ''A'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: C_ltk_C_A_sec intro: event_predOrdI)
  next
    case (A_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_KerberosV_state) T_AuthKey_sec:
  assumes facts:
    "roleMap r tid0 = Some T"
    "s(|AV ''A'' tid0|) ~: Compromised"
    "s(|AV ''C'' tid0|) ~: Compromised"
    "s(|AV ''T'' tid0|) ~: Compromised"
    "(tid0, T_3) : steps t"
    "s(|NV ''AuthKey'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid0|), s(|AV ''C'' tid0|) |}
                       ( K ( s(|AV ''T'' tid0|) ) ( s(|AV ''A'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: T_ltk_T_A_sec intro: event_predOrdI)
  next
    case (A_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_KerberosV_state) T_ServerKey_sec:
  assumes facts:
    "roleMap r tid0 = Some T"
    "s(|AV ''A'' tid0|) ~: Compromised"
    "s(|AV ''C'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "s(|AV ''T'' tid0|) ~: Compromised"
    "LN ''ServerKey'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''ServerKey'' tid0 ")
  case (S_6_t tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT41'', s(|NV ''ServerKey'' tid1|), s(|AV ''C'' tid1|)
                       |}
                       ( K ( s(|AV ''S'' tid1|) ) ( s(|AV ''T'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''ServerKey'' tid0 |}
                         ( s(|NV ''ServerKey'' tid1|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (T_4_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''ServerKey'' tid2 ")
      case (S_6_t tid3) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid2|), s(|AV ''C'' tid1|) |}
                           ( K ( s(|AV ''T'' tid1|) ) ( s(|AV ''A'' tid2|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT3'', s(|AV ''C'' tid1|) |}
                             ( s(|NV ''AuthKey'' tid2|) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''ServerKey'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (C_3_enc tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''ServerKey'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (A_2_enc tid4) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''ServerKey'' tid0 |}
                             ( LN ''ServerKey'' tid2 ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case T_4_ServerKey note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''S'' tid1|) ) ( s(|AV ''T'' tid1|) ) ")
        case ik0 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid2|), s(|AV ''C'' tid1|) |}
                             ( K ( s(|AV ''T'' tid1|) ) ( s(|AV ''A'' tid2|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT3'', s(|AV ''C'' tid1|) |}
                               ( s(|NV ''AuthKey'' tid2|) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''ServerKey'' tid0 |}
                                 ( LN ''ServerKey'' tid2 ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (C_3_enc tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''ServerKey'' tid0 |}
                                 ( LN ''ServerKey'' tid2 ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (A_2_enc tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''ServerKey'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case ik0_1 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid2|), s(|AV ''C'' tid1|) |}
                             ( K ( s(|AV ''T'' tid1|) ) ( s(|AV ''A'' tid2|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT3'', s(|AV ''C'' tid1|) |}
                               ( s(|NV ''AuthKey'' tid2|) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''ServerKey'' tid0 |}
                                 ( LN ''ServerKey'' tid2 ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (C_3_enc tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''ServerKey'' tid0 |}
                                 ( LN ''ServerKey'' tid2 ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (A_2_enc tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''ServerKey'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case T_4_ServerKey_1 note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid2|), s(|AV ''C'' tid1|) |}
                           ( K ( s(|AV ''T'' tid1|) ) ( s(|AV ''A'' tid2|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT3'', s(|AV ''C'' tid1|) |}
                             ( s(|NV ''AuthKey'' tid2|) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''ServerKey'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (C_3_enc tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''ServerKey'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (A_2_enc tid4) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''ServerKey'' tid0 |}
                             ( LN ''ServerKey'' tid2 ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
next
  case T_4_ServerKey note facts = facts this[simplified]
  thus ?thesis by (fastsimp dest: T_ltk_S_T_sec intro: event_predOrdI)
next
  case T_4_ServerKey_1 note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid0|), s(|AV ''C'' tid0|) |}
                       ( K ( s(|AV ''T'' tid0|) ) ( s(|AV ''A'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: T_ltk_T_A_sec intro: event_predOrdI)
  next
    case (A_2_enc tid2) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
  qed (insert facts, ((clarsimp, order?))+)?
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_KerberosV_state) C_ServerKey_sec:
  assumes facts:
    "roleMap r tid0 = Some C"
    "s(|AV ''A'' tid0|) ~: Compromised"
    "s(|AV ''C'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "s(|AV ''T'' tid0|) ~: Compromised"
    "(tid0, C_4) : steps t"
    "s(|NV ''ServerKey'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT22'', s(|NV ''AuthKey'' tid0|), LN ''n1'' tid0,
                          s(|AV ''T'' tid0|)
                       |}
                       ( K ( s(|AV ''C'' tid0|) ) ( s(|AV ''A'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: C_ltk_C_A_sec intro: event_predOrdI)
  next
    case (A_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''n1'' tid0 ")
      case C_1_n1 note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT42'', s(|NV ''ServerKey'' tid0|), LN ''n2'' tid0,
                              s(|AV ''S'' tid0|)
                           |}
                           ( LN ''AuthKey'' tid1 ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
      next
        case (T_4_enc tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! " LN ''n2'' tid0 ")
          case C_3_n2 note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT21'', LN ''AuthKey'' tid1, s(|AV ''C'' tid3|) |}
                               ( K ( s(|AV ''T'' tid3|) ) ( s(|AV ''A'' tid3|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
          next
            case A_2_enc note facts = facts this[simplified]
            thus ?thesis by (fastsimp dest: T_ServerKey_sec intro: event_predOrdI)
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (S_6_t tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT21'', LN ''AuthKey'' tid1, s(|AV ''C'' tid3|) |}
                               ( K ( s(|AV ''T'' tid3|) ) ( s(|AV ''A'' tid3|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
          next
            case A_2_enc note facts = facts this[simplified]
            thus ?thesis by (fastsimp dest: T_ServerKey_sec intro: event_predOrdI)
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_6_t tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT42'', s(|NV ''ServerKey'' tid0|), LN ''n2'' tid0,
                              s(|AV ''S'' tid0|)
                           |}
                           ( LN ''AuthKey'' tid1 ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
      next
        case (T_4_enc tid3) note facts = facts this[simplified]
        thus ?thesis proof(sources! " LN ''n2'' tid0 ")
          case C_3_n2 note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT21'', LN ''AuthKey'' tid1, s(|AV ''C'' tid3|) |}
                               ( K ( s(|AV ''T'' tid3|) ) ( s(|AV ''A'' tid3|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
          next
            case A_2_enc note facts = facts this[simplified]
            thus ?thesis by (fastsimp dest: T_ServerKey_sec intro: event_predOrdI)
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (S_6_t tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT21'', LN ''AuthKey'' tid1, s(|AV ''C'' tid3|) |}
                               ( K ( s(|AV ''T'' tid3|) ) ( s(|AV ''A'' tid3|) ) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
          next
            case A_2_enc note facts = facts this[simplified]
            thus ?thesis by (fastsimp dest: T_ServerKey_sec intro: event_predOrdI)
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_KerberosV_state) C_t_sec:
  assumes facts:
    "roleMap r tid0 = Some C"
    "s(|AV ''A'' tid0|) ~: Compromised"
    "s(|AV ''C'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "s(|AV ''T'' tid0|) ~: Compromised"
    "LN ''t'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''t'' tid0 ")
  case C_5_t note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT22'', s(|NV ''AuthKey'' tid0|), LN ''n1'' tid0,
                          s(|AV ''T'' tid0|)
                       |}
                       ( K ( s(|AV ''C'' tid0|) ) ( s(|AV ''A'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: C_ltk_C_A_sec intro: event_predOrdI)
  next
    case (A_2_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''n1'' tid0 ")
      case C_1_n1 note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT42'', s(|NV ''ServerKey'' tid0|), LN ''n2'' tid0,
                              s(|AV ''S'' tid0|)
                           |}
                           ( LN ''AuthKey'' tid2 ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
      next
        case (T_4_enc tid4) note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: C_ServerKey_sec intro: event_predOrdI)
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_6_t tid3) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT42'', s(|NV ''ServerKey'' tid0|), LN ''n2'' tid0,
                              s(|AV ''S'' tid0|)
                           |}
                           ( LN ''AuthKey'' tid2 ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
      next
        case (T_4_enc tid4) note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: C_ServerKey_sec intro: event_predOrdI)
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (S_6_t tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT41'', s(|NV ''ServerKey'' tid1|), s(|AV ''C'' tid1|)
                       |}
                       ( K ( s(|AV ''S'' tid1|) ) ( s(|AV ''T'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''t'' tid0 |}
                         ( s(|NV ''ServerKey'' tid1|) ) ")
      case C_5_enc note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: C_ServerKey_sec intro: event_predOrdI)
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (T_4_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''ServerKey'' tid2 ")
      case (S_6_t tid3) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid2|), s(|AV ''C'' tid1|) |}
                           ( K ( s(|AV ''T'' tid1|) ) ( s(|AV ''A'' tid2|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT3'', s(|AV ''C'' tid1|) |}
                             ( s(|NV ''AuthKey'' tid2|) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''t'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
            case C_5_enc note facts = facts this[simplified]
            thus ?thesis by (fastsimp dest: C_ServerKey_sec intro: event_predOrdI)
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (C_3_enc tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''t'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
            case C_5_enc note facts = facts this[simplified]
            thus ?thesis by (fastsimp dest: C_ServerKey_sec intro: event_predOrdI)
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (A_2_enc tid4) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''t'' tid0 |}
                             ( LN ''ServerKey'' tid2 ) ")
          case C_5_enc note facts = facts this[simplified]
          thus ?thesis by (fastsimp dest: C_ServerKey_sec intro: event_predOrdI)
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case T_4_ServerKey note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''S'' tid1|) ) ( s(|AV ''T'' tid1|) ) ")
        case ik0 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid2|), s(|AV ''C'' tid1|) |}
                             ( K ( s(|AV ''T'' tid1|) ) ( s(|AV ''A'' tid2|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT3'', s(|AV ''C'' tid1|) |}
                               ( s(|NV ''AuthKey'' tid2|) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''t'' tid0 |}
                                 ( LN ''ServerKey'' tid2 ) ")
              case C_5_enc note facts = facts this[simplified]
              thus ?thesis by (fastsimp dest: C_ServerKey_sec intro: event_predOrdI)
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (C_3_enc tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''t'' tid0 |}
                                 ( LN ''ServerKey'' tid2 ) ")
              case C_5_enc note facts = facts this[simplified]
              thus ?thesis by (fastsimp dest: C_ServerKey_sec intro: event_predOrdI)
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (A_2_enc tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''t'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
            case C_5_enc note facts = facts this[simplified]
            thus ?thesis by (fastsimp dest: C_ServerKey_sec intro: event_predOrdI)
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case ik0_1 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid2|), s(|AV ''C'' tid1|) |}
                             ( K ( s(|AV ''T'' tid1|) ) ( s(|AV ''A'' tid2|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT3'', s(|AV ''C'' tid1|) |}
                               ( s(|NV ''AuthKey'' tid2|) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''t'' tid0 |}
                                 ( LN ''ServerKey'' tid2 ) ")
              case C_5_enc note facts = facts this[simplified]
              thus ?thesis by (fastsimp dest: C_ServerKey_sec intro: event_predOrdI)
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (C_3_enc tid4) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''t'' tid0 |}
                                 ( LN ''ServerKey'' tid2 ) ")
              case C_5_enc note facts = facts this[simplified]
              thus ?thesis by (fastsimp dest: C_ServerKey_sec intro: event_predOrdI)
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (A_2_enc tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''t'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
            case C_5_enc note facts = facts this[simplified]
            thus ?thesis by (fastsimp dest: C_ServerKey_sec intro: event_predOrdI)
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case T_4_ServerKey_1 note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid2|), s(|AV ''C'' tid1|) |}
                           ( K ( s(|AV ''T'' tid1|) ) ( s(|AV ''A'' tid2|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT3'', s(|AV ''C'' tid1|) |}
                             ( s(|NV ''AuthKey'' tid2|) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''t'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
            case C_5_enc note facts = facts this[simplified]
            thus ?thesis by (fastsimp dest: C_ServerKey_sec intro: event_predOrdI)
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (C_3_enc tid4) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''t'' tid0 |}
                               ( LN ''ServerKey'' tid2 ) ")
            case C_5_enc note facts = facts this[simplified]
            thus ?thesis by (fastsimp dest: C_ServerKey_sec intro: event_predOrdI)
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (A_2_enc tid4) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''t'' tid0 |}
                             ( LN ''ServerKey'' tid2 ) ")
          case C_5_enc note facts = facts this[simplified]
          thus ?thesis by (fastsimp dest: C_ServerKey_sec intro: event_predOrdI)
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_KerberosV_state) C_n1_first_send:
  assumes facts:
    "roleMap r tid1 = Some C"
    "LN ''n1'' tid1 : knows t"
  shows "predOrd t (St(tid1, C_1)) (Ln(LN ''n1'' tid1))"
using facts proof(sources! " LN ''n1'' tid1 ")
  case C_1_n1 note facts = facts this[simplified]
  thus ?thesis by force
next
  case (S_6_t tid2) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT41'', s(|NV ''ServerKey'' tid2|), s(|AV ''C'' tid2|)
                       |}
                       ( K ( s(|AV ''S'' tid2|) ) ( s(|AV ''T'' tid2|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n1'' tid1 |}
                         ( s(|NV ''ServerKey'' tid2|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (T_4_enc tid3) note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''ServerKey'' tid3 ")
      case (S_6_t tid4) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid3|), s(|AV ''C'' tid2|) |}
                           ( K ( s(|AV ''T'' tid2|) ) ( s(|AV ''A'' tid3|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT3'', s(|AV ''C'' tid2|) |}
                             ( s(|NV ''AuthKey'' tid3|) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n1'' tid1 |}
                               ( LN ''ServerKey'' tid3 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (C_3_enc tid5) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n1'' tid1 |}
                               ( LN ''ServerKey'' tid3 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (A_2_enc tid5) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n1'' tid1 |}
                             ( LN ''ServerKey'' tid3 ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case T_4_ServerKey note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''S'' tid2|) ) ( s(|AV ''T'' tid2|) ) ")
        case ik0 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid3|), s(|AV ''C'' tid2|) |}
                             ( K ( s(|AV ''T'' tid2|) ) ( s(|AV ''A'' tid3|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT3'', s(|AV ''C'' tid2|) |}
                               ( s(|NV ''AuthKey'' tid3|) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n1'' tid1 |}
                                 ( LN ''ServerKey'' tid3 ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (C_3_enc tid5) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n1'' tid1 |}
                                 ( LN ''ServerKey'' tid3 ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (A_2_enc tid5) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n1'' tid1 |}
                               ( LN ''ServerKey'' tid3 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case ik0_1 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid3|), s(|AV ''C'' tid2|) |}
                             ( K ( s(|AV ''T'' tid2|) ) ( s(|AV ''A'' tid3|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT3'', s(|AV ''C'' tid2|) |}
                               ( s(|NV ''AuthKey'' tid3|) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n1'' tid1 |}
                                 ( LN ''ServerKey'' tid3 ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (C_3_enc tid5) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n1'' tid1 |}
                                 ( LN ''ServerKey'' tid3 ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (A_2_enc tid5) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n1'' tid1 |}
                               ( LN ''ServerKey'' tid3 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case T_4_ServerKey_1 note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid3|), s(|AV ''C'' tid2|) |}
                           ( K ( s(|AV ''T'' tid2|) ) ( s(|AV ''A'' tid3|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT3'', s(|AV ''C'' tid2|) |}
                             ( s(|NV ''AuthKey'' tid3|) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n1'' tid1 |}
                               ( LN ''ServerKey'' tid3 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (C_3_enc tid5) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n1'' tid1 |}
                               ( LN ''ServerKey'' tid3 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (A_2_enc tid5) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n1'' tid1 |}
                             ( LN ''ServerKey'' tid3 ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_KerberosV_state) C_n2_first_send:
  assumes facts:
    "roleMap r tid1 = Some C"
    "LN ''n2'' tid1 : knows t"
  shows "predOrd t (St(tid1, C_3)) (Ln(LN ''n2'' tid1))"
using facts proof(sources! " LN ''n2'' tid1 ")
  case C_3_n2 note facts = facts this[simplified]
  thus ?thesis by force
next
  case (S_6_t tid2) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT41'', s(|NV ''ServerKey'' tid2|), s(|AV ''C'' tid2|)
                       |}
                       ( K ( s(|AV ''S'' tid2|) ) ( s(|AV ''T'' tid2|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n2'' tid1 |}
                         ( s(|NV ''ServerKey'' tid2|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (T_4_enc tid3) note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''ServerKey'' tid3 ")
      case (S_6_t tid4) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid3|), s(|AV ''C'' tid2|) |}
                           ( K ( s(|AV ''T'' tid2|) ) ( s(|AV ''A'' tid3|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT3'', s(|AV ''C'' tid2|) |}
                             ( s(|NV ''AuthKey'' tid3|) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n2'' tid1 |}
                               ( LN ''ServerKey'' tid3 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (C_3_enc tid5) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n2'' tid1 |}
                               ( LN ''ServerKey'' tid3 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (A_2_enc tid5) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n2'' tid1 |}
                             ( LN ''ServerKey'' tid3 ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case T_4_ServerKey note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''S'' tid2|) ) ( s(|AV ''T'' tid2|) ) ")
        case ik0 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid3|), s(|AV ''C'' tid2|) |}
                             ( K ( s(|AV ''T'' tid2|) ) ( s(|AV ''A'' tid3|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT3'', s(|AV ''C'' tid2|) |}
                               ( s(|NV ''AuthKey'' tid3|) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n2'' tid1 |}
                                 ( LN ''ServerKey'' tid3 ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (C_3_enc tid5) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n2'' tid1 |}
                                 ( LN ''ServerKey'' tid3 ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (A_2_enc tid5) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n2'' tid1 |}
                               ( LN ''ServerKey'' tid3 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case ik0_1 note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid3|), s(|AV ''C'' tid2|) |}
                             ( K ( s(|AV ''T'' tid2|) ) ( s(|AV ''A'' tid3|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT3'', s(|AV ''C'' tid2|) |}
                               ( s(|NV ''AuthKey'' tid3|) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n2'' tid1 |}
                                 ( LN ''ServerKey'' tid3 ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (C_3_enc tid5) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n2'' tid1 |}
                                 ( LN ''ServerKey'' tid3 ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (A_2_enc tid5) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n2'' tid1 |}
                               ( LN ''ServerKey'' tid3 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case T_4_ServerKey_1 note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid3|), s(|AV ''C'' tid2|) |}
                           ( K ( s(|AV ''T'' tid2|) ) ( s(|AV ''A'' tid3|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT3'', s(|AV ''C'' tid2|) |}
                             ( s(|NV ''AuthKey'' tid3|) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n2'' tid1 |}
                               ( LN ''ServerKey'' tid3 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (C_3_enc tid5) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n2'' tid1 |}
                               ( LN ''ServerKey'' tid3 ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (A_2_enc tid5) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT5'', s(|AV ''C'' tid2|), LN ''n2'' tid1 |}
                             ( LN ''ServerKey'' tid3 ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_KerberosV_state) C_ni_synch:
  assumes facts:
    "roleMap r tid1 = Some C"
    "s(|AV ''A'' tid1|) ~: Compromised"
    "s(|AV ''C'' tid1|) ~: Compromised"
    "s(|AV ''S'' tid1|) ~: Compromised"
    "s(|AV ''T'' tid1|) ~: Compromised"
    "(tid1, C_6) : steps t"
  shows
    "? tid2 tid3 tid4.
       roleMap r tid2 = Some A &
       roleMap r tid3 = Some T &
       roleMap r tid4 = Some S &
       s(|AV ''A'' tid2|) = s(|AV ''A'' tid1|) &
       s(|AV ''A'' tid3|) = s(|AV ''A'' tid1|) &
       s(|AV ''C'' tid2|) = s(|AV ''C'' tid1|) &
       s(|AV ''C'' tid3|) = s(|AV ''C'' tid1|) &
       s(|AV ''C'' tid4|) = s(|AV ''C'' tid1|) &
       s(|AV ''S'' tid3|) = s(|AV ''S'' tid1|) &
       s(|AV ''S'' tid4|) = s(|AV ''S'' tid1|) &
       s(|AV ''T'' tid2|) = s(|AV ''T'' tid1|) &
       s(|AV ''T'' tid3|) = s(|AV ''T'' tid1|) &
       s(|AV ''T'' tid4|) = s(|AV ''T'' tid1|) &
       s(|NV ''AuthKey'' tid1|) = LN ''AuthKey'' tid2 &
       s(|NV ''AuthKey'' tid3|) = LN ''AuthKey'' tid2 &
       s(|NV ''ServerKey'' tid1|) = LN ''ServerKey'' tid3 &
       s(|NV ''ServerKey'' tid4|) = LN ''ServerKey'' tid3 &
       s(|NV ''n1'' tid2|) = LN ''n1'' tid1 &
       s(|NV ''n2'' tid3|) = LN ''n2'' tid1 &
       s(|NV ''t'' tid4|) = LN ''t'' tid1 &
       predOrd t (St(tid1, C_1)) (St(tid2, A_1)) &
       predOrd t (St(tid1, C_3)) (St(tid3, T_3)) &
       predOrd t (St(tid1, C_5)) (St(tid4, S_5)) &
       predOrd t (St(tid1, C_2)) (St(tid1, C_3)) &
       predOrd t (St(tid1, C_4)) (St(tid1, C_5)) &
       predOrd t (St(tid2, A_2)) (St(tid1, C_2)) &
       predOrd t (St(tid2, A_1)) (St(tid2, A_2)) &
       predOrd t (St(tid3, T_4)) (St(tid1, C_4)) &
       predOrd t (St(tid3, T_3)) (St(tid3, T_4)) &
       predOrd t (St(tid4, S_6)) (St(tid1, C_6)) &
       predOrd t (St(tid4, S_5)) (St(tid4, S_6))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT22'', s(|NV ''AuthKey'' tid1|), LN ''n1'' tid1,
                          s(|AV ''T'' tid1|)
                       |}
                       ( K ( s(|AV ''C'' tid1|) ) ( s(|AV ''A'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: C_ltk_C_A_sec intro: event_predOrdI)
  next
    case (A_2_enc tid2) note facts = facts this[simplified]
    have f1: "roleMap r tid1 = Some C" using facts by (auto intro: event_predOrdI)
    have f2: "LN ''n1'' tid1 : knows t" using facts by (auto intro: event_predOrdI)
    note facts = facts C_n1_first_send[OF f1 f2, simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT6'', LN ''t'' tid1 |}
                         ( s(|NV ''ServerKey'' tid1|) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: C_ServerKey_sec intro: event_predOrdI)
    next
      case (S_6_enc tid3) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT41'', s(|NV ''ServerKey'' tid1|), s(|AV ''C'' tid3|)
                           |}
                           ( K ( s(|AV ''S'' tid3|) ) ( s(|AV ''T'' tid3|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: C_ServerKey_sec intro: event_predOrdI)
      next
        case (T_4_enc tid4) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid4|), s(|AV ''C'' tid3|) |}
                             ( K ( s(|AV ''T'' tid3|) ) ( s(|AV ''A'' tid4|) ) ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT3'', s(|AV ''C'' tid3|) |}
                               ( s(|NV ''AuthKey'' tid4|) ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT42'', LN ''ServerKey'' tid4, LN ''n2'' tid1,
                                    s(|AV ''S'' tid1|)
                                 |}
                                 ( LN ''AuthKey'' tid2 ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
            next
              case T_4_enc note facts = facts this[simplified]
              thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (C_3_enc tid5) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT42'', LN ''ServerKey'' tid4, LN ''n2'' tid1,
                                    s(|AV ''S'' tid1|)
                                 |}
                                 ( LN ''AuthKey'' tid2 ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
            next
              case T_4_enc note facts = facts this[simplified]
              thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (A_2_enc tid5) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT42'', LN ''ServerKey'' tid4, LN ''n2'' tid1,
                                  s(|AV ''S'' tid1|)
                               |}
                               ( LN ''AuthKey'' tid2 ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
          next
            case T_4_enc note facts = facts this[simplified]
            have f1: "roleMap r tid1 = Some C" using facts by (auto intro: event_predOrdI)
            have f2: "LN ''n2'' tid1 : knows t" using facts by (auto intro: event_predOrdI)
            note facts = facts C_n2_first_send[OF f1 f2, simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT3'', s(|AV ''C'' tid1|) |} ( LN ''AuthKey'' tid2 ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
            next
              case (C_3_enc tid7) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''TT5'', s(|AV ''C'' tid1|), LN ''t'' tid1 |}
                                   ( LN ''ServerKey'' tid4 ) ")
                case fake note facts = facts this[simplified]
                thus ?thesis by (fastsimp dest: T_ServerKey_sec intro: event_predOrdI)
              next
                case C_5_enc note facts = facts this[simplified]
                thus ?thesis by force
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_KerberosV_state) T_ni_synch:
  assumes facts:
    "roleMap r tid3 = Some T"
    "s(|AV ''A'' tid3|) ~: Compromised"
    "s(|AV ''C'' tid3|) ~: Compromised"
    "s(|AV ''T'' tid3|) ~: Compromised"
    "(tid3, T_3) : steps t"
  shows
    "? tid1 tid2.
       roleMap r tid1 = Some C &
       roleMap r tid2 = Some A &
       s(|AV ''A'' tid2|) = s(|AV ''A'' tid1|) &
       s(|AV ''A'' tid3|) = s(|AV ''A'' tid1|) &
       s(|AV ''C'' tid2|) = s(|AV ''C'' tid1|) &
       s(|AV ''C'' tid3|) = s(|AV ''C'' tid1|) &
       s(|AV ''T'' tid2|) = s(|AV ''T'' tid1|) &
       s(|AV ''T'' tid3|) = s(|AV ''T'' tid1|) &
       s(|NV ''AuthKey'' tid1|) = LN ''AuthKey'' tid2 &
       s(|NV ''AuthKey'' tid3|) = LN ''AuthKey'' tid2 &
       s(|NV ''n1'' tid2|) = LN ''n1'' tid1 &
       predOrd t (St(tid1, C_1)) (St(tid2, A_1)) &
       predOrd t (St(tid1, C_3)) (St(tid3, T_3)) &
       predOrd t (St(tid1, C_2)) (St(tid1, C_3)) &
       predOrd t (St(tid2, A_2)) (St(tid1, C_2)) &
       predOrd t (St(tid2, A_1)) (St(tid2, A_2))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid3|), s(|AV ''C'' tid3|) |}
                       ( K ( s(|AV ''T'' tid3|) ) ( s(|AV ''A'' tid3|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: T_ltk_T_A_sec intro: event_predOrdI)
  next
    case (A_2_enc tid4) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT3'', s(|AV ''C'' tid3|) |} ( LN ''AuthKey'' tid4 ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
    next
      case (C_3_enc tid5) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT22'', LN ''AuthKey'' tid4, LN ''n1'' tid5,
                              s(|AV ''T'' tid5|)
                           |}
                           ( K ( s(|AV ''C'' tid3|) ) ( s(|AV ''A'' tid5|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
      next
        case A_2_enc note facts = facts this[simplified]
        have f1: "roleMap r tid5 = Some C" using facts by (auto intro: event_predOrdI)
        have f2: "LN ''n1'' tid5 : knows t" using facts by (auto intro: event_predOrdI)
        note facts = facts C_n1_first_send[OF f1 f2, simplified]
        thus ?thesis by force
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_KerberosV_state) S_auth:
  assumes facts:
    "roleMap r tid3 = Some T"
    "roleMap r tid4 = Some S"
    "s(|NV ''ServerKey'' tid4|) = LN ''ServerKey'' tid3"
    "s(|AV ''A'' tid3|) ~: Compromised"
    "s(|AV ''C'' tid4|) ~: Compromised"
    "s(|AV ''S'' tid4|) ~: Compromised"
    "s(|AV ''T'' tid4|) ~: Compromised"
    "(tid4, S_5) : steps t"
  shows
    "? tid1 tid2.
       roleMap r tid1 = Some C &
       roleMap r tid2 = Some A &
       s(|AV ''A'' tid2|) = s(|AV ''A'' tid1|) &
       s(|AV ''A'' tid3|) = s(|AV ''A'' tid1|) &
       s(|AV ''C'' tid2|) = s(|AV ''C'' tid1|) &
       s(|AV ''C'' tid3|) = s(|AV ''C'' tid1|) &
       s(|AV ''C'' tid4|) = s(|AV ''C'' tid1|) &
       s(|AV ''S'' tid3|) = s(|AV ''S'' tid1|) &
       s(|AV ''S'' tid4|) = s(|AV ''S'' tid1|) &
       s(|AV ''T'' tid2|) = s(|AV ''T'' tid1|) &
       s(|AV ''T'' tid3|) = s(|AV ''T'' tid1|) &
       s(|AV ''T'' tid4|) = s(|AV ''T'' tid1|) &
       s(|NV ''AuthKey'' tid1|) = LN ''AuthKey'' tid2 &
       s(|NV ''AuthKey'' tid3|) = LN ''AuthKey'' tid2 &
       s(|NV ''ServerKey'' tid1|) = LN ''ServerKey'' tid3 &
       s(|NV ''ServerKey'' tid4|) = LN ''ServerKey'' tid3 &
       s(|NV ''n1'' tid2|) = LN ''n1'' tid1 &
       s(|NV ''n2'' tid3|) = LN ''n2'' tid1 &
       s(|NV ''t'' tid4|) = LN ''t'' tid1 &
       predOrd t (St(tid1, C_1)) (St(tid2, A_1)) &
       predOrd t (St(tid1, C_3)) (St(tid3, T_3)) &
       predOrd t (St(tid1, C_5)) (St(tid4, S_5)) &
       predOrd t (St(tid1, C_2)) (St(tid1, C_3)) &
       predOrd t (St(tid1, C_4)) (St(tid1, C_5)) &
       predOrd t (St(tid2, A_2)) (St(tid1, C_2)) &
       predOrd t (St(tid2, A_1)) (St(tid2, A_2)) &
       predOrd t (St(tid3, T_4)) (St(tid1, C_4)) &
       predOrd t (St(tid3, T_3)) (St(tid3, T_4))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT41'', s(|NV ''ServerKey'' tid4|), s(|AV ''C'' tid4|)
                       |}
                       ( K ( s(|AV ''S'' tid4|) ) ( s(|AV ''T'' tid4|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: S_ltk_S_T_sec intro: event_predOrdI)
  next
    case T_4_enc note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid3|), s(|AV ''C'' tid3|) |}
                         ( K ( s(|AV ''T'' tid3|) ) ( s(|AV ''A'' tid3|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: T_ltk_T_A_sec intro: event_predOrdI)
    next
      case (A_2_enc tid6) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT5'', s(|AV ''C'' tid3|), s(|NV ''t'' tid4|) |}
                           ( LN ''ServerKey'' tid3 ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: T_ServerKey_sec intro: event_predOrdI)
      next
        case (C_5_enc tid7) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT3'', s(|AV ''C'' tid3|) |} ( LN ''AuthKey'' tid6 ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
        next
          case (C_3_enc tid8) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''TT22'', s(|NV ''AuthKey'' tid7|), LN ''n1'' tid7,
                                  s(|AV ''T'' tid7|)
                               |}
                               ( K ( s(|AV ''C'' tid3|) ) ( s(|AV ''A'' tid7|) ) ) ")
            case fake note facts = facts this[simplified]
            have f1: "roleMap r tid7 = Some C" using facts by (auto intro: event_predOrdI)
            have f2: "LN ''n1'' tid7 : knows t" using facts by (auto intro: event_predOrdI)
            note facts = facts C_n1_first_send[OF f1 f2, simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT42'', LN ''ServerKey'' tid3, LN ''n2'' tid7,
                                    s(|AV ''S'' tid7|)
                                 |}
                                 ( s(|NV ''AuthKey'' tid7|) ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis by (fastsimp dest: T_ServerKey_sec intro: event_predOrdI)
            next
              case T_4_enc note facts = facts this[simplified]
              thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (A_2_enc tid9) note facts = facts this[simplified]
            have f1: "roleMap r tid7 = Some C" using facts by (auto intro: event_predOrdI)
            have f2: "LN ''n1'' tid7 : knows t" using facts by (auto intro: event_predOrdI)
            note facts = facts C_n1_first_send[OF f1 f2, simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''TT22'', LN ''AuthKey'' tid6, LN ''n1'' tid8,
                                    s(|AV ''T'' tid8|)
                                 |}
                                 ( K ( s(|AV ''C'' tid3|) ) ( s(|AV ''A'' tid8|) ) ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis by (fastsimp dest: A_AuthKey_sec intro: event_predOrdI)
            next
              case A_2_enc note facts = facts this[simplified]
              thus ?thesis proof(sources! " LN ''n1'' tid8 ")
                case C_1_n1 note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT42'', LN ''ServerKey'' tid3, LN ''n2'' tid7,
                                        s(|AV ''S'' tid7|)
                                     |}
                                     ( LN ''AuthKey'' tid9 ) ")
                  case fake note facts = facts this[simplified]
                  thus ?thesis by (fastsimp dest: T_ServerKey_sec intro: event_predOrdI)
                next
                  case T_4_enc note facts = facts this[simplified]
                  thus ?thesis by force
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case (S_6_t tid11) note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''TT42'', LN ''ServerKey'' tid3, LN ''n2'' tid7,
                                        s(|AV ''S'' tid7|)
                                     |}
                                     ( LN ''AuthKey'' tid9 ) ")
                  case fake note facts = facts this[simplified]
                  thus ?thesis by (fastsimp dest: T_ServerKey_sec intro: event_predOrdI)
                next
                  case T_4_enc note facts = facts this[simplified]
                  thus ?thesis by force
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in KerberosV_state) weak_atomicity:
  "complete (t,r,s) atomicAnn"
proof (cases rule: complete_atomicAnnI[completeness_cases_rule])
  case (A_1_n1 t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state KerberosV t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  by (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps)
next
  case (C_2_AuthKey t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state KerberosV t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT22'', ?s'(|NV ''AuthKey'' tid0|), LN ''n1'' tid0,
             ?s'(|AV ''T'' tid0|)
          |}
          ( K ( ?s'(|AV ''C'' tid0|) ) ( ?s'(|AV ''A'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (C_2_TicketGrantingTicket t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state KerberosV t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  by (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps)
next
  case (C_4_ServerKey t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state KerberosV t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT22'', ?s'(|NV ''AuthKey'' tid0|), LN ''n1'' tid0,
             ?s'(|AV ''T'' tid0|)
          |}
          ( K ( ?s'(|AV ''C'' tid0|) ) ( ?s'(|AV ''A'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''n1'' tid0 ")
      case C_1_n1 note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT42'', ?s'(|NV ''ServerKey'' tid0|), LN ''n2'' tid0,
                              ?s'(|AV ''S'' tid0|)
                           |}
                           ( ?s'(|NV ''AuthKey'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
    next
      case (S_6_t tid1) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT42'', ?s'(|NV ''ServerKey'' tid0|), LN ''n2'' tid0,
                              ?s'(|AV ''S'' tid0|)
                           |}
                           ( ?s'(|NV ''AuthKey'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (A_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''n1'' tid0 ")
      case C_1_n1 note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT42'', ?s'(|NV ''ServerKey'' tid0|), LN ''n2'' tid0,
                              ?s'(|AV ''S'' tid0|)
                           |}
                           ( LN ''AuthKey'' tid1 ) ")
      qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
    next
      case (S_6_t tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT42'', ?s'(|NV ''ServerKey'' tid0|), LN ''n2'' tid0,
                              ?s'(|AV ''S'' tid0|)
                           |}
                           ( LN ''AuthKey'' tid1 ) ")
      qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (C_4_ServerTicket t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state KerberosV t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  by (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps)
next
  case (S_5_ServerKey t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state KerberosV t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT41'', ?s'(|NV ''ServerKey'' tid0|),
             ?s'(|AV ''C'' tid0|)
          |}
          ( K ( ?s'(|AV ''S'' tid0|) ) ( ?s'(|AV ''T'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (S_5_t t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state KerberosV t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT41'', ?s'(|NV ''ServerKey'' tid0|),
             ?s'(|AV ''C'' tid0|)
          |}
          ( K ( ?s'(|AV ''S'' tid0|) ) ( ?s'(|AV ''T'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT5'', ?s'(|AV ''C'' tid0|), ?s'(|NV ''t'' tid0|) |}
                         ( ?s'(|NV ''ServerKey'' tid0|) ) ")
    qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
  next
    case (T_4_enc tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT21'', s(|NV ''AuthKey'' tid1|), ?s'(|AV ''C'' tid0|)
                         |}
                         ( K ( ?s'(|AV ''T'' tid0|) ) ( s(|AV ''A'' tid1|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT3'', ?s'(|AV ''C'' tid0|) |}
                           ( s(|NV ''AuthKey'' tid1|) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT5'', ?s'(|AV ''C'' tid0|), ?s'(|NV ''t'' tid0|) |}
                             ( LN ''ServerKey'' tid1 ) ")
        qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
      next
        case (C_3_enc tid2) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''TT5'', ?s'(|AV ''C'' tid0|), ?s'(|NV ''t'' tid0|) |}
                             ( LN ''ServerKey'' tid1 ) ")
        qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (A_2_enc tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT5'', ?s'(|AV ''C'' tid0|), ?s'(|NV ''t'' tid0|) |}
                           ( LN ''ServerKey'' tid1 ) ")
      qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (T_3_AuthKey t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state KerberosV t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT21'', ?s'(|NV ''AuthKey'' tid0|),
             ?s'(|AV ''C'' tid0|)
          |}
          ( K ( ?s'(|AV ''T'' tid0|) ) ( ?s'(|AV ''A'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (T_3_n2 t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state KerberosV t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  by (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps)
qed

end