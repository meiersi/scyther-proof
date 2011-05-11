theory WooLam_cert_auto
imports
  "../ESPLogic"
begin

role A
where "A =
  [ Send ''1'' {| sLAV ''A'', sLN ''na'' |}
  , Recv ''2'' {| sLAV ''B'', sLNV ''nb'' |}
  , Send ''3'' ( Enc {| sLC ''enc3'', sLAV ''A'', sLAV ''B'',
                        sLN ''na'', sLNV ''nb''
                     |}
                     ( sK ''A'' ''S'' )
               )
  , Recv ''6'' {| Enc {| sLC ''enc51'', sLAV ''B'', sLN ''na'',
                         sLNV ''nb'', sLNV ''kab''
                      |}
                      ( sK ''A'' ''S'' ),
                  Enc {| sLC ''enc6'', sLN ''na'', sLNV ''nb'' |} ( sLNV ''kab'' )
               |}
  , Send ''7'' ( Enc {| sLC ''enc7'', sLNV ''nb'' |} ( sLNV ''kab'' )
               )
  ]"

role B
where "B =
  [ Recv ''1'' {| sLAV ''A'', sLNV ''na'' |}
  , Send ''2'' {| sLAV ''B'', sLN ''nb'' |}
  , Recv ''3'' ( sLNV ''Ticket1'' )
  , Send ''4'' {| sLNV ''Ticket1'',
                  Enc {| sLC ''enc4'', sLAV ''A'', sLAV ''B'', sLNV ''na'',
                         sLN ''nb''
                      |}
                      ( sK ''B'' ''S'' )
               |}
  , Recv ''5'' {| sLNV ''Ticket2'',
                  Enc {| sLC ''enc52'', sLAV ''A'', sLNV ''na'', sLN ''nb'',
                         sLNV ''kab''
                      |}
                      ( sK ''B'' ''S'' )
               |}
  , Send ''6'' {| sLNV ''Ticket2'',
                  Enc {| sLC ''enc6'', sLNV ''na'', sLN ''nb'' |} ( sLNV ''kab'' )
               |}
  , Recv ''7'' ( Enc {| sLC ''enc7'', sLN ''nb'' |} ( sLNV ''kab'' )
               )
  ]"

role S
where "S =
  [ Recv ''4'' {| Enc {| sLC ''enc3'', sLAV ''A'', sLAV ''B'',
                         sLNV ''na'', sLNV ''nb''
                      |}
                      ( sK ''A'' ''S'' ),
                  Enc {| sLC ''enc4'', sLAV ''A'', sLAV ''B'', sLNV ''na'',
                         sLNV ''nb''
                      |}
                      ( sK ''A'' ''S'' )
               |}
  , Send ''5'' {| Enc {| sLC ''enc51'', sLAV ''B'', sLNV ''na'',
                         sLNV ''nb'', sLN ''kab''
                      |}
                      ( sK ''A'' ''S'' ),
                  Enc {| sLC ''enc52'', sLAV ''A'', sLNV ''na'', sLNV ''nb'',
                         sLN ''kab''
                      |}
                      ( sK ''B'' ''S'' )
               |}
  ]"

protocol WooLam
where "WooLam = { A, B, S }"

locale atomic_WooLam_state = atomic_state WooLam
locale WooLam_state = reachable_state WooLam

lemma (in atomic_WooLam_state) A_ltk_A_S_sec:
  assumes facts:
    "roleMap r tid0 = Some A"
    "s(|AV ''A'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''A'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''A'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_WooLam_state) S_ltk_A_S_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''A'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''A'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''A'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_WooLam_state) B_ltk_B_S_sec:
  assumes facts:
    "roleMap r tid0 = Some B"
    "s(|AV ''B'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''B'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''B'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_WooLam_state) S_ltk_B_S_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''B'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''B'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''B'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_WooLam_state) S_sec_kab:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''A'' tid0|) ~: Compromised"
    "s(|AV ''B'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "LN ''kab'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''kab'' tid0 ")
  case (S_5_na tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(|AV ''A'' tid1|), s(|AV ''B'' tid1|),
                          LN ''kab'' tid0, s(|NV ''nb'' tid1|)
                       |}
                       ( K ( s(|AV ''A'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (S_5_nb tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(|AV ''A'' tid1|), s(|AV ''B'' tid1|),
                          s(|NV ''na'' tid1|), LN ''kab'' tid0
                       |}
                       ( K ( s(|AV ''A'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
next
  case S_5_kab note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   K ( s(|AV ''A'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (S_5_na_1 tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(|AV ''A'' tid1|), s(|AV ''B'' tid1|),
                          LN ''kab'' tid0, s(|NV ''nb'' tid1|)
                       |}
                       ( K ( s(|AV ''A'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (S_5_nb_1 tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(|AV ''A'' tid1|), s(|AV ''B'' tid1|),
                          s(|NV ''na'' tid1|), LN ''kab'' tid0
                       |}
                       ( K ( s(|AV ''A'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
next
  case S_5_kab_1 note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   K ( s(|AV ''B'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_WooLam_state) A_sec_kab:
  assumes facts:
    "roleMap r tid0 = Some A"
    "s(|AV ''A'' tid0|) ~: Compromised"
    "s(|AV ''B'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, A_6) : steps t"
    "s(|NV ''kab'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc51'', s(|AV ''B'' tid0|), LN ''na'' tid0,
                          s(|NV ''nb'' tid0|), s(|NV ''kab'' tid0|)
                       |}
                       ( K ( s(|AV ''A'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     K ( s(|AV ''A'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_5_enc tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''kab'' tid1 ")
      case (S_5_na tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                              LN ''kab'' tid1, s(|NV ''nb'' tid2|)
                           |}
                           ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_5_nb tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                              s(|NV ''na'' tid2|), LN ''kab'' tid1
                           |}
                           ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case S_5_kab note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''A'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_5_na_1 tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                              LN ''kab'' tid1, s(|NV ''nb'' tid2|)
                           |}
                           ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_5_nb_1 tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                              s(|NV ''na'' tid2|), LN ''kab'' tid1
                           |}
                           ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case S_5_kab_1 note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''B'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_WooLam_state) B_sec_kab:
  assumes facts:
    "roleMap r tid0 = Some B"
    "s(|AV ''A'' tid0|) ~: Compromised"
    "s(|AV ''B'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, B_5) : steps t"
    "s(|NV ''kab'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc52'', s(|AV ''A'' tid0|), s(|NV ''na'' tid0|),
                          LN ''nb'' tid0, s(|NV ''kab'' tid0|)
                       |}
                       ( K ( s(|AV ''B'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     K ( s(|AV ''B'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_5_enc tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''kab'' tid1 ")
      case (S_5_na tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                              LN ''kab'' tid1, s(|NV ''nb'' tid2|)
                           |}
                           ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_5_nb tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                              s(|NV ''na'' tid2|), LN ''kab'' tid1
                           |}
                           ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case S_5_kab note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''A'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_5_na_1 tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                              LN ''kab'' tid1, s(|NV ''nb'' tid2|)
                           |}
                           ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_5_nb_1 tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                              s(|NV ''na'' tid2|), LN ''kab'' tid1
                           |}
                           ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case S_5_kab_1 note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''B'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_WooLam_state) A_sec_inv_kab:
  assumes facts:
    "roleMap r tid0 = Some A"
    "s(|AV ''A'' tid0|) ~: Compromised"
    "s(|AV ''B'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, A_6) : steps t"
    "inv(s(|NV ''kab'' tid0|)) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc51'', s(|AV ''B'' tid0|), LN ''na'' tid0,
                          s(|NV ''nb'' tid0|), s(|NV ''kab'' tid0|)
                       |}
                       ( K ( s(|AV ''A'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     K ( s(|AV ''A'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_5_enc tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''kab'' tid1 ")
      case (S_5_na tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                              LN ''kab'' tid1, s(|NV ''nb'' tid2|)
                           |}
                           ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_5_nb tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                              s(|NV ''na'' tid2|), LN ''kab'' tid1
                           |}
                           ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case S_5_kab note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''A'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_5_na_1 tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                              LN ''kab'' tid1, s(|NV ''nb'' tid2|)
                           |}
                           ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_5_nb_1 tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                              s(|NV ''na'' tid2|), LN ''kab'' tid1
                           |}
                           ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case S_5_kab_1 note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''B'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_WooLam_state) B_sec_inv_kab:
  assumes facts:
    "roleMap r tid0 = Some B"
    "s(|AV ''A'' tid0|) ~: Compromised"
    "s(|AV ''B'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, B_5) : steps t"
    "inv(s(|NV ''kab'' tid0|)) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc52'', s(|AV ''A'' tid0|), s(|NV ''na'' tid0|),
                          LN ''nb'' tid0, s(|NV ''kab'' tid0|)
                       |}
                       ( K ( s(|AV ''B'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     K ( s(|AV ''B'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_5_enc tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''kab'' tid1 ")
      case (S_5_na tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                              LN ''kab'' tid1, s(|NV ''nb'' tid2|)
                           |}
                           ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_5_nb tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                              s(|NV ''na'' tid2|), LN ''kab'' tid1
                           |}
                           ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case S_5_kab note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''A'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_5_na_1 tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                              LN ''kab'' tid1, s(|NV ''nb'' tid2|)
                           |}
                           ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (S_5_nb_1 tid2) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                              s(|NV ''na'' tid2|), LN ''kab'' tid1
                           |}
                           ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case S_5_kab_1 note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''B'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_WooLam_state) na_first_send:
  assumes facts:
    "roleMap r tid1 = Some A"
    "LN ''na'' tid1 : knows t"
  shows "predOrd t (St(tid1, A_1)) (Ln(LN ''na'' tid1))"
using facts proof(sources! " LN ''na'' tid1 ")
  case A_1_na note facts = facts this[simplified]
  thus ?thesis by force
next
  case A_3_na note facts = facts this[simplified]
  thus ?thesis by force
next
  case (S_5_na tid2) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                          LN ''na'' tid1, s(|NV ''nb'' tid2|)
                       |}
                       ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
    case A_3_enc note facts = facts this[simplified]
    thus ?thesis by force
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (S_5_nb tid2) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                          s(|NV ''na'' tid2|), LN ''na'' tid1
                       |}
                       ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (S_5_na_1 tid2) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                          LN ''na'' tid1, s(|NV ''nb'' tid2|)
                       |}
                       ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
    case A_3_enc note facts = facts this[simplified]
    thus ?thesis by force
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (S_5_nb_1 tid2) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                          s(|NV ''na'' tid2|), LN ''na'' tid1
                       |}
                       ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_WooLam_state) nb_first_send:
  assumes facts:
    "roleMap r tid1 = Some B"
    "LN ''nb'' tid1 : knows t"
  shows "predOrd t (St(tid1, B_2)) (Ln(LN ''nb'' tid1))"
using facts proof(sources! " LN ''nb'' tid1 ")
  case B_2_nb note facts = facts this[simplified]
  thus ?thesis by force
next
  case B_4_nb note facts = facts this[simplified]
  thus ?thesis by force
next
  case B_6_nb note facts = facts this[simplified]
  thus ?thesis by force
next
  case (S_5_na tid2) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                          LN ''nb'' tid1, s(|NV ''nb'' tid2|)
                       |}
                       ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (S_5_nb tid2) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                          s(|NV ''na'' tid2|), LN ''nb'' tid1
                       |}
                       ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (S_5_na_1 tid2) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                          LN ''nb'' tid1, s(|NV ''nb'' tid2|)
                       |}
                       ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
next
  case (S_5_nb_1 tid2) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                          s(|NV ''na'' tid2|), LN ''nb'' tid1
                       |}
                       ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_WooLam_state) A_ni_synch:
  assumes facts:
    "roleMap r tid1 = Some A"
    "s(|AV ''A'' tid1|) ~: Compromised"
    "s(|AV ''B'' tid1|) ~: Compromised"
    "s(|AV ''S'' tid1|) ~: Compromised"
    "(tid1, A_6) : steps t"
  shows
    "? tid2 tid3.
       roleMap r tid2 = Some B &
       roleMap r tid3 = Some S &
       s(|AV ''A'' tid2|) = s(|AV ''A'' tid1|) &
       s(|AV ''A'' tid3|) = s(|AV ''A'' tid1|) &
       s(|AV ''B'' tid2|) = s(|AV ''B'' tid1|) &
       s(|AV ''B'' tid3|) = s(|AV ''B'' tid1|) &
       s(|AV ''S'' tid2|) = s(|AV ''S'' tid1|) &
       s(|AV ''S'' tid3|) = s(|AV ''S'' tid1|) &
       s(|NV ''kab'' tid1|) = LN ''kab'' tid3 &
       s(|NV ''kab'' tid2|) = LN ''kab'' tid3 &
       s(|NV ''na'' tid2|) = LN ''na'' tid1 &
       s(|NV ''na'' tid3|) = LN ''na'' tid1 &
       s(|NV ''nb'' tid1|) = LN ''nb'' tid2 &
       s(|NV ''nb'' tid3|) = LN ''nb'' tid2 &
       predOrd t (St(tid1, A_1)) (St(tid2, B_1)) &
       predOrd t (St(tid1, A_3)) (St(tid3, S_4)) &
       predOrd t (St(tid1, A_2)) (St(tid1, A_3)) &
       predOrd t (St(tid2, B_2)) (St(tid1, A_2)) &
       predOrd t (St(tid2, B_4)) (St(tid3, S_4)) &
       predOrd t (St(tid2, B_6)) (St(tid1, A_6)) &
       predOrd t (St(tid2, B_1)) (St(tid2, B_2)) &
       predOrd t (St(tid2, B_3)) (St(tid2, B_4)) &
       predOrd t (St(tid2, B_5)) (St(tid2, B_6)) &
       predOrd t (St(tid3, S_5)) (St(tid2, B_5)) &
       predOrd t (St(tid3, S_4)) (St(tid3, S_5))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc51'', s(|AV ''B'' tid1|), LN ''na'' tid1,
                          s(|NV ''nb'' tid1|), s(|NV ''kab'' tid1|)
                       |}
                       ( K ( s(|AV ''A'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     K ( s(|AV ''A'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_5_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''enc3'', s(|AV ''A'' tid1|), s(|AV ''B'' tid1|),
                            LN ''na'' tid1, s(|NV ''nb'' tid1|)
                         |}
                         ( K ( s(|AV ''A'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''A'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case A_3_enc note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc4'', s(|AV ''A'' tid1|), s(|AV ''B'' tid1|),
                              LN ''na'' tid1, s(|NV ''nb'' tid1|)
                           |}
                           ( K ( s(|AV ''A'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''A'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (B_4_enc tid4) note facts = facts this[simplified]
        thus ?thesis proof(sources! " LN ''na'' tid1 ")
          case A_1_na note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''enc6'', LN ''na'' tid1, LN ''nb'' tid4 |}
                               ( LN ''kab'' tid2 ) ")
            case fake note facts = facts this[simplified]
            thus ?thesis proof(sources! " LN ''kab'' tid2 ")
              case (S_5_na tid6) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''enc3'', s(|AV ''A'' tid6|), s(|AV ''B'' tid6|),
                                      LN ''kab'' tid2, s(|NV ''nb'' tid6|)
                                   |}
                                   ( K ( s(|AV ''A'' tid6|) ) ( s(|AV ''S'' tid6|) ) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (S_5_nb tid6) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''enc3'', s(|AV ''A'' tid6|), s(|AV ''B'' tid6|),
                                      s(|NV ''na'' tid6|), LN ''kab'' tid2
                                   |}
                                   ( K ( s(|AV ''A'' tid6|) ) ( s(|AV ''S'' tid6|) ) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case S_5_kab note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''A'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (S_5_na_1 tid6) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''enc3'', s(|AV ''A'' tid6|), s(|AV ''B'' tid6|),
                                      LN ''kab'' tid2, s(|NV ''nb'' tid6|)
                                   |}
                                   ( K ( s(|AV ''A'' tid6|) ) ( s(|AV ''S'' tid6|) ) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case (S_5_nb_1 tid6) note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''enc3'', s(|AV ''A'' tid6|), s(|AV ''B'' tid6|),
                                      s(|NV ''na'' tid6|), LN ''kab'' tid2
                                   |}
                                   ( K ( s(|AV ''A'' tid6|) ) ( s(|AV ''S'' tid6|) ) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case S_5_kab_1 note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''A'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case B_6_enc note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''enc52'', s(|AV ''A'' tid1|), LN ''na'' tid1,
                                    LN ''nb'' tid4, LN ''kab'' tid2
                                 |}
                                 ( K ( s(|AV ''A'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''A'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case S_5_enc note facts = facts this[simplified]
              thus ?thesis proof(sources! " LN ''nb'' tid4 ")
                case B_2_nb note facts = facts this[simplified]
                thus ?thesis by force
              next
                case B_4_nb note facts = facts this[simplified]
                thus ?thesis by force
              next
                case (S_5_na tid8) note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''enc3'', s(|AV ''A'' tid8|), s(|AV ''B'' tid8|),
                                        LN ''nb'' tid4, s(|NV ''nb'' tid8|)
                                     |}
                                     ( K ( s(|AV ''A'' tid8|) ) ( s(|AV ''S'' tid8|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case (S_5_nb tid8) note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''enc3'', s(|AV ''A'' tid8|), s(|AV ''B'' tid8|),
                                        s(|NV ''na'' tid8|), LN ''nb'' tid4
                                     |}
                                     ( K ( s(|AV ''A'' tid8|) ) ( s(|AV ''S'' tid8|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case (S_5_na_1 tid8) note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''enc3'', s(|AV ''A'' tid8|), s(|AV ''B'' tid8|),
                                        LN ''nb'' tid4, s(|NV ''nb'' tid8|)
                                     |}
                                     ( K ( s(|AV ''A'' tid8|) ) ( s(|AV ''S'' tid8|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case (S_5_nb_1 tid8) note facts = facts this[simplified]
                thus ?thesis proof(sources! "
                                 Enc {| LC ''enc3'', s(|AV ''A'' tid8|), s(|AV ''B'' tid8|),
                                        s(|NV ''na'' tid8|), LN ''nb'' tid4
                                     |}
                                     ( K ( s(|AV ''A'' tid8|) ) ( s(|AV ''S'' tid8|) ) ) ")
                qed (insert facts, ((clarsimp, order?))+)?
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case A_3_na note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           K ( s(|AV ''A'' tid1|) ) ( s(|AV ''S'' tid1|) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (S_5_na tid5) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''enc3'', s(|AV ''A'' tid5|), s(|AV ''B'' tid5|),
                                  LN ''na'' tid1, s(|NV ''nb'' tid5|)
                               |}
                               ( K ( s(|AV ''A'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (S_5_nb tid5) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''enc3'', s(|AV ''A'' tid5|), s(|AV ''B'' tid5|),
                                  s(|NV ''na'' tid5|), LN ''na'' tid1
                               |}
                               ( K ( s(|AV ''A'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (S_5_na_1 tid5) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''enc3'', s(|AV ''A'' tid5|), s(|AV ''B'' tid5|),
                                  LN ''na'' tid1, s(|NV ''nb'' tid5|)
                               |}
                               ( K ( s(|AV ''A'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (S_5_nb_1 tid5) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''enc3'', s(|AV ''A'' tid5|), s(|AV ''B'' tid5|),
                                  s(|NV ''na'' tid5|), LN ''na'' tid1
                               |}
                               ( K ( s(|AV ''A'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_WooLam_state) B_ni_synch:
  assumes facts:
    "roleMap r tid2 = Some B"
    "s(|AV ''A'' tid2|) ~: Compromised"
    "s(|AV ''B'' tid2|) ~: Compromised"
    "s(|AV ''S'' tid2|) ~: Compromised"
    "(tid2, B_7) : steps t"
  shows
    "? tid1 tid3.
       roleMap r tid1 = Some A &
       roleMap r tid3 = Some S &
       s(|AV ''A'' tid2|) = s(|AV ''A'' tid1|) &
       s(|AV ''A'' tid3|) = s(|AV ''A'' tid1|) &
       s(|AV ''B'' tid2|) = s(|AV ''B'' tid1|) &
       s(|AV ''B'' tid3|) = s(|AV ''B'' tid1|) &
       s(|AV ''S'' tid2|) = s(|AV ''S'' tid1|) &
       s(|AV ''S'' tid3|) = s(|AV ''S'' tid1|) &
       s(|NV ''kab'' tid1|) = LN ''kab'' tid3 &
       s(|NV ''kab'' tid2|) = LN ''kab'' tid3 &
       s(|NV ''na'' tid2|) = LN ''na'' tid1 &
       s(|NV ''na'' tid3|) = LN ''na'' tid1 &
       s(|NV ''nb'' tid1|) = LN ''nb'' tid2 &
       s(|NV ''nb'' tid3|) = LN ''nb'' tid2 &
       predOrd t (St(tid1, A_1)) (St(tid2, B_1)) &
       predOrd t (St(tid1, A_3)) (St(tid3, S_4)) &
       predOrd t (St(tid1, A_7)) (St(tid2, B_7)) &
       predOrd t (St(tid1, A_2)) (St(tid1, A_3)) &
       predOrd t (St(tid1, A_6)) (St(tid1, A_7)) &
       predOrd t (St(tid2, B_2)) (St(tid1, A_2)) &
       predOrd t (St(tid2, B_4)) (St(tid3, S_4)) &
       predOrd t (St(tid2, B_6)) (St(tid1, A_6)) &
       predOrd t (St(tid2, B_1)) (St(tid2, B_2)) &
       predOrd t (St(tid2, B_3)) (St(tid2, B_4)) &
       predOrd t (St(tid2, B_5)) (St(tid2, B_6)) &
       predOrd t (St(tid3, S_5)) (St(tid2, B_5)) &
       predOrd t (St(tid3, S_4)) (St(tid3, S_5))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc52'', s(|AV ''A'' tid2|), s(|NV ''na'' tid2|),
                          LN ''nb'' tid2, s(|NV ''kab'' tid2|)
                       |}
                       ( K ( s(|AV ''B'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     K ( s(|AV ''B'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_5_enc tid3) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''enc3'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                            s(|NV ''na'' tid2|), LN ''nb'' tid2
                         |}
                         ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (A_3_enc tid4) note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''nb'' tid2 ")
        case B_2_nb note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''enc7'', LN ''nb'' tid2 |} ( LN ''kab'' tid3 ) ")
          case fake note facts = facts this[simplified]
          thus ?thesis proof(sources! " LN ''kab'' tid3 ")
            case (S_5_na tid6) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''enc3'', s(|AV ''A'' tid6|), s(|AV ''B'' tid6|),
                                    LN ''kab'' tid3, s(|NV ''nb'' tid6|)
                                 |}
                                 ( K ( s(|AV ''A'' tid6|) ) ( s(|AV ''S'' tid6|) ) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (S_5_nb tid6) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''enc3'', s(|AV ''A'' tid6|), s(|AV ''B'' tid6|),
                                    s(|NV ''na'' tid6|), LN ''kab'' tid3
                                 |}
                                 ( K ( s(|AV ''A'' tid6|) ) ( s(|AV ''S'' tid6|) ) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case S_5_kab note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (S_5_na_1 tid6) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''enc3'', s(|AV ''A'' tid6|), s(|AV ''B'' tid6|),
                                    LN ''kab'' tid3, s(|NV ''nb'' tid6|)
                                 |}
                                 ( K ( s(|AV ''A'' tid6|) ) ( s(|AV ''S'' tid6|) ) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (S_5_nb_1 tid6) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''enc3'', s(|AV ''A'' tid6|), s(|AV ''B'' tid6|),
                                    s(|NV ''na'' tid6|), LN ''kab'' tid3
                                 |}
                                 ( K ( s(|AV ''A'' tid6|) ) ( s(|AV ''S'' tid6|) ) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case S_5_kab_1 note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             K ( s(|AV ''B'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (A_7_enc tid6) note facts = facts this[simplified]
          thus ?thesis proof(sources! " LN ''na'' tid4 ")
            case A_1_na note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''enc4'', s(|AV ''A'' tid2|), s(|AV ''B'' tid2|),
                                    LN ''na'' tid4, LN ''nb'' tid2
                                 |}
                                 ( K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
              case fake note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
              qed (insert facts, ((clarsimp, order?))+)?
            next
              case B_4_enc note facts = facts this[simplified]
              thus ?thesis proof(sources! "
                               Enc {| LC ''enc6'', LN ''na'' tid6, LN ''nb'' tid2 |}
                                   ( LN ''kab'' tid3 ) ")
                case fake note facts = facts this[simplified]
                thus ?thesis proof(sources! " LN ''kab'' tid3 ")
                  case (S_5_na tid9) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''enc3'', s(|AV ''A'' tid9|), s(|AV ''B'' tid9|),
                                          LN ''kab'' tid3, s(|NV ''nb'' tid9|)
                                       |}
                                       ( K ( s(|AV ''A'' tid9|) ) ( s(|AV ''S'' tid9|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case (S_5_nb tid9) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''enc3'', s(|AV ''A'' tid9|), s(|AV ''B'' tid9|),
                                          s(|NV ''na'' tid9|), LN ''kab'' tid3
                                       |}
                                       ( K ( s(|AV ''A'' tid9|) ) ( s(|AV ''S'' tid9|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case S_5_kab note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case (S_5_na_1 tid9) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''enc3'', s(|AV ''A'' tid9|), s(|AV ''B'' tid9|),
                                          LN ''kab'' tid3, s(|NV ''nb'' tid9|)
                                       |}
                                       ( K ( s(|AV ''A'' tid9|) ) ( s(|AV ''S'' tid9|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case (S_5_nb_1 tid9) note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   Enc {| LC ''enc3'', s(|AV ''A'' tid9|), s(|AV ''B'' tid9|),
                                          s(|NV ''na'' tid9|), LN ''kab'' tid3
                                       |}
                                       ( K ( s(|AV ''A'' tid9|) ) ( s(|AV ''S'' tid9|) ) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                next
                  case S_5_kab_1 note facts = facts this[simplified]
                  thus ?thesis proof(sources! "
                                   K ( s(|AV ''A'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
                  qed (insert facts, ((clarsimp, order?))+)?
                qed (insert facts, ((clarsimp, order?))+)?
              next
                case B_6_enc note facts = facts this[simplified]
                thus ?thesis by force
              qed (insert facts, ((clarsimp, order?))+)?
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (S_5_na tid7) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''enc3'', s(|AV ''A'' tid7|), s(|AV ''B'' tid7|),
                                    LN ''na'' tid4, s(|NV ''nb'' tid7|)
                                 |}
                                 ( K ( s(|AV ''A'' tid7|) ) ( s(|AV ''S'' tid7|) ) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (S_5_nb tid7) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''enc3'', s(|AV ''A'' tid7|), s(|AV ''B'' tid7|),
                                    s(|NV ''na'' tid7|), LN ''na'' tid4
                                 |}
                                 ( K ( s(|AV ''A'' tid7|) ) ( s(|AV ''S'' tid7|) ) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (S_5_na_1 tid7) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''enc3'', s(|AV ''A'' tid7|), s(|AV ''B'' tid7|),
                                    LN ''na'' tid4, s(|NV ''nb'' tid7|)
                                 |}
                                 ( K ( s(|AV ''A'' tid7|) ) ( s(|AV ''S'' tid7|) ) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          next
            case (S_5_nb_1 tid7) note facts = facts this[simplified]
            thus ?thesis proof(sources! "
                             Enc {| LC ''enc3'', s(|AV ''A'' tid7|), s(|AV ''B'' tid7|),
                                    s(|NV ''na'' tid7|), LN ''na'' tid4
                                 |}
                                 ( K ( s(|AV ''A'' tid7|) ) ( s(|AV ''S'' tid7|) ) ) ")
            qed (insert facts, ((clarsimp, order?))+)?
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case B_4_nb note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''B'' tid2|) ) ( s(|AV ''S'' tid2|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (S_5_na tid5) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''enc3'', s(|AV ''A'' tid5|), s(|AV ''B'' tid5|),
                                LN ''nb'' tid2, s(|NV ''nb'' tid5|)
                             |}
                             ( K ( s(|AV ''A'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (S_5_nb tid5) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''enc3'', s(|AV ''A'' tid5|), s(|AV ''B'' tid5|),
                                s(|NV ''na'' tid5|), LN ''nb'' tid2
                             |}
                             ( K ( s(|AV ''A'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (S_5_na_1 tid5) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''enc3'', s(|AV ''A'' tid5|), s(|AV ''B'' tid5|),
                                LN ''nb'' tid2, s(|NV ''nb'' tid5|)
                             |}
                             ( K ( s(|AV ''A'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (S_5_nb_1 tid5) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''enc3'', s(|AV ''A'' tid5|), s(|AV ''B'' tid5|),
                                s(|NV ''na'' tid5|), LN ''nb'' tid2
                             |}
                             ( K ( s(|AV ''A'' tid5|) ) ( s(|AV ''S'' tid5|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_WooLam_state) S_ni_synch:
  assumes facts:
    "roleMap r tid3 = Some S"
    "s(|AV ''A'' tid3|) ~: Compromised"
    "s(|AV ''B'' tid3|) ~: Compromised"
    "s(|AV ''S'' tid3|) ~: Compromised"
    "(tid3, S_4) : steps t"
  shows
    "? tid1 tid2.
       roleMap r tid1 = Some A &
       roleMap r tid2 = Some B &
       s(|AV ''A'' tid2|) = s(|AV ''A'' tid1|) &
       s(|AV ''A'' tid3|) = s(|AV ''A'' tid1|) &
       s(|AV ''B'' tid2|) = s(|AV ''B'' tid1|) &
       s(|AV ''B'' tid3|) = s(|AV ''B'' tid1|) &
       s(|AV ''S'' tid2|) = s(|AV ''S'' tid1|) &
       s(|AV ''S'' tid3|) = s(|AV ''S'' tid1|) &
       s(|NV ''na'' tid2|) = LN ''na'' tid1 &
       s(|NV ''na'' tid3|) = LN ''na'' tid1 &
       s(|NV ''nb'' tid1|) = LN ''nb'' tid2 &
       s(|NV ''nb'' tid3|) = LN ''nb'' tid2 &
       predOrd t (St(tid1, A_1)) (St(tid2, B_1)) &
       predOrd t (St(tid1, A_3)) (St(tid3, S_4)) &
       predOrd t (St(tid1, A_2)) (St(tid1, A_3)) &
       predOrd t (St(tid2, B_2)) (St(tid1, A_2)) &
       predOrd t (St(tid2, B_4)) (St(tid3, S_4)) &
       predOrd t (St(tid2, B_1)) (St(tid2, B_2)) &
       predOrd t (St(tid2, B_3)) (St(tid2, B_4))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(|AV ''A'' tid3|), s(|AV ''B'' tid3|),
                          s(|NV ''na'' tid3|), s(|NV ''nb'' tid3|)
                       |}
                       ( K ( s(|AV ''A'' tid3|) ) ( s(|AV ''S'' tid3|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     K ( s(|AV ''A'' tid3|) ) ( s(|AV ''S'' tid3|) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (A_3_enc tid4) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''enc4'', s(|AV ''A'' tid3|), s(|AV ''B'' tid3|),
                            LN ''na'' tid4, s(|NV ''nb'' tid3|)
                         |}
                         ( K ( s(|AV ''A'' tid3|) ) ( s(|AV ''S'' tid3|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       K ( s(|AV ''A'' tid3|) ) ( s(|AV ''S'' tid3|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case (B_4_enc tid5) note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''na'' tid4 ")
        case A_1_na note facts = facts this[simplified]
        thus ?thesis proof(sources! " LN ''nb'' tid5 ")
          case B_2_nb note facts = facts this[simplified]
          thus ?thesis by force
        next
          case B_4_nb note facts = facts this[simplified]
          thus ?thesis by force
        next
          case B_6_nb note facts = facts this[simplified]
          thus ?thesis by force
        next
          case (S_5_na tid7) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''enc3'', s(|AV ''A'' tid7|), s(|AV ''B'' tid7|),
                                  LN ''nb'' tid5, s(|NV ''nb'' tid7|)
                               |}
                               ( K ( s(|AV ''A'' tid7|) ) ( s(|AV ''S'' tid7|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (S_5_nb tid7) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''enc3'', s(|AV ''A'' tid7|), s(|AV ''B'' tid7|),
                                  s(|NV ''na'' tid7|), LN ''nb'' tid5
                               |}
                               ( K ( s(|AV ''A'' tid7|) ) ( s(|AV ''S'' tid7|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (S_5_na_1 tid7) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''enc3'', s(|AV ''A'' tid7|), s(|AV ''B'' tid7|),
                                  LN ''nb'' tid5, s(|NV ''nb'' tid7|)
                               |}
                               ( K ( s(|AV ''A'' tid7|) ) ( s(|AV ''S'' tid7|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        next
          case (S_5_nb_1 tid7) note facts = facts this[simplified]
          thus ?thesis proof(sources! "
                           Enc {| LC ''enc3'', s(|AV ''A'' tid7|), s(|AV ''B'' tid7|),
                                  s(|NV ''na'' tid7|), LN ''nb'' tid5
                               |}
                               ( K ( s(|AV ''A'' tid7|) ) ( s(|AV ''S'' tid7|) ) ) ")
          qed (insert facts, ((clarsimp, order?))+)?
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case A_3_na note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         K ( s(|AV ''A'' tid3|) ) ( s(|AV ''S'' tid3|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (S_5_na tid6) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''enc3'', s(|AV ''A'' tid6|), s(|AV ''B'' tid6|),
                                LN ''na'' tid4, s(|NV ''nb'' tid6|)
                             |}
                             ( K ( s(|AV ''A'' tid6|) ) ( s(|AV ''S'' tid6|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (S_5_nb tid6) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''enc3'', s(|AV ''A'' tid6|), s(|AV ''B'' tid6|),
                                s(|NV ''na'' tid6|), LN ''na'' tid4
                             |}
                             ( K ( s(|AV ''A'' tid6|) ) ( s(|AV ''S'' tid6|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (S_5_na_1 tid6) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''enc3'', s(|AV ''A'' tid6|), s(|AV ''B'' tid6|),
                                LN ''na'' tid4, s(|NV ''nb'' tid6|)
                             |}
                             ( K ( s(|AV ''A'' tid6|) ) ( s(|AV ''S'' tid6|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      next
        case (S_5_nb_1 tid6) note facts = facts this[simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''enc3'', s(|AV ''A'' tid6|), s(|AV ''B'' tid6|),
                                s(|NV ''na'' tid6|), LN ''na'' tid4
                             |}
                             ( K ( s(|AV ''A'' tid6|) ) ( s(|AV ''S'' tid6|) ) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in WooLam_state) weak_atomicity:
  "complete (t,r,s) atomicAnn"
proof (cases rule: complete_atomicAnnI[completeness_cases_rule])
  case (A_2_nb t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state WooLam t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  by (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps)
next
  case (A_6_kab t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state WooLam t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''enc51'', ?s'(|AV ''B'' tid0|), LN ''na'' tid0,
             ?s'(|NV ''nb'' tid0|), ?s'(|NV ''kab'' tid0|)
          |}
          ( K ( ?s'(|AV ''A'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (B_1_na t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state WooLam t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  by (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps)
next
  case (B_5_Ticket2 t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state WooLam t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  by (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps)
next
  case (B_5_kab t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state WooLam t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''enc52'', ?s'(|AV ''A'' tid0|), ?s'(|NV ''na'' tid0|),
             LN ''nb'' tid0, ?s'(|NV ''kab'' tid0|)
          |}
          ( K ( ?s'(|AV ''B'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (S_4_na t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state WooLam t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''enc3'', ?s'(|AV ''A'' tid0|), ?s'(|AV ''B'' tid0|),
             ?s'(|NV ''na'' tid0|), ?s'(|NV ''nb'' tid0|)
          |}
          ( K ( ?s'(|AV ''A'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (S_4_nb t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state WooLam t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''enc3'', ?s'(|AV ''A'' tid0|), ?s'(|AV ''B'' tid0|),
             ?s'(|NV ''na'' tid0|), ?s'(|NV ''nb'' tid0|)
          |}
          ( K ( ?s'(|AV ''A'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
qed

end