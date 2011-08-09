theory "Kerberos_V4_cert_auto"
imports
  "../ESPLogic"
begin

(* section:  The Kerberos Protocol, Version 4  *)

(* text: 
  Modeled after the description given by Bella [1] based on the original
  technical report [2].

  Notable differences:

    1. We do not model the timestamps and the timing properties because our
       model does not support reasoning about them yet. We model them as
       freshly generated nonces that are leaked immediately after generation.

    2. We do not model session key leakage, as our support for key compromise
       properties is not ready yet.

    3. We provide more general authentication and secrecy properties, as we do
       not assume a priory the uncompromisedness of the ticket granting server.
       Furthermore, the authentication propertis are more fine-grained due to
       our more precise execution model.

    4. We use explicit global constants instead of implicit typing to identify
       the different encryptions.

    5. We use the abbreviations: C for Client, A for authenticator, G for
       ticket granting server, S for server.


[1] Bella, Giampaolo and Paulson, Lawrence C., "Kerberos Version 4: Inductive
    Analysis of the Secrecy Goals", in ESORICS, 1998, pp. 361-375.

[2] Miller, S. P. and Neuman, B. C. and Schiller, J. I. and Saltzer, J. H.,
    "Kerberos Authentication and Authorization System", in Project Athena Technical
    Plan, 1987, pp. 1-36.
 *)

role A
where "A =
  [ Recv ''1'' <| sMV ''C'', sMV ''G'', sMV ''Tc1'' |>
  , Send ''2_leak'' ( sN ''Ta'' )
  , Send ''2'' <| sAV ''A'',
                  PEnc <| sC ''21'', sN ''AuthKey'', sMV ''G'', sN ''Ta'',
                          PEnc <| sC ''22'', sMV ''C'', sMV ''G'', sN ''AuthKey'', sN ''Ta'' |>
                               ( PSymK ( sAV ''A'' ) ( sMV ''G'' ) )
                       |>
                       ( PSymK ( sMV ''C'' ) ( sAV ''A'' ) )
               |>
  ]"

role C
where "C =
  [ Send ''1_leak'' ( sN ''Tc1'' )
  , Send ''1'' <| sAV ''C'', sAV ''G'', sN ''Tc1'' |>
  , Recv ''2'' <| sMV ''A'',
                  PEnc <| sC ''21'', sMV ''AuthKey'', sAV ''G'', sMV ''Ta'',
                          sMV ''AuthTicket''
                       |>
                       ( PSymK ( sAV ''C'' ) ( sMV ''A'' ) )
               |>
  , Send ''3_leak'' ( sN ''Tc2'' )
  , Send ''3'' <| sMV ''A'', sMV ''AuthTicket'',
                  PEnc <| sC ''3'', sAV ''C'', sN ''Tc2'' |> ( sMV ''AuthKey'' ), sAV ''S''
               |>
  , Recv ''4'' ( PEnc <| sC ''41'', sMV ''ServKey'', sAV ''S'', sMV ''Tg'',
                         sMV ''ServTicket''
                      |>
                      ( sMV ''AuthKey'' )
               )
  , Send ''5_leak'' ( sN ''Tc3'' )
  , Send ''5'' <| sAV ''G'', sMV ''ServTicket'',
                  PEnc <| sC ''5'', sAV ''C'', sN ''Tc3'' |> ( sMV ''ServKey'' )
               |>
  , Recv ''6'' ( PEnc <| sC ''6'', sN ''Tc3'' |> ( sMV ''ServKey'' ) )
  ]"

role G
where "G =
  [ Recv ''3'' <| sMV ''A'',
                  PEnc <| sC ''22'', sMV ''C'', sAV ''G'', sMV ''AuthKey'', sMV ''Ta'' |>
                       ( PSymK ( sMV ''A'' ) ( sAV ''G'' ) ),
                  PEnc <| sC ''3'', sMV ''C'', sMV ''Tc2'' |> ( sMV ''AuthKey'' ),
                  sMV ''S''
               |>
  , Send ''4_leak'' ( sN ''Tg'' )
  , Send ''4'' ( PEnc <| sC ''41'', sN ''ServKey'', sMV ''S'', sN ''Tg'',
                         PEnc <| sC ''42'', sMV ''C'', sMV ''S'', sN ''ServKey'', sN ''Tg'' |>
                              ( PSymK ( sAV ''G'' ) ( sMV ''S'' ) )
                      |>
                      ( sMV ''AuthKey'' )
               )
  ]"

role S
where "S =
  [ Recv ''5'' <| sMV ''G'',
                  PEnc <| sC ''42'', sMV ''C'', sAV ''S'', sMV ''ServKey'', sMV ''Tg'' |>
                       ( PSymK ( sMV ''G'' ) ( sAV ''S'' ) ),
                  PEnc <| sC ''5'', sMV ''C'', sMV ''Tc3'' |> ( sMV ''ServKey'' )
               |>
  , Send ''6'' ( PEnc <| sC ''6'', sMV ''Tc3'' |> ( sMV ''ServKey'' ) )
  ]"

protocol Kerberos
where "Kerberos = { A, C, G, S }"

locale restricted_Kerberos_state = Kerberos_state

type_invariant Kerberos_typing for Kerberos
where "Kerberos_typing = mk_typing
  [ ((C, ''A''), (KnownT C_2))
  , ((G, ''A''), (KnownT G_3))
  , ((C, ''AuthKey''), (SumT (KnownT C_2) (NonceT A ''AuthKey'')))
  , ((G, ''AuthKey''), (SumT (KnownT G_3) (NonceT A ''AuthKey'')))
  , ((C, ''AuthTicket''),
     (SumT (KnownT C_2) (EncT (TupT (ConstT ''22'') (TupT (KnownT C_2) (TupT AgentT (TupT (NonceT A ''AuthKey'') (NonceT A ''Ta''))))) (KT AgentT AgentT))))
  , ((A, ''C''), (KnownT A_1))
  , ((G, ''C''), (SumT (KnownT G_3) AgentT))
  , ((S, ''C''), (SumT (KnownT S_5) AgentT))
  , ((A, ''G''), (KnownT A_1))
  , ((S, ''G''), (KnownT S_5))
  , ((G, ''S''), (KnownT G_3))
  , ((C, ''ServKey''), (SumT (KnownT C_4) (NonceT G ''ServKey'')))
  , ((S, ''ServKey''), (SumT (KnownT S_5) (NonceT G ''ServKey'')))
  , ((C, ''ServTicket''),
     (SumT (KnownT C_4) (EncT (TupT (ConstT ''42'') (TupT (KnownT C_4) (TupT AgentT (TupT (NonceT G ''ServKey'') (NonceT G ''Tg''))))) (KT AgentT AgentT))))
  , ((C, ''Ta''), (SumT (KnownT C_2) (NonceT A ''Ta'')))
  , ((G, ''Ta''), (SumT (KnownT G_3) (NonceT A ''Ta'')))
  , ((A, ''Tc1''), (KnownT A_1))
  , ((G, ''Tc2''), (SumT (KnownT G_3) (NonceT C ''Tc2'')))
  , ((S, ''Tc3''), (SumT (KnownT S_5) (NonceT C ''Tc3'')))
  , ((C, ''Tg''), (SumT (KnownT C_4) (NonceT G ''Tg'')))
  , ((S, ''Tg''), (SumT (KnownT S_5) (NonceT G ''Tg'')))
  ]"

sublocale Kerberos_state < Kerberos_typing_state
proof -
  have "(t,r,s) : approx Kerberos_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF Kerberos_typing.monoTyp, completeness_cases_rule])
    case (A_1_C t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (A_1_G t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (A_1_Tc1 t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (C_2_A t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (C_2_AuthKey t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''21'', s(MV ''AuthKey'' tid0), s(AV ''G'' tid0),
               s(MV ''Ta'' tid0), s(MV ''AuthTicket'' tid0)
            |}
            ( K ( s(AV ''C'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (C_2_AuthTicket t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''21'', s(MV ''AuthKey'' tid0), s(AV ''G'' tid0),
               s(MV ''Ta'' tid0), s(MV ''AuthTicket'' tid0)
            |}
            ( K ( s(AV ''C'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (C_2_Ta t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''21'', s(MV ''AuthKey'' tid0), s(AV ''G'' tid0),
               s(MV ''Ta'' tid0), s(MV ''AuthTicket'' tid0)
            |}
            ( K ( s(AV ''C'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (C_4_ServKey t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''41'', s(MV ''ServKey'' tid0), s(AV ''S'' tid0),
               s(MV ''Tg'' tid0), s(MV ''ServTicket'' tid0)
            |}
            ( s(MV ''AuthKey'' tid0) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (C_4_ServTicket t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''41'', s(MV ''ServKey'' tid0), s(AV ''S'' tid0),
               s(MV ''Tg'' tid0), s(MV ''ServTicket'' tid0)
            |}
            ( s(MV ''AuthKey'' tid0) ) ")
      case (G_4_enc tid1) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''3'', s(MV ''C'' tid1), s(MV ''Tc2'' tid1) |}
                           ( s(MV ''AuthKey'' tid0) ) ")
      qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (C_4_Tg t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''41'', s(MV ''ServKey'' tid0), s(AV ''S'' tid0),
               s(MV ''Tg'' tid0), s(MV ''ServTicket'' tid0)
            |}
            ( s(MV ''AuthKey'' tid0) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (G_3_A t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (G_3_AuthKey t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''22'', s(MV ''C'' tid0), s(AV ''G'' tid0),
               s(MV ''AuthKey'' tid0), s(MV ''Ta'' tid0)
            |}
            ( K ( s(MV ''A'' tid0) ) ( s(AV ''G'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (G_3_C t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''3'', s(MV ''C'' tid0), s(MV ''Tc2'' tid0) |}
            ( s(MV ''AuthKey'' tid0) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (G_3_S t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (G_3_Ta t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''22'', s(MV ''C'' tid0), s(AV ''G'' tid0),
               s(MV ''AuthKey'' tid0), s(MV ''Ta'' tid0)
            |}
            ( K ( s(MV ''A'' tid0) ) ( s(AV ''G'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (G_3_Tc2 t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''3'', s(MV ''C'' tid0), s(MV ''Tc2'' tid0) |}
            ( s(MV ''AuthKey'' tid0) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (S_5_C t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''5'', s(MV ''C'' tid0), s(MV ''Tc3'' tid0) |}
            ( s(MV ''ServKey'' tid0) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (S_5_G t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (S_5_ServKey t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''42'', s(MV ''C'' tid0), s(AV ''S'' tid0),
               s(MV ''ServKey'' tid0), s(MV ''Tg'' tid0)
            |}
            ( K ( s(MV ''G'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (S_5_Tc3 t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''5'', s(MV ''C'' tid0), s(MV ''Tc3'' tid0) |}
            ( s(MV ''ServKey'' tid0) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (S_5_Tg t r s tid0) note facts = this
    then interpret state: Kerberos_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''42'', s(MV ''C'' tid0), s(AV ''S'' tid0),
               s(MV ''ServKey'' tid0), s(MV ''Tg'' tid0)
            |}
            ( K ( s(MV ''G'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  qed
  thus "Kerberos_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context Kerberos_state begin

  (* This rule is unsafe in general, but OK here, 
     as we are only reasoning about static compromise. 
  *)
  lemma static_longterm_key_reveal[dest!]:
    "predOrd t (LKR a) e ==> RLKR a : reveals t"
    by (auto intro: compr_predOrdI)

  lemma longterm_private_key_secrecy:
    assumes facts:
      "SK m : knows t"
      "RLKR m ~: reveals t"
    shows "False"
  using facts by (sources "SK m")

  lemma longterm_sym_ud_key_secrecy:
    assumes facts:
      "K m1 m2 : knows t"
      "RLKR m1 ~: reveals t"
      "RLKR m2 ~: reveals t"
    shows "False"
  using facts by (sources "K m1 m2")

  lemma longterm_sym_bd_key_secrecy:
    assumes facts:
      "Kbd m1 m2 : knows t"
      "RLKR m1 ~: reveals t"
      "RLKR m2 ~: reveals t"
      "m1 : Agent"
      "m2 : Agent"
    shows "False"
  proof -
    from facts 
    have "KShr (agents {m1, m2}) : knows t"
      by (auto simp: Kbd_def)
    thus ?thesis using facts
    proof (sources "KShr (agents {m1, m2})")
    qed (auto simp: agents_def Agent_def)
  qed

  lemmas ltk_secrecy =
    longterm_sym_ud_key_secrecy
    longterm_sym_ud_key_secrecy[OF in_knows_predOrd1]
    longterm_sym_bd_key_secrecy
    longterm_sym_bd_key_secrecy[OF in_knows_predOrd1]
    longterm_private_key_secrecy
    longterm_private_key_secrecy[OF in_knows_predOrd1]

end

(* subsection:  Secrecy Properties  *)

lemma (in restricted_Kerberos_state) A_AuthKey_secret:
  assumes facts:
    "roleMap r tid0 = Some A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''C'' tid0)) ~: reveals t"
    "RLKR(s(MV ''G'' tid0)) ~: reveals t"
    "LN ''AuthKey'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''AuthKey'' tid0 ")
  case A_2_AuthKey note_unified facts = this facts
  thus ?thesis by (fastsimp dest!: ltk_secrecy)
next
  case A_2_AuthKey_1 note_unified facts = this facts
  thus ?thesis by (fastsimp dest!: ltk_secrecy)
next
  case (C_3_AuthTicket_AuthKey tid1 a0 a1 tid3 a2 a3) note_unified facts = this facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''21'', s(MV ''AuthKey'' tid1), s(AV ''G'' tid1),
                          s(MV ''Ta'' tid1),
                          Enc {| LC ''22'', a0, a1, LN ''AuthKey'' tid0, LN ''Ta'' tid3 |}
                              ( K ( a2 ) ( a3 ) )
                       |}
                       ( K ( s(AV ''C'' tid1) ) ( s(MV ''A'' tid1) ) ) ")
    case (A_2_enc tid4) note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  qed (insert facts, (((clarsimp, order?) | order))+)?
qed (insert facts, fastsimp+)?

lemma (in restricted_Kerberos_state) C_AuthKey_secret:
  assumes facts:
    "roleMap r tid0 = Some C"
    "RLKR(s(AV ''C'' tid0)) ~: reveals t"
    "RLKR(s(AV ''G'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, C_2 ) : steps t"
    "s(MV ''AuthKey'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''21'', s(MV ''AuthKey'' tid0), s(AV ''G'' tid0),
                          s(MV ''Ta'' tid0), s(MV ''AuthTicket'' tid0)
                       |}
                       ( K ( s(AV ''C'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (A_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp dest: A_AuthKey_secret intro: event_predOrdI)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_Kerberos_state) G_AuthKey_secret:
  assumes facts:
    "roleMap r tid0 = Some G"
    "RLKR(s(AV ''G'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''C'' tid0)) ~: reveals t"
    "( tid0, G_3 ) : steps t"
    "s(MV ''AuthKey'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''22'', s(MV ''C'' tid0), s(AV ''G'' tid0),
                          s(MV ''AuthKey'' tid0), s(MV ''Ta'' tid0)
                       |}
                       ( K ( s(MV ''A'' tid0) ) ( s(AV ''G'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (A_2_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (C_3_AuthTicket_enc tid1 a0 a1 tid2 tid3 a2 a3) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''21'', s(MV ''AuthKey'' tid1), s(AV ''G'' tid1),
                            s(MV ''Ta'' tid1),
                            Enc {| LC ''22'', a0, s(AV ''G'' tid0), LN ''AuthKey'' tid2,
                                   LN ''Ta'' tid3
                                |}
                                ( K ( a2 ) ( s(AV ''G'' tid0) ) )
                         |}
                         ( K ( s(AV ''C'' tid1) ) ( s(MV ''A'' tid1) ) ) ")
      case (A_2_enc tid4) note_unified facts = this facts
      thus ?thesis by (fastsimp dest: A_AuthKey_secret intro: event_predOrdI)
    qed (insert facts, (((clarsimp, order?) | order))+)?
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_Kerberos_state) G_ServKey_sec:
  assumes facts:
    "roleMap r tid0 = Some G"
    "RLKR(s(AV ''G'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''C'' tid0)) ~: reveals t"
    "RLKR(s(MV ''S'' tid0)) ~: reveals t"
    "LN ''ServKey'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''ServKey'' tid0 ")
  case (C_5_ServTicket_ServKey tid1 a0 a1 tid3 a2 a3) note_unified facts = this facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''41'', s(MV ''ServKey'' tid1), s(AV ''S'' tid1),
                          s(MV ''Tg'' tid1),
                          Enc {| LC ''42'', a0, a1, LN ''ServKey'' tid0, LN ''Tg'' tid3 |}
                              ( K ( a2 ) ( a3 ) )
                       |}
                       ( s(MV ''AuthKey'' tid1) ) ")
    case (G_4_enc tid4) note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  qed (insert facts, (((clarsimp, order?) | order))+)?
next
  case G_4_ServKey note_unified facts = this facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''22'', s(MV ''C'' tid0), s(AV ''G'' tid0),
                          s(MV ''AuthKey'' tid0), s(MV ''Ta'' tid0)
                       |}
                       ( K ( s(MV ''A'' tid0) ) ( s(AV ''G'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (A_2_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (C_3_AuthTicket_enc tid1 a0 a1 tid2 tid3 a2 a3) note_unified facts = this facts
    thus ?thesis by (fastsimp dest: G_AuthKey_secret intro: event_predOrdI)
  qed (insert facts, fastsimp+)?
next
  case G_4_ServKey_1 note_unified facts = this facts
  thus ?thesis by (fastsimp dest!: ltk_secrecy)
qed (insert facts, fastsimp+)?

lemma (in restricted_Kerberos_state) C_ServKey_sec:
  assumes facts:
    "roleMap r tid0 = Some C"
    "RLKR(s(AV ''C'' tid0)) ~: reveals t"
    "RLKR(s(AV ''G'' tid0)) ~: reveals t"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, C_4 ) : steps t"
    "s(MV ''ServKey'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''21'', s(MV ''AuthKey'' tid0), s(AV ''G'' tid0),
                          s(MV ''Ta'' tid0), s(MV ''AuthTicket'' tid0)
                       |}
                       ( K ( s(AV ''C'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (A_2_enc tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''41'', s(MV ''ServKey'' tid0), s(AV ''S'' tid0),
                            s(MV ''Tg'' tid0), s(MV ''ServTicket'' tid0)
                         |}
                         ( LN ''AuthKey'' tid1 ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest: A_AuthKey_secret intro: event_predOrdI)
    next
      case (G_4_enc tid2) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''22'', s(MV ''C'' tid2), s(AV ''G'' tid2),
                              LN ''AuthKey'' tid1, s(MV ''Ta'' tid2)
                           |}
                           ( K ( s(MV ''A'' tid2) ) ( s(AV ''G'' tid2) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastsimp dest: A_AuthKey_secret intro: event_predOrdI)
      next
        case (A_2_enc_1 tid3) note_unified facts = this facts
        thus ?thesis by (fastsimp dest!: ltk_secrecy)
      next
        case (C_3_AuthTicket_enc tid3 a0 a1 tid4 tid5 a2 a3) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''21'', s(MV ''AuthKey'' tid3), s(AV ''G'' tid3),
                                s(MV ''Ta'' tid3),
                                Enc {| LC ''22'', a0, s(AV ''G'' tid2), LN ''AuthKey'' tid1,
                                       LN ''Ta'' tid5
                                    |}
                                    ( K ( a2 ) ( s(AV ''G'' tid2) ) )
                             |}
                             ( K ( s(AV ''C'' tid3) ) ( s(MV ''A'' tid3) ) ) ")
          case (A_2_enc tid6) note_unified facts = this facts
          thus ?thesis by (fastsimp dest: G_ServKey_sec intro: event_predOrdI)
        qed (insert facts, (((clarsimp, order?) | order))+)?
      qed (insert facts, fastsimp+)?
    qed (insert facts, fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

(* subsection:  Authentication Properties  *)

lemma (in restricted_Kerberos_state) C_auth:
  assumes facts:
    "roleMap r tid1 = Some C"
    "RLKR(s(AV ''C'' tid1)) ~: reveals t"
    "RLKR(s(AV ''G'' tid1)) ~: reveals t"
    "RLKR(s(AV ''S'' tid1)) ~: reveals t"
    "RLKR(s(MV ''A'' tid1)) ~: reveals t"
    "( tid1, C_6 ) : steps t"
  shows
    "(?  tid2.
        (?  tid3.
           (?  tid4.
              roleMap r tid2 = Some A &
              roleMap r tid3 = Some G &
              roleMap r tid4 = Some S &
              s(MV ''A'' tid1) = s(AV ''A'' tid2) &
              s(AV ''C'' tid1) = s(MV ''C'' tid2) &
              s(AV ''G'' tid1) = s(MV ''G'' tid2) &
              s(MV ''Ta'' tid1) = LN ''Ta'' tid2 &
              s(MV ''AuthKey'' tid1) = LN ''AuthKey'' tid2 &
              s(MV ''A'' tid1) = s(MV ''A'' tid3) &
              s(AV ''C'' tid1) = s(MV ''C'' tid3) &
              s(AV ''G'' tid1) = s(AV ''G'' tid3) &
              s(AV ''S'' tid1) = s(MV ''S'' tid3) &
              s(MV ''Tg'' tid1) = LN ''Tg'' tid3 &
              s(MV ''AuthKey'' tid1) = s(MV ''AuthKey'' tid3) &
              s(MV ''ServKey'' tid1) = LN ''ServKey'' tid3 &
              s(AV ''C'' tid1) = s(MV ''C'' tid4) &
              s(AV ''G'' tid1) = s(MV ''G'' tid4) &
              s(AV ''S'' tid1) = s(AV ''S'' tid4) &
              LN ''Tc3'' tid1 = s(MV ''Tc3'' tid4) &
              s(MV ''ServKey'' tid1) = s(MV ''ServKey'' tid4))))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''21'', s(MV ''AuthKey'' tid1), s(AV ''G'' tid1),
                          s(MV ''Ta'' tid1), s(MV ''AuthTicket'' tid1)
                       |}
                       ( K ( s(AV ''C'' tid1) ) ( s(MV ''A'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (A_2_enc tid2) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''6'', LN ''Tc3'' tid1 |} ( s(MV ''ServKey'' tid1) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest: C_ServKey_sec intro: event_predOrdI)
    next
      case (S_6_enc tid3) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''41'', s(MV ''ServKey'' tid1), s(AV ''S'' tid1),
                              s(MV ''Tg'' tid1), s(MV ''ServTicket'' tid1)
                           |}
                           ( LN ''AuthKey'' tid2 ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastsimp dest: A_AuthKey_secret intro: event_predOrdI)
      next
        case (G_4_enc tid4) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''22'', s(MV ''C'' tid4), s(AV ''G'' tid4),
                                LN ''AuthKey'' tid2, s(MV ''Ta'' tid4)
                             |}
                             ( K ( s(MV ''A'' tid4) ) ( s(AV ''G'' tid4) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastsimp dest: A_AuthKey_secret intro: event_predOrdI)
        next
          case (A_2_enc_1 tid5) note_unified facts = this facts
          thus ?thesis by (fastsimp dest!: ltk_secrecy)
        next
          case (C_3_AuthTicket_enc tid5 a0 a1 tid6 tid7 a2 a3) note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''42'', s(MV ''C'' tid3), s(AV ''S'' tid3),
                                  LN ''ServKey'' tid4, s(MV ''Tg'' tid3)
                               |}
                               ( K ( s(MV ''G'' tid3) ) ( s(AV ''S'' tid3) ) ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastsimp dest: C_ServKey_sec intro: event_predOrdI)
          next
            case (C_5_ServTicket_enc tid8 a3 a4 tid9 tid10 a5 a6) note_unified facts = this facts
            thus ?thesis proof(sources! "
                             Enc {| LC ''21'', s(MV ''AuthKey'' tid5), s(AV ''G'' tid5),
                                    s(MV ''Ta'' tid5),
                                    Enc {| LC ''22'', a0, s(AV ''G'' tid4), LN ''AuthKey'' tid2,
                                           LN ''Ta'' tid7
                                        |}
                                        ( K ( a2 ) ( s(AV ''G'' tid4) ) )
                                 |}
                                 ( K ( s(AV ''C'' tid5) ) ( s(MV ''A'' tid5) ) ) ")
              case (A_2_enc tid11) note_unified facts = this facts
              thus ?thesis proof(sources! "
                               Enc {| LC ''41'', s(MV ''ServKey'' tid8), s(AV ''S'' tid8),
                                      s(MV ''Tg'' tid8),
                                      Enc {| LC ''42'', a3, s(AV ''S'' tid3), LN ''ServKey'' tid4,
                                             LN ''Tg'' tid10
                                          |}
                                          ( K ( a5 ) ( s(AV ''S'' tid3) ) )
                                   |}
                                   ( s(MV ''AuthKey'' tid8) ) ")
                case (G_4_enc tid11) note_unified facts = this facts
                thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
              qed (insert facts, (((clarsimp, order?) | order))+)?
            qed (insert facts, (((clarsimp, order?) | order))+)?
          next
            case (G_4_enc_1 tid8) note_unified facts = this facts
            thus ?thesis by (fastsimp dest: A_AuthKey_secret intro: event_predOrdI)
          qed (insert facts, fastsimp+)?
        qed (insert facts, fastsimp+)?
      qed (insert facts, fastsimp+)?
    qed (insert facts, fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_Kerberos_state) G_auth:
  assumes facts:
    "roleMap r tid3 = Some G"
    "RLKR(s(AV ''G'' tid3)) ~: reveals t"
    "RLKR(s(MV ''A'' tid3)) ~: reveals t"
    "RLKR(s(MV ''C'' tid3)) ~: reveals t"
    "( tid3, G_3 ) : steps t"
  shows
    "(?  tid1.
        (?  tid2.
           roleMap r tid1 = Some C &
           roleMap r tid2 = Some A &
           s(MV ''A'' tid1) = s(MV ''A'' tid3) &
           s(AV ''C'' tid1) = s(MV ''C'' tid3) &
           s(AV ''G'' tid1) = s(AV ''G'' tid3) &
           LN ''Tc2'' tid1 = s(MV ''Tc2'' tid3) &
           s(MV ''AuthKey'' tid1) = s(MV ''AuthKey'' tid3) &
           s(MV ''A'' tid1) = s(AV ''A'' tid2) &
           s(AV ''C'' tid1) = s(MV ''C'' tid2) &
           s(AV ''G'' tid1) = s(MV ''G'' tid2) &
           s(MV ''AuthKey'' tid1) = LN ''AuthKey'' tid2))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''22'', s(MV ''C'' tid3), s(AV ''G'' tid3),
                          s(MV ''AuthKey'' tid3), s(MV ''Ta'' tid3)
                       |}
                       ( K ( s(MV ''A'' tid3) ) ( s(AV ''G'' tid3) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (A_2_enc_1 tid4) note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (C_3_AuthTicket_enc tid4 a0 a1 tid5 tid6 a2 a3) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''3'', a0, s(MV ''Tc2'' tid3) |} ( LN ''AuthKey'' tid5 ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest: G_AuthKey_secret intro: event_predOrdI)
    next
      case (C_3_enc tid7) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''21'', s(MV ''AuthKey'' tid4), s(AV ''G'' tid4),
                              s(MV ''Ta'' tid4),
                              Enc {| LC ''22'', s(AV ''C'' tid7), s(AV ''G'' tid3),
                                     LN ''AuthKey'' tid5, LN ''Ta'' tid6
                                  |}
                                  ( K ( a2 ) ( s(AV ''G'' tid3) ) )
                           |}
                           ( K ( s(AV ''C'' tid4) ) ( s(MV ''A'' tid4) ) ) ")
        case (A_2_enc tid8) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''21'', LN ''AuthKey'' tid5, s(AV ''G'' tid7),
                                s(MV ''Ta'' tid7), s(MV ''AuthTicket'' tid7)
                             |}
                             ( K ( s(AV ''C'' tid4) ) ( s(MV ''A'' tid7) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastsimp dest: A_AuthKey_secret intro: event_predOrdI)
        next
          case (A_2_enc tid8) note_unified facts = this facts
          thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
        qed (insert facts, fastsimp+)?
      qed (insert facts, (((clarsimp, order?) | order))+)?
    qed (insert facts, fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

end