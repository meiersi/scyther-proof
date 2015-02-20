theory "Kerberos_V5_cert_auto"
imports
  "ESPLogic"
begin

(* section:  The Kerberos Protocol, Version 5  *)

(* text: 
Modeled after SPORE.

Notable differences.

  1. We use explicit global constants instead of implicit typing to identify
     the different encryptions.

  2. We do not model the timestamps and the timing properties because our
     model does not support reasoning about them yet. We use nonces that are
     leaked immediately after generation for timestamps and prove the
     agreement properties over them.

  3. The authentication properties in SPORE are not formulated precisely
     enough. Some directions of agreement are only satisfied under additional
     assumptions. See the notes below (in the original source). We prove now
     the strongest authentication that can be proven without additional
     assumptions. Some more work is required to check whether these are
     sufficient for the real-world applications where Kerberos is used.
  
  4. We identify client and user. Therefore, the user key Ku in the
     description in SPORE is modeled as k(A,C).

Note that we do not model the loss of authentication, server, and session
keys. The Isabelle models could handle that thanks to the work done by Martin
Schaub in his master thesis [1], but scyther-proof does not (yet).

[1] Schaub, Martin. Efficient Interactive Construction of Machine-Checked
    Protocol Security Proofs in the Context of Dynamically Compromising
    Adversaries.  Eidgenoessische Technische Hochschule Zuerich, Departement
    Informatik (2011).  doi:10.3929/ethz-a-006450686.
 *)

role A
where "A =
  [ Recv ''1'' <| sMV ''C'', sMV ''G'', sMV ''L1'', sMV ''N1'' |>
  , Send ''2_leak'' <| sN ''T1start'', sN ''T1expire'' |>
  , Send ''2'' <| sAV ''A'', sMV ''C'',
                  PEnc <| sC ''2_1'', sMV ''C'', sMV ''G'', sN ''AuthKey'', sN ''T1start'',
                          sN ''T1expire''
                       |>
                       ( PSymK ( sMV ''G'' ) ( sAV ''A'' ) ),
                  PEnc <| sC ''2_2'', sMV ''G'', sN ''AuthKey'', sN ''T1start'',
                          sN ''T1expire''
                       |>
                       ( PSymK ( sMV ''C'' ) ( sAV ''A'' ) )
               |>
  ]"

role C
where "C =
  [ Send ''1'' <| sAV ''C'', sAV ''G'', sN ''L1'', sN ''N1'' |>
  , Recv ''2'' <| sMV ''A'', sAV ''C'', sMV ''TicketGrantingTicket'',
                  PEnc <| sC ''2_2'', sAV ''G'', sMV ''AuthKey'', sMV ''T1start'',
                          sMV ''T1expire''
                       |>
                       ( PSymK ( sAV ''C'' ) ( sMV ''A'' ) )
               |>
  , Send ''3_leak'' ( sN ''T1'' )
  , Send ''3'' <| sMV ''A'', sAV ''S'', sN ''L2'', sN ''N2'',
                  sMV ''TicketGrantingTicket'',
                  PEnc <| sC ''3'', sAV ''C'', sN ''T1'' |> ( sMV ''AuthKey'' )
               |>
  , Recv ''4'' <| sAV ''C'', sMV ''ServerTicket'',
                  PEnc <| sC ''4_2'', sAV ''S'', sMV ''ServerKey'', sMV ''T2start'',
                          sMV ''T2expire'', sN ''N2''
                       |>
                       ( sMV ''AuthKey'' )
               |>
  , Send ''5_leak'' ( sN ''T2'' )
  , Send ''5'' <| sAV ''G'', sMV ''ServerTicket'',
                  PEnc <| sC ''5'', sAV ''C'', sN ''T2'' |> ( sMV ''ServerKey'' )
               |>
  , Recv ''6'' ( PEnc <| sC ''6'', sN ''T2'' |> ( sMV ''ServerKey'' ) )
  ]"

role G
where "G =
  [ Recv ''3'' <| sMV ''A'', sMV ''S'', sMV ''L2'', sMV ''N2'',
                  PEnc <| sC ''2_1'', sMV ''C'', sAV ''G'', sMV ''AuthKey'',
                          sMV ''T1start'', sMV ''T1expire''
                       |>
                       ( PSymK ( sAV ''G'' ) ( sMV ''A'' ) ),
                  PEnc <| sC ''3'', sMV ''C'', sMV ''T1'' |> ( sMV ''AuthKey'' )
               |>
  , Send ''4_leak'' <| sN ''T2start'', sN ''T2expire'' |>
  , Send ''4'' <| sMV ''C'',
                  PEnc <| sC ''4_1'', sMV ''C'', sMV ''S'', sN ''ServerKey'',
                          sN ''T2start'', sN ''T2expire''
                       |>
                       ( PSymK ( sAV ''G'' ) ( sMV ''S'' ) ),
                  PEnc <| sC ''4_2'', sMV ''S'', sN ''ServerKey'', sN ''T2start'',
                          sN ''T2expire'', sMV ''N2''
                       |>
                       ( sMV ''AuthKey'' )
               |>
  ]"

role S
where "S =
  [ Recv ''5'' <| sMV ''G'',
                  PEnc <| sC ''4_1'', sMV ''C'', sAV ''S'', sMV ''ServerKey'',
                          sMV ''T2start'', sMV ''T2expire''
                       |>
                       ( PSymK ( sMV ''G'' ) ( sAV ''S'' ) ),
                  PEnc <| sC ''5'', sMV ''C'', sMV ''T2'' |> ( sMV ''ServerKey'' )
               |>
  , Send ''6'' ( PEnc <| sC ''6'', sMV ''T2'' |> ( sMV ''ServerKey'' ) )
  ]"

protocol Kerberos
where "Kerberos = { A, C, G, S }"

locale restricted_Kerberos_state = Kerberos_state

type_invariant Kerberos_msc_typing for Kerberos
where "Kerberos_msc_typing = mk_typing
  [ ((C, ''A''), (KnownT C_2))
  , ((G, ''A''), (KnownT G_3))
  , ((C, ''AuthKey''), (SumT (KnownT C_2) (NonceT A ''AuthKey'')))
  , ((G, ''AuthKey''), (SumT (KnownT G_3) (NonceT A ''AuthKey'')))
  , ((A, ''C''), (KnownT A_1))
  , ((G, ''C''), (SumT (KnownT G_3) AgentT))
  , ((S, ''C''), (SumT (KnownT S_5) AgentT))
  , ((A, ''G''), (KnownT A_1))
  , ((S, ''G''), (KnownT S_5))
  , ((A, ''L1''), (KnownT A_1))
  , ((G, ''L2''), (KnownT G_3))
  , ((A, ''N1''), (KnownT A_1))
  , ((G, ''N2''), (KnownT G_3))
  , ((G, ''S''), (KnownT G_3))
  , ((C, ''ServerKey''), (SumT (KnownT C_4) (NonceT G ''ServerKey'')))
  , ((S, ''ServerKey''), (SumT (KnownT S_5) (NonceT G ''ServerKey'')))
  , ((C, ''ServerTicket''), (KnownT C_4))
  , ((G, ''T1''), (SumT (KnownT G_3) (NonceT C ''T1'')))
  , ((C, ''T1expire''), (SumT (KnownT C_2) (NonceT A ''T1expire'')))
  , ((G, ''T1expire''), (SumT (KnownT G_3) (NonceT A ''T1expire'')))
  , ((C, ''T1start''), (SumT (KnownT C_2) (NonceT A ''T1start'')))
  , ((G, ''T1start''), (SumT (KnownT G_3) (NonceT A ''T1start'')))
  , ((S, ''T2''), (SumT (KnownT S_5) (NonceT C ''T2'')))
  , ((C, ''T2expire''), (SumT (KnownT C_4) (NonceT G ''T2expire'')))
  , ((S, ''T2expire''), (SumT (KnownT S_5) (NonceT G ''T2expire'')))
  , ((C, ''T2start''), (SumT (KnownT C_4) (NonceT G ''T2start'')))
  , ((S, ''T2start''), (SumT (KnownT S_5) (NonceT G ''T2start'')))
  , ((C, ''TicketGrantingTicket''), (KnownT C_2))
  ]"

sublocale Kerberos_state < Kerberos_msc_typing_state
proof -
  have "(t,r,s) : approx Kerberos_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF Kerberos_msc_typing.monoTyp, completeness_cases_rule])
    case (A_1_C t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_1_C
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (A_1_G t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_1_G
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (A_1_L1 t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_1_L1
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (A_1_N1 t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_1_N1
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (C_2_A t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = C_2_A
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (C_2_AuthKey t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = C_2_AuthKey
    thus ?case
    proof(sources! "
        Enc {| LC ''2_2'', s(AV ''G'' tid0), s(MV ''AuthKey'' tid0),
               s(MV ''T1start'' tid0), s(MV ''T1expire'' tid0)
            |}
            ( K ( s(AV ''C'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (C_2_T1expire t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = C_2_T1expire
    thus ?case
    proof(sources! "
        Enc {| LC ''2_2'', s(AV ''G'' tid0), s(MV ''AuthKey'' tid0),
               s(MV ''T1start'' tid0), s(MV ''T1expire'' tid0)
            |}
            ( K ( s(AV ''C'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (C_2_T1start t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = C_2_T1start
    thus ?case
    proof(sources! "
        Enc {| LC ''2_2'', s(AV ''G'' tid0), s(MV ''AuthKey'' tid0),
               s(MV ''T1start'' tid0), s(MV ''T1expire'' tid0)
            |}
            ( K ( s(AV ''C'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (C_2_TicketGrantingTicket t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = C_2_TicketGrantingTicket
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (C_4_ServerKey t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = C_4_ServerKey
    thus ?case
    proof(sources! "
        Enc {| LC ''4_2'', s(AV ''S'' tid0), s(MV ''ServerKey'' tid0),
               s(MV ''T2start'' tid0), s(MV ''T2expire'' tid0), LN ''N2'' tid0
            |}
            ( s(MV ''AuthKey'' tid0) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (C_4_ServerTicket t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = C_4_ServerTicket
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (C_4_T2expire t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = C_4_T2expire
    thus ?case
    proof(sources! "
        Enc {| LC ''4_2'', s(AV ''S'' tid0), s(MV ''ServerKey'' tid0),
               s(MV ''T2start'' tid0), s(MV ''T2expire'' tid0), LN ''N2'' tid0
            |}
            ( s(MV ''AuthKey'' tid0) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (C_4_T2start t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = C_4_T2start
    thus ?case
    proof(sources! "
        Enc {| LC ''4_2'', s(AV ''S'' tid0), s(MV ''ServerKey'' tid0),
               s(MV ''T2start'' tid0), s(MV ''T2expire'' tid0), LN ''N2'' tid0
            |}
            ( s(MV ''AuthKey'' tid0) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (G_3_A t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = G_3_A
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (G_3_AuthKey t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = G_3_AuthKey
    thus ?case
    proof(sources! "
        Enc {| LC ''2_1'', s(MV ''C'' tid0), s(AV ''G'' tid0),
               s(MV ''AuthKey'' tid0), s(MV ''T1start'' tid0), s(MV ''T1expire'' tid0)
            |}
            ( K ( s(AV ''G'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (G_3_C t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = G_3_C
    thus ?case
    proof(sources! "
        Enc {| LC ''2_1'', s(MV ''C'' tid0), s(AV ''G'' tid0),
               s(MV ''AuthKey'' tid0), s(MV ''T1start'' tid0), s(MV ''T1expire'' tid0)
            |}
            ( K ( s(AV ''G'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (G_3_L2 t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = G_3_L2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (G_3_N2 t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = G_3_N2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (G_3_S t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = G_3_S
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (G_3_T1 t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = G_3_T1
    thus ?case
    proof(sources! "
        Enc {| LC ''3'', s(MV ''C'' tid0), s(MV ''T1'' tid0) |}
            ( s(MV ''AuthKey'' tid0) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (G_3_T1expire t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = G_3_T1expire
    thus ?case
    proof(sources! "
        Enc {| LC ''2_1'', s(MV ''C'' tid0), s(AV ''G'' tid0),
               s(MV ''AuthKey'' tid0), s(MV ''T1start'' tid0), s(MV ''T1expire'' tid0)
            |}
            ( K ( s(AV ''G'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (G_3_T1start t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = G_3_T1start
    thus ?case
    proof(sources! "
        Enc {| LC ''2_1'', s(MV ''C'' tid0), s(AV ''G'' tid0),
               s(MV ''AuthKey'' tid0), s(MV ''T1start'' tid0), s(MV ''T1expire'' tid0)
            |}
            ( K ( s(AV ''G'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (S_5_C t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_5_C
    thus ?case
    proof(sources! "
        Enc {| LC ''5'', s(MV ''C'' tid0), s(MV ''T2'' tid0) |}
            ( s(MV ''ServerKey'' tid0) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (S_5_G t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_5_G
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (S_5_ServerKey t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_5_ServerKey
    thus ?case
    proof(sources! "
        Enc {| LC ''4_1'', s(MV ''C'' tid0), s(AV ''S'' tid0),
               s(MV ''ServerKey'' tid0), s(MV ''T2start'' tid0), s(MV ''T2expire'' tid0)
            |}
            ( K ( s(MV ''G'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (S_5_T2 t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_5_T2
    thus ?case
    proof(sources! "
        Enc {| LC ''5'', s(MV ''C'' tid0), s(MV ''T2'' tid0) |}
            ( s(MV ''ServerKey'' tid0) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (S_5_T2expire t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_5_T2expire
    thus ?case
    proof(sources! "
        Enc {| LC ''4_1'', s(MV ''C'' tid0), s(AV ''S'' tid0),
               s(MV ''ServerKey'' tid0), s(MV ''T2start'' tid0), s(MV ''T2expire'' tid0)
            |}
            ( K ( s(MV ''G'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (S_5_T2start t r s tid0)
    then interpret state: Kerberos_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_5_T2start
    thus ?case
    proof(sources! "
        Enc {| LC ''4_1'', s(MV ''C'' tid0), s(AV ''S'' tid0),
               s(MV ''ServerKey'' tid0), s(MV ''T2start'' tid0), s(MV ''T2expire'' tid0)
            |}
            ( K ( s(MV ''G'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  qed
  thus "Kerberos_msc_typing_state t r s" by unfold_locales auto
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
  thus ?thesis by (auto dest!: ltk_secrecy)
next
  case A_2_AuthKey_1 note_unified facts = this facts
  thus ?thesis by (auto dest!: ltk_secrecy)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

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
                   Enc {| LC ''2_2'', s(AV ''G'' tid0), s(MV ''AuthKey'' tid0),
                          s(MV ''T1start'' tid0), s(MV ''T1expire'' tid0)
                       |}
                       ( K ( s(AV ''C'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (A_2_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: A_AuthKey_secret intro: event_predOrdI)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_Kerberos_state) T_AuthKey_secret:
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
                   Enc {| LC ''2_1'', s(MV ''C'' tid0), s(AV ''G'' tid0),
                          s(MV ''AuthKey'' tid0), s(MV ''T1start'' tid0), s(MV ''T1expire'' tid0)
                       |}
                       ( K ( s(AV ''G'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (A_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: A_AuthKey_secret intro: event_predOrdI)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_Kerberos_state) G_ServerKey_secret:
  assumes facts:
    "roleMap r tid0 = Some G"
    "RLKR(s(AV ''G'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''C'' tid0)) ~: reveals t"
    "RLKR(s(MV ''S'' tid0)) ~: reveals t"
    "LN ''ServerKey'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''ServerKey'' tid0 ")
  case G_4_ServerKey note_unified facts = this facts
  thus ?thesis by (auto dest!: ltk_secrecy)
next
  case G_4_ServerKey_1 note_unified facts = this facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''2_1'', s(MV ''C'' tid0), s(AV ''G'' tid0),
                          s(MV ''AuthKey'' tid0), s(MV ''T1start'' tid0), s(MV ''T1expire'' tid0)
                       |}
                       ( K ( s(AV ''G'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (A_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: A_AuthKey_secret intro: event_predOrdI)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

lemma (in restricted_Kerberos_state) C_ServerKey_secret:
  assumes facts:
    "roleMap r tid0 = Some C"
    "RLKR(s(AV ''C'' tid0)) ~: reveals t"
    "RLKR(s(AV ''G'' tid0)) ~: reveals t"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, C_4 ) : steps t"
    "s(MV ''ServerKey'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''2_2'', s(AV ''G'' tid0), s(MV ''AuthKey'' tid0),
                          s(MV ''T1start'' tid0), s(MV ''T1expire'' tid0)
                       |}
                       ( K ( s(AV ''C'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (A_2_enc_1 tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''4_2'', s(AV ''S'' tid0), s(MV ''ServerKey'' tid0),
                            s(MV ''T2start'' tid0), s(MV ''T2expire'' tid0), LN ''N2'' tid0
                         |}
                         ( LN ''AuthKey'' tid1 ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastforce dest: A_AuthKey_secret intro: event_predOrdI)
    next
      case (G_4_enc_1 tid2) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''2_1'', s(MV ''C'' tid2), s(AV ''G'' tid2),
                              LN ''AuthKey'' tid1, s(MV ''T1start'' tid2), s(MV ''T1expire'' tid2)
                           |}
                           ( K ( s(AV ''G'' tid2) ) ( s(MV ''A'' tid2) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest: A_AuthKey_secret intro: event_predOrdI)
      next
        case (A_2_enc tid3) note_unified facts = this facts
        thus ?thesis by (fastforce dest: G_ServerKey_secret intro: event_predOrdI)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

(* text: 
Server key secrecy is not given as it cannot check that authenticator is
uncompromised; i.e., the following does not hold

  S_ServerKey_secret: secret(S, 5, ServerKey, {C,A,G,S})

 *)

(* subsection:  Authentication Properties  *)

(* text: 
We first prove the following first send property to speedup the proof search.
 *)

lemma (in restricted_Kerberos_state) C_N2_first_send:
  assumes facts:
    "roleMap r tid1 = Some C"
    "LN ''N2'' tid1 : knows t"
  shows "predOrd t (St( tid1, C_3 )) (Ln(LN ''N2'' tid1))"
using facts proof(sources! " LN ''N2'' tid1 ")
  case C_3_N2 note_unified facts = this facts
  thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

lemma (in restricted_Kerberos_state) A_auth:
  assumes facts:
    "roleMap r tid2 = Some A"
    "RLKR(LN ''S'' tid2) ~: reveals t"
    "RLKR(s(AV ''A'' tid2)) ~: reveals t"
    "RLKR(s(MV ''C'' tid2)) ~: reveals t"
    "RLKR(s(MV ''G'' tid2)) ~: reveals t"
    "( tid2, A_2 ) : steps t"
  shows "predOrd t (St( tid2, A_1 )) (St( tid2, A_2 ))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
qed

lemma (in restricted_Kerberos_state) G_auth:
  assumes facts:
    "roleMap r tid3 = Some G"
    "RLKR(s(AV ''G'' tid3)) ~: reveals t"
    "RLKR(s(MV ''A'' tid3)) ~: reveals t"
    "RLKR(s(MV ''C'' tid3)) ~: reveals t"
    "RLKR(s(MV ''S'' tid3)) ~: reveals t"
    "( tid3, G_3 ) : steps t"
  shows
    "(?  tid1.
        (?  tid2.
           roleMap r tid1 = Some C &
           roleMap r tid2 = Some A &
           s(MV ''A'' tid1) = s(MV ''A'' tid3) &
           s(AV ''C'' tid1) = s(MV ''C'' tid3) &
           s(AV ''G'' tid1) = s(AV ''G'' tid3) &
           s(MV ''AuthKey'' tid1) = s(MV ''AuthKey'' tid3) &
           LN ''T1'' tid1 = s(MV ''T1'' tid3) &
           s(MV ''T1start'' tid1) = s(MV ''T1start'' tid3) &
           s(MV ''T1expire'' tid1) = s(MV ''T1expire'' tid3) &
           s(MV ''A'' tid3) = s(AV ''A'' tid2) &
           s(MV ''C'' tid3) = s(MV ''C'' tid2) &
           s(AV ''G'' tid3) = s(MV ''G'' tid2) &
           s(MV ''AuthKey'' tid3) = LN ''AuthKey'' tid2 &
           s(MV ''T1start'' tid3) = LN ''T1start'' tid2 &
           s(MV ''T1expire'' tid3) = LN ''T1expire'' tid2 &
           predOrd t (St( tid2, A_2 )) (St( tid1, C_2 )) &
           predOrd t (St( tid1, C_2 )) (St( tid1, C_3 )) &
           predOrd t (St( tid1, C_3 )) (St( tid3, G_3 ))))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''2_1'', s(MV ''C'' tid3), s(AV ''G'' tid3),
                          s(MV ''AuthKey'' tid3), s(MV ''T1start'' tid3), s(MV ''T1expire'' tid3)
                       |}
                       ( K ( s(AV ''G'' tid3) ) ( s(MV ''A'' tid3) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (A_2_enc tid4) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''3'', s(MV ''C'' tid3), s(MV ''T1'' tid3) |}
                         ( LN ''AuthKey'' tid4 ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastforce dest: A_AuthKey_secret intro: event_predOrdI)
    next
      case (C_3_enc tid5) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''2_2'', s(AV ''G'' tid5), LN ''AuthKey'' tid4,
                              s(MV ''T1start'' tid5), s(MV ''T1expire'' tid5)
                           |}
                           ( K ( s(AV ''C'' tid5) ) ( s(MV ''A'' tid5) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest: A_AuthKey_secret intro: event_predOrdI)
      next
        case (A_2_enc_1 tid6) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

(* text:  
Authentication for the server S is also rather weak, as it cannot check whether
the authenticator is compromised or not.
 *)

lemma (in restricted_Kerberos_state) S_auth:
  assumes facts:
    "roleMap r tid4 = Some S"
    "RLKR(s(AV ''S'' tid4)) ~: reveals t"
    "RLKR(s(MV ''C'' tid4)) ~: reveals t"
    "RLKR(s(MV ''G'' tid4)) ~: reveals t"
    "( tid4, S_5 ) : steps t"
  shows
    "(?  tid1.
        (?  tid3.
           (?  tid4.
              roleMap r tid3 = Some G &
              s(MV ''C'' tid4) = s(MV ''C'' tid3) &
              s(MV ''G'' tid4) = s(AV ''G'' tid3) &
              s(AV ''S'' tid4) = s(MV ''S'' tid3) &
              s(MV ''ServerKey'' tid4) = LN ''ServerKey'' tid3 &
              s(MV ''T2start'' tid4) = LN ''T2start'' tid3 &
              s(MV ''T2expire'' tid4) = LN ''T2expire'' tid3)))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''4_1'', s(MV ''C'' tid4), s(AV ''S'' tid4),
                          s(MV ''ServerKey'' tid4), s(MV ''T2start'' tid4), s(MV ''T2expire'' tid4)
                       |}
                       ( K ( s(MV ''G'' tid4) ) ( s(AV ''S'' tid4) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (G_4_enc tid5) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

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
              s(MV ''AuthKey'' tid1) = LN ''AuthKey'' tid2 &
              s(MV ''T1start'' tid1) = LN ''T1start'' tid2 &
              s(MV ''T1expire'' tid1) = LN ''T1expire'' tid2 &
              s(MV ''A'' tid1) = s(MV ''A'' tid3) &
              s(AV ''C'' tid1) = s(MV ''C'' tid3) &
              s(AV ''G'' tid1) = s(AV ''G'' tid3) &
              s(AV ''S'' tid1) = s(MV ''S'' tid3) &
              s(MV ''AuthKey'' tid1) = s(MV ''AuthKey'' tid3) &
              s(MV ''ServerKey'' tid1) = LN ''ServerKey'' tid3 &
              LN ''N2'' tid1 = s(MV ''N2'' tid3) &
              s(MV ''T2start'' tid1) = LN ''T2start'' tid3 &
              s(MV ''T2expire'' tid1) = LN ''T2expire'' tid3 &
              s(AV ''C'' tid1) = s(MV ''C'' tid4) &
              s(AV ''G'' tid1) = s(MV ''G'' tid4) &
              s(AV ''S'' tid1) = s(AV ''S'' tid4) &
              LN ''T2'' tid1 = s(MV ''T2'' tid4) &
              s(MV ''T2start'' tid1) = s(MV ''T2start'' tid4) &
              s(MV ''T2expire'' tid1) = s(MV ''T2expire'' tid4) &
              s(MV ''ServerKey'' tid1) = s(MV ''ServerKey'' tid4) &
              predOrd t (St( tid2, A_2 )) (St( tid1, C_2 )) &
              predOrd t (St( tid1, C_2 )) (St( tid1, C_3 )) &
              predOrd t (St( tid1, C_3 )) (St( tid3, G_3 )) &
              predOrd t (St( tid3, G_3 )) (St( tid3, G_4 )) &
              predOrd t (St( tid3, G_4 )) (St( tid1, C_4 )) &
              predOrd t (St( tid1, C_4 )) (St( tid1, C_5 )) &
              predOrd t (St( tid1, C_5 )) (St( tid4, S_5 )) &
              predOrd t (St( tid4, S_5 )) (St( tid4, S_6 )) &
              predOrd t (St( tid4, S_6 )) (St( tid1, C_6 )))))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''2_2'', s(AV ''G'' tid1), s(MV ''AuthKey'' tid1),
                          s(MV ''T1start'' tid1), s(MV ''T1expire'' tid1)
                       |}
                       ( K ( s(AV ''C'' tid1) ) ( s(MV ''A'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (A_2_enc_1 tid2) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''6'', LN ''T2'' tid1 |} ( s(MV ''ServerKey'' tid1) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastforce dest: C_ServerKey_secret intro: event_predOrdI)
    next
      case (S_6_enc tid3) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''4_2'', s(AV ''S'' tid1), s(MV ''ServerKey'' tid1),
                              s(MV ''T2start'' tid1), s(MV ''T2expire'' tid1), LN ''N2'' tid1
                           |}
                           ( LN ''AuthKey'' tid2 ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest: A_AuthKey_secret intro: event_predOrdI)
      next
        case (G_4_enc_1 tid4) note_unified facts = this facts
        have f1: "roleMap r tid1 = Some C" using facts by (auto intro: event_predOrdI)
        have f2: "LN ''N2'' tid1 : knows t" using facts by (auto intro: event_predOrdI)
        note facts = facts C_N2_first_send[OF f1 f2, simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''2_1'', s(MV ''C'' tid4), s(AV ''G'' tid4),
                                LN ''AuthKey'' tid2, s(MV ''T1start'' tid4), s(MV ''T1expire'' tid4)
                             |}
                             ( K ( s(AV ''G'' tid4) ) ( s(MV ''A'' tid4) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest: A_AuthKey_secret intro: event_predOrdI)
        next
          case (A_2_enc tid5) note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''4_1'', s(MV ''C'' tid3), s(AV ''S'' tid3),
                                  LN ''ServerKey'' tid4, s(MV ''T2start'' tid3), s(MV ''T2expire'' tid3)
                               |}
                               ( K ( s(MV ''G'' tid3) ) ( s(AV ''S'' tid3) ) ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest: G_ServerKey_secret intro: event_predOrdI)
          next
            case (G_4_enc tid5) note_unified facts = this facts
            thus ?thesis proof(sources! "
                             Enc {| LC ''5'', s(AV ''C'' tid1), LN ''T2'' tid1 |}
                                 ( LN ''ServerKey'' tid4 ) ")
              case fake note_unified facts = this facts
              thus ?thesis by (fastforce dest: G_ServerKey_secret intro: event_predOrdI)
            next
              case (C_5_enc tid5) note_unified facts = this facts
              thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
            qed (safe?, simp_all?, insert facts, (fastforce+)?)
          qed (safe?, simp_all?, insert facts, (fastforce+)?)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

end