theory "Woo_Lam_Pi_cert_auto"
imports
  "../ESPLogic"
begin

(* section:  Woo and Lam Pi 3  *)

(* text: 
  Modelled after SPORE.

  Notable differences:
    1. We use explicit global constants instead of implicit typing to discern
       the different messages.
    
    2. We prove non-injective synchronization, which is stronger than the
       authenticatino requirement stated in the description.

    3. We added the identity B to the plaintext of the fourth message, as the
       server must know it for looking up the key k(B,S).

 *)

role A
where "A =
  [ Send ''1'' ( sAV ''A'' )
  , Recv ''2'' ( sMV ''Nb'' )
  , Send ''3'' ( PEnc <| sC ''3'', sMV ''Nb'' |> ( sK ''A'' ''S'' ) )
  ]"

role B
where "B =
  [ Recv ''1'' ( sMV ''A'' )
  , Send ''2'' ( sN ''Nb'' )
  , Recv ''3'' ( sMV ''Ticket'' )
  , Send ''4'' <| sAV ''B'',
                  PEnc <| sC ''4'', sMV ''A'', sMV ''Ticket'' |> ( sK ''B'' ''S'' )
               |>
  , Recv ''5'' ( PEnc <| sC ''5'', sMV ''A'', sN ''Nb'' |>
                      ( sK ''B'' ''S'' )
               )
  ]"

role S
where "S =
  [ Recv ''4'' <| sMV ''B'',
                  PEnc <| sC ''4'', sMV ''A'',
                          PEnc <| sC ''3'', sMV ''Nb'' |> ( PSymK ( sMV ''A'' ) ( sAV ''S'' ) )
                       |>
                       ( PSymK ( sMV ''B'' ) ( sAV ''S'' ) )
               |>
  , Send ''5'' ( PEnc <| sC ''5'', sMV ''A'', sMV ''Nb'' |>
                      ( PSymK ( sMV ''B'' ) ( sAV ''S'' ) )
               )
  ]"

protocol WooLamPi
where "WooLamPi = { A, B, S }"

locale restricted_WooLamPi_state = WooLamPi_state

type_invariant WooLamPi_msc_typing for WooLamPi
where "WooLamPi_msc_typing = mk_typing
  [ ((B, ''A''), (KnownT B_1))
  , ((S, ''A''), (SumT (KnownT S_4) AgentT))
  , ((S, ''B''), (KnownT S_4))
  , ((A, ''Nb''), (KnownT A_2))
  , ((S, ''Nb''), (SumT (KnownT S_4) (NonceT B ''Nb'')))
  , ((B, ''Ticket''), (KnownT B_3))
  ]"

sublocale WooLamPi_state < WooLamPi_msc_typing_state
proof -
  have "(t,r,s) : approx WooLamPi_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF WooLamPi_msc_typing.monoTyp, completeness_cases_rule])
    case (S_4_A t r s tid0) note facts = this
    then interpret state: WooLamPi_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''4'', s(MV ''A'' tid0),
               Enc {| LC ''3'', s(MV ''Nb'' tid0) |}
                   ( K ( s(MV ''A'' tid0) ) ( s(AV ''S'' tid0) ) )
            |}
            ( K ( s(MV ''B'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (S_4_B t r s tid0) note facts = this
    then interpret state: WooLamPi_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (S_4_Nb t r s tid0) note facts = this
    then interpret state: WooLamPi_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''4'', s(MV ''A'' tid0),
               Enc {| LC ''3'', s(MV ''Nb'' tid0) |}
                   ( K ( s(MV ''A'' tid0) ) ( s(AV ''S'' tid0) ) )
            |}
            ( K ( s(MV ''B'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''3'', s(MV ''Nb'' tid0) |}
                           ( K ( s(MV ''A'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
      qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
    next
      case (B_4_enc tid1) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''3'', s(MV ''Nb'' tid0) |}
                           ( K ( s(MV ''A'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
      qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
    qed (insert facts, fastsimp+)?
  qed
  thus "WooLamPi_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context WooLamPi_state begin

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

(* subsection:  Security Properties  *)

lemma (in restricted_WooLamPi_state) B_noninjective_agreement:
  assumes facts:
    "roleMap r tid2 = Some B"
    "RLKR(s(AV ''B'' tid2)) ~: reveals t"
    "RLKR(s(AV ''S'' tid2)) ~: reveals t"
    "RLKR(s(MV ''A'' tid2)) ~: reveals t"
    "( tid2, B_5 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some A &
        s(AV ''A'' tid1) = s(MV ''A'' tid2) &
        s(AV ''S'' tid1) = s(AV ''S'' tid2) &
        s(MV ''Nb'' tid1) = LN ''Nb'' tid2)"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''5'', s(MV ''A'' tid2), LN ''Nb'' tid2 |}
                       ( K ( s(AV ''B'' tid2) ) ( s(AV ''S'' tid2) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (S_5_enc tid3) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''4'', s(MV ''A'' tid2),
                            Enc {| LC ''3'', LN ''Nb'' tid2 |}
                                ( K ( s(MV ''A'' tid2) ) ( s(AV ''S'' tid2) ) )
                         |}
                         ( K ( s(AV ''B'' tid2) ) ( s(AV ''S'' tid2) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest!: ltk_secrecy)
    next
      case (B_4_enc tid4) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''3'', LN ''Nb'' tid2 |}
                           ( K ( s(MV ''A'' tid2) ) ( s(AV ''S'' tid2) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastsimp dest!: ltk_secrecy)
      next
        case (A_3_enc tid5) note_unified facts = this facts
        thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
      qed (insert facts, fastsimp+)?
    qed (insert facts, fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

end