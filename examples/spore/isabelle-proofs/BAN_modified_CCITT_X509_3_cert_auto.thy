theory "BAN_modified_CCITT_X509_3_cert_auto"
imports
  "../ESPLogic"
begin

(* section:  BAN modified version of CCITT X.509 (3)  *)

(* text: 
  Modelled after SPORE.

  Notable differences:
    1. We use explicit global constants instead of implicit typing to discern
       the different messages.
    
    2. We prove non-injective synchronization, which is stronger than the
       authentication on Ya and Yb required in the SPORE description.

    3. We equate all timestamps to a single global constant; i.e., we assume
       no checking of timestamps is done.

 *)

role A
where "A =
  [ Send ''1'' <| sAV ''A'',
                  PSign <| sC ''1_1'', sC ''Time'', sN ''Na'', sAV ''B'', sN ''Xa'',
                           PEnc <| sC ''1_2'', sN ''Ya'' |> ( sPK ''B'' )
                        |>
                        ( sPK ''A'' )
               |>
  , Recv ''2'' <| sAV ''B'',
                  PSign <| sC ''2_1'', sC ''Time'', sMV ''Nb'', sAV ''A'', sN ''Na'',
                           sMV ''Xb'', PEnc <| sC ''2_2'', sMV ''Yb'' |> ( sPK ''A'' )
                        |>
                        ( sPK ''B'' )
               |>
  , Send ''3'' <| sAV ''A'',
                  PSign <| sC ''3'', sAV ''B'', sMV ''Nb'' |> ( sPK ''A'' )
               |>
  ]"

role B
where "B =
  [ Recv ''1'' <| sMV ''A'',
                  PSign <| sC ''1_1'', sC ''Time'', sMV ''Na'', sAV ''B'', sMV ''Xa'',
                           PEnc <| sC ''1_2'', sMV ''Ya'' |> ( sPK ''B'' )
                        |>
                        ( PAsymPK ( sMV ''A'' ) )
               |>
  , Send ''2'' <| sAV ''B'',
                  PSign <| sC ''2_1'', sC ''Time'', sN ''Nb'', sMV ''A'', sMV ''Na'',
                           sN ''Xb'', PEnc <| sC ''2_2'', sN ''Yb'' |> ( PAsymPK ( sMV ''A'' ) )
                        |>
                        ( sPK ''B'' )
               |>
  , Recv ''3'' <| sMV ''A'',
                  PSign <| sC ''3'', sAV ''B'', sN ''Nb'' |> ( PAsymPK ( sMV ''A'' ) )
               |>
  ]"

protocol X509
where "X509 = { A, B }"

locale restricted_X509_state = X509_state

type_invariant X509_msc_typing for X509
where "X509_msc_typing = mk_typing
  [ ((B, ''A''), (KnownT B_1))
  , ((B, ''Na''), (KnownT B_1))
  , ((A, ''Nb''), (KnownT A_2))
  , ((B, ''Xa''), (KnownT B_1))
  , ((A, ''Xb''), (KnownT A_2))
  , ((B, ''Ya''), (SumT (KnownT B_1) (NonceT A ''Ya'')))
  , ((A, ''Yb''), (SumT (KnownT A_2) (NonceT B ''Yb'')))
  ]"

sublocale X509_state < X509_msc_typing_state
proof -
  have "(t,r,s) : approx X509_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF X509_msc_typing.monoTyp, completeness_cases_rule])
    case (A_2_Nb t r s tid0) note facts = this
    then interpret state: X509_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (A_2_Xb t r s tid0) note facts = this
    then interpret state: X509_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (A_2_Yb t r s tid0) note facts = this
    then interpret state: X509_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''2_2'', s(MV ''Yb'' tid0) |} ( PK ( s(AV ''A'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (B_1_A t r s tid0) note facts = this
    then interpret state: X509_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (B_1_Na t r s tid0) note facts = this
    then interpret state: X509_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (B_1_Xa t r s tid0) note facts = this
    then interpret state: X509_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (B_1_Ya t r s tid0) note facts = this
    then interpret state: X509_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''1_2'', s(MV ''Ya'' tid0) |} ( PK ( s(AV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  qed
  thus "X509_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context X509_state begin

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

lemma (in restricted_X509_state) A_Ya_secrecy:
  assumes facts:
    "roleMap r tid0 = Some A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "LN ''Ya'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''Ya'' tid0 ")
  case A_1_Ya note_unified facts = this facts
  thus ?thesis by (fastsimp dest!: ltk_secrecy)
next
  case A_1_Ya_1 note_unified facts = this facts
  thus ?thesis by (fastsimp dest!: ltk_secrecy)
qed (insert facts, fastsimp+)?

lemma (in restricted_X509_state) B_Yb_secrecy:
  assumes facts:
    "roleMap r tid0 = Some B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "LN ''Yb'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''Yb'' tid0 ")
  case B_2_Yb note_unified facts = this facts
  thus ?thesis by (fastsimp dest!: ltk_secrecy)
next
  case B_2_Yb_1 note_unified facts = this facts
  thus ?thesis by (fastsimp dest!: ltk_secrecy)
qed (insert facts, fastsimp+)?

lemma (in restricted_X509_state) B_Ya_secrecy:
  assumes facts:
    "roleMap r tid0 = Some B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, B_1 ) : steps t"
    "s(MV ''Ya'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''1_1'', LC ''Time'', s(MV ''Na'' tid0), s(AV ''B'' tid0),
                          s(MV ''Xa'' tid0),
                          Enc {| LC ''1_2'', s(MV ''Ya'' tid0) |} ( PK ( s(AV ''B'' tid0) ) )
                       |}
                       ( SK ( s(MV ''A'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (A_1_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp dest: A_Ya_secrecy intro: event_predOrdI)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_X509_state) A_Yb_secrecy:
  assumes facts:
    "roleMap r tid0 = Some A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "( tid0, A_2 ) : steps t"
    "s(MV ''Yb'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''2_1'', LC ''Time'', s(MV ''Nb'' tid0), s(AV ''A'' tid0),
                          LN ''Na'' tid0, s(MV ''Xb'' tid0),
                          Enc {| LC ''2_2'', s(MV ''Yb'' tid0) |} ( PK ( s(AV ''A'' tid0) ) )
                       |}
                       ( SK ( s(AV ''B'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (B_2_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp dest: B_Yb_secrecy intro: event_predOrdI)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_X509_state) A_noninjective_synch:
  assumes facts:
    "roleMap r tid1 = Some A"
    "RLKR(s(AV ''A'' tid1)) ~: reveals t"
    "RLKR(s(AV ''B'' tid1)) ~: reveals t"
    "( tid1, A_3 ) : steps t"
  shows
    "(?  tid2.
        roleMap r tid2 = Some B &
        s(AV ''A'' tid1) = s(MV ''A'' tid2) &
        s(AV ''B'' tid1) = s(AV ''B'' tid2) &
        LN ''Na'' tid1 = s(MV ''Na'' tid2) &
        s(MV ''Nb'' tid1) = LN ''Nb'' tid2 &
        LN ''Ya'' tid1 = s(MV ''Ya'' tid2) &
        s(MV ''Yb'' tid1) = LN ''Yb'' tid2 &
        predOrd t (St( tid1, A_1 )) (St( tid2, B_1 )) &
        predOrd t (St( tid2, B_2 )) (St( tid1, A_2 )) &
        predOrd t (St( tid1, A_1 )) (St( tid1, A_2 )) &
        predOrd t (St( tid1, A_2 )) (St( tid1, A_3 )) &
        predOrd t (St( tid2, B_1 )) (St( tid2, B_2 )))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''2_1'', LC ''Time'', s(MV ''Nb'' tid1), s(AV ''A'' tid1),
                          LN ''Na'' tid1, s(MV ''Xb'' tid1),
                          Enc {| LC ''2_2'', s(MV ''Yb'' tid1) |} ( PK ( s(AV ''A'' tid1) ) )
                       |}
                       ( SK ( s(AV ''B'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (B_2_enc_1 tid2) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''1_1'', LC ''Time'', LN ''Na'' tid1, s(AV ''B'' tid1),
                            s(MV ''Xa'' tid2),
                            Enc {| LC ''1_2'', s(MV ''Ya'' tid2) |} ( PK ( s(AV ''B'' tid1) ) )
                         |}
                         ( SK ( s(AV ''A'' tid1) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest!: ltk_secrecy)
    next
      case (A_1_enc_1 tid3) note_unified facts = this facts
      thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
    qed (insert facts, fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_X509_state) B_noninjective_synch:
  assumes facts:
    "roleMap r tid2 = Some B"
    "RLKR(s(AV ''B'' tid2)) ~: reveals t"
    "RLKR(s(MV ''A'' tid2)) ~: reveals t"
    "( tid2, B_3 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some A &
        s(AV ''A'' tid1) = s(MV ''A'' tid2) &
        s(AV ''B'' tid1) = s(AV ''B'' tid2) &
        LN ''Na'' tid1 = s(MV ''Na'' tid2) &
        s(MV ''Nb'' tid1) = LN ''Nb'' tid2 &
        LN ''Ya'' tid1 = s(MV ''Ya'' tid2) &
        s(MV ''Yb'' tid1) = LN ''Yb'' tid2 &
        predOrd t (St( tid1, A_1 )) (St( tid2, B_1 )) &
        predOrd t (St( tid2, B_2 )) (St( tid1, A_2 )) &
        predOrd t (St( tid1, A_3 )) (St( tid2, B_3 )) &
        predOrd t (St( tid1, A_1 )) (St( tid1, A_2 )) &
        predOrd t (St( tid1, A_2 )) (St( tid1, A_3 )) &
        predOrd t (St( tid2, B_1 )) (St( tid2, B_2 )) &
        predOrd t (St( tid2, B_2 )) (St( tid2, B_3 )))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''1_1'', LC ''Time'', s(MV ''Na'' tid2), s(AV ''B'' tid2),
                          s(MV ''Xa'' tid2),
                          Enc {| LC ''1_2'', s(MV ''Ya'' tid2) |} ( PK ( s(AV ''B'' tid2) ) )
                       |}
                       ( SK ( s(MV ''A'' tid2) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (A_1_enc_1 tid3) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''3'', s(AV ''B'' tid2), LN ''Nb'' tid2 |}
                         ( SK ( s(AV ''A'' tid3) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest!: ltk_secrecy)
    next
      case (A_3_enc tid4) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''2_1'', LC ''Time'', LN ''Nb'' tid2, s(AV ''A'' tid3),
                              LN ''Na'' tid4, s(MV ''Xb'' tid4),
                              Enc {| LC ''2_2'', s(MV ''Yb'' tid4) |} ( PK ( s(AV ''A'' tid3) ) )
                           |}
                           ( SK ( s(AV ''B'' tid2) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastsimp dest!: ltk_secrecy)
      next
        case (B_2_enc_1 tid5) note_unified facts = this facts
        thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
      qed (insert facts, fastsimp+)?
    qed (insert facts, fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

end