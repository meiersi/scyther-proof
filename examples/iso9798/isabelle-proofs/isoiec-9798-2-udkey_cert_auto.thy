theory "isoiec-9798-2-udkey_cert_auto"
imports
  "../ESPLogic"
begin

role isoiec_9798_2_1_udkey_A
where "isoiec_9798_2_1_udkey_A =
  [ Send ''leak_A'' ( sN ''TNA'' )
  , Recv ''text_1'' <| sMV ''Text1'', sMV ''Text2'' |>
  , Send ''1'' <| sAV ''A'', sAV ''B'', sMV ''Text2'',
                  PEnc <| sC ''isoiec_9798_2_1_enc_1'', sN ''TNA'', sMV ''Text1'' |>
                       ( sK ''A'' ''B'' )
               |>
  ]"

role isoiec_9798_2_1_udkey_B
where "isoiec_9798_2_1_udkey_B =
  [ Recv ''1'' <| sMV ''A'', sAV ''B'', sMV ''Text2'',
                  PEnc <| sC ''isoiec_9798_2_1_enc_1'', sMV ''TNA'', sMV ''Text1'' |>
                       ( PSymK ( sMV ''A'' ) ( sAV ''B'' ) )
               |>
  ]"

protocol isoiec_9798_2_1_udkey
where "isoiec_9798_2_1_udkey =
{ isoiec_9798_2_1_udkey_A, isoiec_9798_2_1_udkey_B }"

locale restricted_isoiec_9798_2_1_udkey_state = isoiec_9798_2_1_udkey_state

type_invariant isoiec_9798_2_1_udkey_msc_typing for isoiec_9798_2_1_udkey
where "isoiec_9798_2_1_udkey_msc_typing = mk_typing
  [ ((isoiec_9798_2_1_udkey_B, ''A''), (KnownT isoiec_9798_2_1_udkey_B_1))
  , ((isoiec_9798_2_1_udkey_B, ''TNA''),
     (SumT (KnownT isoiec_9798_2_1_udkey_B_1) (NonceT isoiec_9798_2_1_udkey_A ''TNA'')))
  , ((isoiec_9798_2_1_udkey_A, ''Text1''),
     (KnownT isoiec_9798_2_1_udkey_A_text_1))
  , ((isoiec_9798_2_1_udkey_B, ''Text1''),
     (KnownT isoiec_9798_2_1_udkey_B_1))
  , ((isoiec_9798_2_1_udkey_A, ''Text2''),
     (KnownT isoiec_9798_2_1_udkey_A_text_1))
  , ((isoiec_9798_2_1_udkey_B, ''Text2''),
     (KnownT isoiec_9798_2_1_udkey_B_1))
  ]"

sublocale isoiec_9798_2_1_udkey_state < isoiec_9798_2_1_udkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_2_1_udkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_2_1_udkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_2_1_udkey_A_text_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_1_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_1_udkey_A_text_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_1_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_1_udkey_B_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_1_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_1_udkey_B_1_TNA t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_1_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_1_enc_1'', s(MV ''TNA'' tid0),
               s(MV ''Text1'' tid0)
            |}
            ( K ( s(MV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_1_udkey_B_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_1_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_1_enc_1'', s(MV ''TNA'' tid0),
               s(MV ''Text1'' tid0)
            |}
            ( K ( s(MV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_1_udkey_B_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_1_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_2_1_udkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_2_1_udkey_state begin

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

lemma (in restricted_isoiec_9798_2_1_udkey_state) B_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_1_udkey_B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_1_udkey_B_1 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_1_udkey_A &
        ( tid1, isoiec_9798_2_1_udkey_A_1 ) : steps t &
        {| s(AV ''A'' tid1), s(AV ''B'' tid1), LN ''TNA'' tid1,
           s(MV ''Text1'' tid1)
        |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''TNA'' tid0),
                s(MV ''Text1'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_1_enc_1'', s(MV ''TNA'' tid0),
                          s(MV ''Text1'' tid0)
                       |}
                       ( K ( s(MV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_1_udkey_A_1_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
  qed (insert facts, fastsimp+)?
qed

role isoiec_9798_2_2_udkey_A
where "isoiec_9798_2_2_udkey_A =
  [ Recv ''1'' <| sMV ''B'', sAV ''A'', sMV ''RB'', sMV ''Text1'' |>
  , Recv ''text_2'' <| sMV ''Text2'', sMV ''Text3'' |>
  , Send ''2'' <| sAV ''A'', sMV ''B'', sMV ''Text3'',
                  PEnc <| sC ''isoiec_9798_2_2_enc_2'', sMV ''RB'', sMV ''Text2'' |>
                       ( PSymK ( sAV ''A'' ) ( sMV ''B'' ) )
               |>
  ]"

role isoiec_9798_2_2_udkey_B
where "isoiec_9798_2_2_udkey_B =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''B'', sAV ''A'', sN ''RB'', sMV ''Text1'' |>
  , Recv ''2'' <| sAV ''A'', sAV ''B'', sMV ''Text3'',
                  PEnc <| sC ''isoiec_9798_2_2_enc_2'', sN ''RB'', sMV ''Text2'' |>
                       ( sK ''A'' ''B'' )
               |>
  ]"

protocol isoiec_9798_2_2_udkey
where "isoiec_9798_2_2_udkey =
{ isoiec_9798_2_2_udkey_A, isoiec_9798_2_2_udkey_B }"

locale restricted_isoiec_9798_2_2_udkey_state = isoiec_9798_2_2_udkey_state

type_invariant isoiec_9798_2_2_udkey_msc_typing for isoiec_9798_2_2_udkey
where "isoiec_9798_2_2_udkey_msc_typing = mk_typing
  [ ((isoiec_9798_2_2_udkey_A, ''B''), (KnownT isoiec_9798_2_2_udkey_A_1))
  , ((isoiec_9798_2_2_udkey_A, ''RB''), (KnownT isoiec_9798_2_2_udkey_A_1))
  , ((isoiec_9798_2_2_udkey_A, ''Text1''),
     (KnownT isoiec_9798_2_2_udkey_A_1))
  , ((isoiec_9798_2_2_udkey_B, ''Text1''),
     (KnownT isoiec_9798_2_2_udkey_B_text_1))
  , ((isoiec_9798_2_2_udkey_A, ''Text2''),
     (KnownT isoiec_9798_2_2_udkey_A_text_2))
  , ((isoiec_9798_2_2_udkey_B, ''Text2''),
     (KnownT isoiec_9798_2_2_udkey_B_2))
  , ((isoiec_9798_2_2_udkey_A, ''Text3''),
     (KnownT isoiec_9798_2_2_udkey_A_text_2))
  , ((isoiec_9798_2_2_udkey_B, ''Text3''),
     (KnownT isoiec_9798_2_2_udkey_B_2))
  ]"

sublocale isoiec_9798_2_2_udkey_state < isoiec_9798_2_2_udkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_2_2_udkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_2_2_udkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_2_2_udkey_A_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_2_udkey_A_1_RB t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_2_udkey_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_2_udkey_A_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_2_udkey_A_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_2_udkey_B_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_2_enc_2'', LN ''RB'' tid0, s(MV ''Text2'' tid0)
            |}
            ( K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_2_udkey_B_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_2_2_udkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_2_2_udkey_state begin

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

lemma (in restricted_isoiec_9798_2_2_udkey_state) B_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_2_udkey_B"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_2_udkey_B_2 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_2_udkey_A &
        ( tid1, isoiec_9798_2_2_udkey_A_2 ) : steps t &
        {| s(AV ''A'' tid1), s(MV ''B'' tid1), s(MV ''RB'' tid1),
           s(MV ''Text2'' tid1)
        |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), LN ''RB'' tid0,
                s(MV ''Text2'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_2_enc_2'', LN ''RB'' tid0, s(MV ''Text2'' tid0)
                       |}
                       ( K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_2_udkey_A_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
  qed (insert facts, fastsimp+)?
qed

role isoiec_9798_2_3_udkey_A
where "isoiec_9798_2_3_udkey_A =
  [ Send ''leak_A'' ( sN ''TNA'' )
  , Recv ''text_1'' <| sMV ''Text1'', sMV ''Text2'' |>
  , Send ''1'' <| sAV ''A'', sAV ''B'', sMV ''Text2'',
                  PEnc <| sC ''isoiec_9798_2_3_enc_1'', sN ''TNA'', sMV ''Text1'' |>
                       ( sK ''A'' ''B'' )
               |>
  , Recv ''2'' <| sAV ''B'', sAV ''A'', sMV ''Text4'',
                  PEnc <| sC ''isoiec_9798_2_3_enc_2'', sMV ''TNB'', sMV ''Text3'' |>
                       ( sK ''B'' ''A'' )
               |>
  ]"

role isoiec_9798_2_3_udkey_B
where "isoiec_9798_2_3_udkey_B =
  [ Send ''leak_B'' ( sN ''TNB'' )
  , Recv ''1'' <| sMV ''A'', sAV ''B'', sMV ''Text2'',
                  PEnc <| sC ''isoiec_9798_2_3_enc_1'', sMV ''TNA'', sMV ''Text1'' |>
                       ( PSymK ( sMV ''A'' ) ( sAV ''B'' ) )
               |>
  , Recv ''text_2'' <| sMV ''Text3'', sMV ''Text4'' |>
  , Send ''2'' <| sAV ''B'', sMV ''A'', sMV ''Text4'',
                  PEnc <| sC ''isoiec_9798_2_3_enc_2'', sN ''TNB'', sMV ''Text3'' |>
                       ( PSymK ( sAV ''B'' ) ( sMV ''A'' ) )
               |>
  ]"

protocol isoiec_9798_2_3_udkey
where "isoiec_9798_2_3_udkey =
{ isoiec_9798_2_3_udkey_A, isoiec_9798_2_3_udkey_B }"

locale restricted_isoiec_9798_2_3_udkey_state = isoiec_9798_2_3_udkey_state

type_invariant isoiec_9798_2_3_udkey_msc_typing for isoiec_9798_2_3_udkey
where "isoiec_9798_2_3_udkey_msc_typing = mk_typing
  [ ((isoiec_9798_2_3_udkey_B, ''A''), (KnownT isoiec_9798_2_3_udkey_B_1))
  , ((isoiec_9798_2_3_udkey_B, ''TNA''),
     (SumT (KnownT isoiec_9798_2_3_udkey_B_1) (NonceT isoiec_9798_2_3_udkey_A ''TNA'')))
  , ((isoiec_9798_2_3_udkey_A, ''TNB''),
     (SumT (KnownT isoiec_9798_2_3_udkey_A_2) (NonceT isoiec_9798_2_3_udkey_B ''TNB'')))
  , ((isoiec_9798_2_3_udkey_A, ''Text1''),
     (KnownT isoiec_9798_2_3_udkey_A_text_1))
  , ((isoiec_9798_2_3_udkey_B, ''Text1''),
     (KnownT isoiec_9798_2_3_udkey_B_1))
  , ((isoiec_9798_2_3_udkey_A, ''Text2''),
     (KnownT isoiec_9798_2_3_udkey_A_text_1))
  , ((isoiec_9798_2_3_udkey_B, ''Text2''),
     (KnownT isoiec_9798_2_3_udkey_B_1))
  , ((isoiec_9798_2_3_udkey_A, ''Text3''),
     (KnownT isoiec_9798_2_3_udkey_A_2))
  , ((isoiec_9798_2_3_udkey_B, ''Text3''),
     (KnownT isoiec_9798_2_3_udkey_B_text_2))
  , ((isoiec_9798_2_3_udkey_A, ''Text4''),
     (KnownT isoiec_9798_2_3_udkey_A_2))
  , ((isoiec_9798_2_3_udkey_B, ''Text4''),
     (KnownT isoiec_9798_2_3_udkey_B_text_2))
  ]"

sublocale isoiec_9798_2_3_udkey_state < isoiec_9798_2_3_udkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_2_3_udkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_2_3_udkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_2_3_udkey_A_text_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_3_udkey_A_text_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_3_udkey_A_2_TNB t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_3_enc_2'', s(MV ''TNB'' tid0),
               s(MV ''Text3'' tid0)
            |}
            ( K ( s(AV ''B'' tid0) ) ( s(AV ''A'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_3_udkey_A_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_3_enc_2'', s(MV ''TNB'' tid0),
               s(MV ''Text3'' tid0)
            |}
            ( K ( s(AV ''B'' tid0) ) ( s(AV ''A'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_3_udkey_A_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_3_udkey_B_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_3_udkey_B_1_TNA t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_3_enc_1'', s(MV ''TNA'' tid0),
               s(MV ''Text1'' tid0)
            |}
            ( K ( s(MV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_3_udkey_B_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_3_enc_1'', s(MV ''TNA'' tid0),
               s(MV ''Text1'' tid0)
            |}
            ( K ( s(MV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_3_udkey_B_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_3_udkey_B_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_3_udkey_B_text_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_2_3_udkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_2_3_udkey_state begin

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

lemma (in restricted_isoiec_9798_2_3_udkey_state) A_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_3_udkey_A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_3_udkey_A_2 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_3_udkey_B &
        ( tid1, isoiec_9798_2_3_udkey_B_2 ) : steps t &
        {| s(MV ''A'' tid1), s(AV ''B'' tid1), LN ''TNB'' tid1,
           s(MV ''Text3'' tid1)
        |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''TNB'' tid0),
                s(MV ''Text3'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_3_enc_2'', s(MV ''TNB'' tid0),
                          s(MV ''Text3'' tid0)
                       |}
                       ( K ( s(AV ''B'' tid0) ) ( s(AV ''A'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_3_udkey_B_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_isoiec_9798_2_3_udkey_state) B_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_3_udkey_B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_3_udkey_B_2 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_3_udkey_A &
        ( tid1, isoiec_9798_2_3_udkey_A_1 ) : steps t &
        {| s(AV ''A'' tid1), s(AV ''B'' tid1), LN ''TNA'' tid1,
           s(MV ''Text1'' tid1)
        |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''TNA'' tid0),
                s(MV ''Text1'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_3_enc_1'', s(MV ''TNA'' tid0),
                          s(MV ''Text1'' tid0)
                       |}
                       ( K ( s(MV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_3_udkey_A_1_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
  qed (insert facts, fastsimp+)?
qed

role isoiec_9798_2_4_udkey_A
where "isoiec_9798_2_4_udkey_A =
  [ Recv ''1'' <| sMV ''B'', sAV ''A'', sMV ''RB'', sMV ''Text1'' |>
  , Recv ''text_2'' <| sMV ''Text2'', sMV ''Text3'' |>
  , Send ''2'' <| sAV ''A'', sMV ''B'', sMV ''Text3'',
                  PEnc <| sC ''isoiec_9798_2_4_enc_1'', sN ''RA'', sMV ''RB'',
                          sMV ''Text2''
                       |>
                       ( PSymK ( sAV ''A'' ) ( sMV ''B'' ) )
               |>
  , Recv ''3'' <| sMV ''B'', sAV ''A'', sMV ''Text5'',
                  PEnc <| sC ''isoiec_9798_2_4_enc_2'', sMV ''RB'', sN ''RA'',
                          sMV ''Text4''
                       |>
                       ( PSymK ( sMV ''B'' ) ( sAV ''A'' ) )
               |>
  ]"

role isoiec_9798_2_4_udkey_B
where "isoiec_9798_2_4_udkey_B =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''B'', sAV ''A'', sN ''RB'', sMV ''Text1'' |>
  , Recv ''2'' <| sAV ''A'', sAV ''B'', sMV ''Text3'',
                  PEnc <| sC ''isoiec_9798_2_4_enc_1'', sMV ''RA'', sN ''RB'',
                          sMV ''Text2''
                       |>
                       ( sK ''A'' ''B'' )
               |>
  , Recv ''text_3'' <| sMV ''Text4'', sMV ''Text5'' |>
  , Send ''3'' <| sAV ''B'', sAV ''A'', sMV ''Text5'',
                  PEnc <| sC ''isoiec_9798_2_4_enc_2'', sN ''RB'', sMV ''RA'',
                          sMV ''Text4''
                       |>
                       ( sK ''B'' ''A'' )
               |>
  ]"

protocol isoiec_9798_2_4_udkey
where "isoiec_9798_2_4_udkey =
{ isoiec_9798_2_4_udkey_A, isoiec_9798_2_4_udkey_B }"

locale restricted_isoiec_9798_2_4_udkey_state = isoiec_9798_2_4_udkey_state

type_invariant isoiec_9798_2_4_udkey_msc_typing for isoiec_9798_2_4_udkey
where "isoiec_9798_2_4_udkey_msc_typing = mk_typing
  [ ((isoiec_9798_2_4_udkey_A, ''B''), (KnownT isoiec_9798_2_4_udkey_A_1))
  , ((isoiec_9798_2_4_udkey_B, ''RA''),
     (SumT (KnownT isoiec_9798_2_4_udkey_B_2) (NonceT isoiec_9798_2_4_udkey_A ''RA'')))
  , ((isoiec_9798_2_4_udkey_A, ''RB''), (KnownT isoiec_9798_2_4_udkey_A_1))
  , ((isoiec_9798_2_4_udkey_A, ''Text1''),
     (KnownT isoiec_9798_2_4_udkey_A_1))
  , ((isoiec_9798_2_4_udkey_B, ''Text1''),
     (KnownT isoiec_9798_2_4_udkey_B_text_1))
  , ((isoiec_9798_2_4_udkey_A, ''Text2''),
     (KnownT isoiec_9798_2_4_udkey_A_text_2))
  , ((isoiec_9798_2_4_udkey_B, ''Text2''),
     (KnownT isoiec_9798_2_4_udkey_B_2))
  , ((isoiec_9798_2_4_udkey_A, ''Text3''),
     (KnownT isoiec_9798_2_4_udkey_A_text_2))
  , ((isoiec_9798_2_4_udkey_B, ''Text3''),
     (KnownT isoiec_9798_2_4_udkey_B_2))
  , ((isoiec_9798_2_4_udkey_A, ''Text4''),
     (KnownT isoiec_9798_2_4_udkey_A_3))
  , ((isoiec_9798_2_4_udkey_B, ''Text4''),
     (KnownT isoiec_9798_2_4_udkey_B_text_3))
  , ((isoiec_9798_2_4_udkey_A, ''Text5''),
     (KnownT isoiec_9798_2_4_udkey_A_3))
  , ((isoiec_9798_2_4_udkey_B, ''Text5''),
     (KnownT isoiec_9798_2_4_udkey_B_text_3))
  ]"

sublocale isoiec_9798_2_4_udkey_state < isoiec_9798_2_4_udkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_2_4_udkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_2_4_udkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_2_4_udkey_A_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_udkey_A_1_RB t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_udkey_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_udkey_A_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_udkey_A_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_udkey_A_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_4_enc_2'', s(MV ''RB'' tid0), LN ''RA'' tid0,
               s(MV ''Text4'' tid0)
            |}
            ( K ( s(MV ''B'' tid0) ) ( s(AV ''A'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_4_udkey_A_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_udkey_B_2_RA t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_4_enc_1'', s(MV ''RA'' tid0), LN ''RB'' tid0,
               s(MV ''Text2'' tid0)
            |}
            ( K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_4_udkey_B_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_4_enc_1'', s(MV ''RA'' tid0), LN ''RB'' tid0,
               s(MV ''Text2'' tid0)
            |}
            ( K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_4_udkey_B_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_udkey_B_text_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_udkey_B_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_2_4_udkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_2_4_udkey_state begin

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

lemma (in restricted_isoiec_9798_2_4_udkey_state) A_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_4_udkey_A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_4_udkey_A_3 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_4_udkey_B &
        ( tid1, isoiec_9798_2_4_udkey_B_3 ) : steps t &
        {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(MV ''RA'' tid1), LN ''RB'' tid1,
           s(MV ''Text2'' tid1), s(MV ''Text4'' tid1)
        |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), LN ''RA'' tid0,
                s(MV ''RB'' tid0), s(MV ''Text2'' tid0), s(MV ''Text4'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_4_enc_2'', s(MV ''RB'' tid0), LN ''RA'' tid0,
                          s(MV ''Text4'' tid0)
                       |}
                       ( K ( s(MV ''B'' tid0) ) ( s(AV ''A'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_4_udkey_B_3_enc tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''isoiec_9798_2_4_enc_1'', LN ''RA'' tid0, LN ''RB'' tid1,
                            s(MV ''Text2'' tid1)
                         |}
                         ( K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid1) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest!: ltk_secrecy)
    next
      case (isoiec_9798_2_4_udkey_A_2_enc tid2) note_unified facts = this facts
      thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
    qed (insert facts, fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_isoiec_9798_2_4_udkey_state) B_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_4_udkey_B"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_4_udkey_B_2 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_4_udkey_A &
        ( tid1, isoiec_9798_2_4_udkey_A_2 ) : steps t &
        {| s(AV ''A'' tid1), s(MV ''B'' tid1), LN ''RA'' tid1, s(MV ''RB'' tid1),
           s(MV ''Text2'' tid1)
        |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''RA'' tid0),
                LN ''RB'' tid0, s(MV ''Text2'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_4_enc_1'', s(MV ''RA'' tid0), LN ''RB'' tid0,
                          s(MV ''Text2'' tid0)
                       |}
                       ( K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_4_udkey_A_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
  qed (insert facts, fastsimp+)?
qed

role isoiec_9798_2_5_udkey_A
where "isoiec_9798_2_5_udkey_A =
  [ Send ''leak_A'' <| sN ''TVPa'', sN ''TNa'' |>
  , Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''A'', sAV ''P'', sN ''TVPa'', sAV ''B'',
                  sMV ''Text1''
               |>
  , Recv ''2'' <| sAV ''P'', sAV ''A'', sMV ''Text4'',
                  PEnc <| sC ''isoiec_9798_2_5_enc_2_1'', sN ''TVPa'', sMV ''Kab'',
                          sAV ''B'', sMV ''Text3''
                       |>
                       ( sK ''A'' ''P'' ),
                  sMV ''TokenPA_for_B''
               |>
  , Recv ''text_3'' <| sMV ''Text5'', sMV ''Text6'' |>
  , Send ''3'' <| sAV ''A'', sAV ''B'', sMV ''Text6'', sAV ''P'',
                  sMV ''TokenPA_for_B'',
                  PEnc <| sC ''isoiec_9798_2_5_enc_3'', sN ''TNa'', sAV ''B'',
                          sMV ''Text5''
                       |>
                       ( sMV ''Kab'' )
               |>
  , Recv ''4'' <| sAV ''B'', sAV ''A'', sMV ''Text8'',
                  PEnc <| sC ''isoiec_9798_2_5_enc_4'', sMV ''TNb'', sAV ''A'',
                          sMV ''Text7''
                       |>
                       ( sMV ''Kab'' )
               |>
  ]"

role isoiec_9798_2_5_udkey_B
where "isoiec_9798_2_5_udkey_B =
  [ Send ''leak_B'' ( sN ''TNb'' )
  , Recv ''3'' <| sMV ''A'', sAV ''B'', sMV ''Text6'', sMV ''P'',
                  PEnc <| sC ''isoiec_9798_2_5_enc_2_2'', sMV ''TNp'', sMV ''Kab'',
                          sMV ''A'', sMV ''Text2''
                       |>
                       ( PSymK ( sAV ''B'' ) ( sMV ''P'' ) ),
                  PEnc <| sC ''isoiec_9798_2_5_enc_3'', sMV ''TNa'', sAV ''B'',
                          sMV ''Text5''
                       |>
                       ( sMV ''Kab'' )
               |>
  , Recv ''text_4'' <| sMV ''Text7'', sMV ''Text8'' |>
  , Send ''4'' <| sAV ''B'', sMV ''A'', sMV ''Text8'',
                  PEnc <| sC ''isoiec_9798_2_5_enc_4'', sN ''TNb'', sMV ''A'',
                          sMV ''Text7''
                       |>
                       ( sMV ''Kab'' )
               |>
  ]"

role isoiec_9798_2_5_udkey_P
where "isoiec_9798_2_5_udkey_P =
  [ Send ''leak_P'' ( sN ''TNp'' )
  , Recv ''1'' <| sMV ''A'', sAV ''P'', sMV ''TVPa'', sMV ''B'',
                  sMV ''Text1''
               |>
  , Recv ''text_2'' <| sMV ''Text2'', sMV ''Text3'', sMV ''Text4'' |>
  , Send ''2'' <| sAV ''P'', sMV ''A'', sMV ''Text4'',
                  PEnc <| sC ''isoiec_9798_2_5_enc_2_1'', sMV ''TVPa'', sN ''Kab'',
                          sMV ''B'', sMV ''Text3''
                       |>
                       ( PSymK ( sMV ''A'' ) ( sAV ''P'' ) ),
                  PEnc <| sC ''isoiec_9798_2_5_enc_2_2'', sN ''TNp'', sN ''Kab'',
                          sMV ''A'', sMV ''Text2''
                       |>
                       ( PSymK ( sMV ''B'' ) ( sAV ''P'' ) )
               |>
  ]"

protocol isoiec_9798_2_5_udkey
where "isoiec_9798_2_5_udkey =
{ isoiec_9798_2_5_udkey_A, isoiec_9798_2_5_udkey_B,
  isoiec_9798_2_5_udkey_P
}"

locale restricted_isoiec_9798_2_5_udkey_state = isoiec_9798_2_5_udkey_state

type_invariant isoiec_9798_2_5_udkey_msc_typing for isoiec_9798_2_5_udkey
where "isoiec_9798_2_5_udkey_msc_typing = mk_typing
  [ ((isoiec_9798_2_5_udkey_B, ''A''), (KnownT isoiec_9798_2_5_udkey_B_3))
  , ((isoiec_9798_2_5_udkey_P, ''A''), (KnownT isoiec_9798_2_5_udkey_P_1))
  , ((isoiec_9798_2_5_udkey_P, ''B''), (KnownT isoiec_9798_2_5_udkey_P_1))
  , ((isoiec_9798_2_5_udkey_A, ''Kab''),
     (SumT (KnownT isoiec_9798_2_5_udkey_A_2) (NonceT isoiec_9798_2_5_udkey_P ''Kab'')))
  , ((isoiec_9798_2_5_udkey_B, ''Kab''),
     (SumT (KnownT isoiec_9798_2_5_udkey_B_3) (NonceT isoiec_9798_2_5_udkey_P ''Kab'')))
  , ((isoiec_9798_2_5_udkey_B, ''P''), (KnownT isoiec_9798_2_5_udkey_B_3))
  , ((isoiec_9798_2_5_udkey_B, ''TNa''),
     (SumT (KnownT isoiec_9798_2_5_udkey_B_3) (NonceT isoiec_9798_2_5_udkey_A ''TNa'')))
  , ((isoiec_9798_2_5_udkey_A, ''TNb''),
     (SumT (KnownT isoiec_9798_2_5_udkey_A_4) (NonceT isoiec_9798_2_5_udkey_B ''TNb'')))
  , ((isoiec_9798_2_5_udkey_B, ''TNp''),
     (SumT (KnownT isoiec_9798_2_5_udkey_B_3) (NonceT isoiec_9798_2_5_udkey_P ''TNp'')))
  , ((isoiec_9798_2_5_udkey_P, ''TVPa''),
     (KnownT isoiec_9798_2_5_udkey_P_1))
  , ((isoiec_9798_2_5_udkey_A, ''Text1''),
     (KnownT isoiec_9798_2_5_udkey_A_text_1))
  , ((isoiec_9798_2_5_udkey_P, ''Text1''),
     (KnownT isoiec_9798_2_5_udkey_P_1))
  , ((isoiec_9798_2_5_udkey_B, ''Text2''),
     (KnownT isoiec_9798_2_5_udkey_B_3))
  , ((isoiec_9798_2_5_udkey_P, ''Text2''),
     (KnownT isoiec_9798_2_5_udkey_P_text_2))
  , ((isoiec_9798_2_5_udkey_A, ''Text3''),
     (KnownT isoiec_9798_2_5_udkey_A_2))
  , ((isoiec_9798_2_5_udkey_P, ''Text3''),
     (KnownT isoiec_9798_2_5_udkey_P_text_2))
  , ((isoiec_9798_2_5_udkey_A, ''Text4''),
     (KnownT isoiec_9798_2_5_udkey_A_2))
  , ((isoiec_9798_2_5_udkey_P, ''Text4''),
     (KnownT isoiec_9798_2_5_udkey_P_text_2))
  , ((isoiec_9798_2_5_udkey_A, ''Text5''),
     (KnownT isoiec_9798_2_5_udkey_A_text_3))
  , ((isoiec_9798_2_5_udkey_B, ''Text5''),
     (KnownT isoiec_9798_2_5_udkey_B_3))
  , ((isoiec_9798_2_5_udkey_A, ''Text6''),
     (KnownT isoiec_9798_2_5_udkey_A_text_3))
  , ((isoiec_9798_2_5_udkey_B, ''Text6''),
     (KnownT isoiec_9798_2_5_udkey_B_3))
  , ((isoiec_9798_2_5_udkey_A, ''Text7''),
     (KnownT isoiec_9798_2_5_udkey_A_4))
  , ((isoiec_9798_2_5_udkey_B, ''Text7''),
     (KnownT isoiec_9798_2_5_udkey_B_text_4))
  , ((isoiec_9798_2_5_udkey_A, ''Text8''),
     (KnownT isoiec_9798_2_5_udkey_A_4))
  , ((isoiec_9798_2_5_udkey_B, ''Text8''),
     (KnownT isoiec_9798_2_5_udkey_B_text_4))
  , ((isoiec_9798_2_5_udkey_A, ''TokenPA_for_B''),
     (KnownT isoiec_9798_2_5_udkey_A_2))
  ]"

sublocale isoiec_9798_2_5_udkey_state < isoiec_9798_2_5_udkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_2_5_udkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_2_5_udkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_2_5_udkey_A_2_Kab t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid0,
               s(MV ''Kab'' tid0), s(AV ''B'' tid0), s(MV ''Text3'' tid0)
            |}
            ( K ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_udkey_A_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid0,
               s(MV ''Kab'' tid0), s(AV ''B'' tid0), s(MV ''Text3'' tid0)
            |}
            ( K ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_udkey_A_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_A_2_TokenPA_for_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_A_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_A_text_3_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_A_4_TNb t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_4'', s(MV ''TNb'' tid0),
               s(AV ''A'' tid0), s(MV ''Text7'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_udkey_A_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_4'', s(MV ''TNb'' tid0),
               s(AV ''A'' tid0), s(MV ''Text7'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_udkey_A_4_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_B_3_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_B_3_Kab t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_2_2'', s(MV ''TNp'' tid0),
               s(MV ''Kab'' tid0), s(MV ''A'' tid0), s(MV ''Text2'' tid0)
            |}
            ( K ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_udkey_B_3_P t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_B_3_TNa t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_3'', s(MV ''TNa'' tid0),
               s(AV ''B'' tid0), s(MV ''Text5'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_udkey_B_3_TNp t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_2_2'', s(MV ''TNp'' tid0),
               s(MV ''Kab'' tid0), s(MV ''A'' tid0), s(MV ''Text2'' tid0)
            |}
            ( K ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_udkey_B_3_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_2_2'', s(MV ''TNp'' tid0),
               s(MV ''Kab'' tid0), s(MV ''A'' tid0), s(MV ''Text2'' tid0)
            |}
            ( K ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_udkey_B_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_3'', s(MV ''TNa'' tid0),
               s(AV ''B'' tid0), s(MV ''Text5'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_udkey_B_3_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_B_text_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_B_text_4_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_P_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_P_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_P_1_TVPa t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_P_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_P_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_P_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_P_text_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_2_5_udkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_2_5_udkey_state begin

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

lemma (in restricted_isoiec_9798_2_5_udkey_state) P_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_5_udkey_P"
    "RLKR(s(AV ''P'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "LN ''Kab'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''Kab'' tid0 ")
  case isoiec_9798_2_5_udkey_P_2_Kab note_unified facts = this facts
  thus ?thesis by (fastsimp dest!: ltk_secrecy)
next
  case isoiec_9798_2_5_udkey_P_2_Kab_1 note_unified facts = this facts
  thus ?thesis by (fastsimp dest!: ltk_secrecy)
qed (insert facts, fastsimp+)?

lemma (in restricted_isoiec_9798_2_5_udkey_state) A_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_5_udkey_A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(AV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_5_udkey_A_2 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid0,
                          s(MV ''Kab'' tid0), s(AV ''B'' tid0), s(MV ''Text3'' tid0)
                       |}
                       ( K ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_5_udkey_P_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp dest: P_secret_Kab intro: event_predOrdI)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_isoiec_9798_2_5_udkey_state) B_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_5_udkey_B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_5_udkey_B_3 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_5_enc_2_2'', s(MV ''TNp'' tid0),
                          s(MV ''Kab'' tid0), s(MV ''A'' tid0), s(MV ''Text2'' tid0)
                       |}
                       ( K ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_5_udkey_P_2_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp dest: P_secret_Kab intro: event_predOrdI)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_isoiec_9798_2_5_udkey_state) A_non_injective_agreement_B:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_5_udkey_A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(AV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_5_udkey_A_4 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_5_udkey_B &
        ( tid1, isoiec_9798_2_5_udkey_B_4 ) : steps t &
        {| s(MV ''A'' tid1), s(AV ''B'' tid1), s(MV ''P'' tid1),
           s(MV ''Kab'' tid1), s(MV ''TNa'' tid1), s(MV ''Text5'' tid1),
           LN ''TNb'' tid1, s(MV ''Text7'' tid1)
        |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(AV ''P'' tid0),
                s(MV ''Kab'' tid0), LN ''TNa'' tid0, s(MV ''Text5'' tid0),
                s(MV ''TNb'' tid0), s(MV ''Text7'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid0,
                          s(MV ''Kab'' tid0), s(AV ''B'' tid0), s(MV ''Text3'' tid0)
                       |}
                       ( K ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_5_udkey_P_2_enc tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''isoiec_9798_2_5_enc_4'', s(MV ''TNb'' tid0),
                            s(AV ''A'' tid0), s(MV ''Text7'' tid0)
                         |}
                         ( LN ''Kab'' tid1 ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest: P_secret_Kab intro: event_predOrdI)
    next
      case (isoiec_9798_2_5_udkey_B_4_enc tid2) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_5_enc_2_2'', s(MV ''TNp'' tid2),
                              LN ''Kab'' tid1, s(AV ''A'' tid0), s(MV ''Text2'' tid2)
                           |}
                           ( K ( s(AV ''B'' tid2) ) ( s(MV ''P'' tid2) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastsimp dest: P_secret_Kab intro: event_predOrdI)
      next
        case (isoiec_9798_2_5_udkey_P_2_enc_1 tid3) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_2_5_enc_3'', s(MV ''TNa'' tid2),
                                s(AV ''B'' tid0), s(MV ''Text5'' tid2)
                             |}
                             ( LN ''Kab'' tid1 ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastsimp dest: P_secret_Kab intro: event_predOrdI)
        next
          case (isoiec_9798_2_5_udkey_A_3_enc tid3) note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid3, LN ''Kab'' tid1,
                                  s(AV ''B'' tid0), s(MV ''Text3'' tid3)
                               |}
                               ( K ( s(AV ''A'' tid3) ) ( s(AV ''P'' tid3) ) ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastsimp dest: P_secret_Kab intro: event_predOrdI)
          next
            case (isoiec_9798_2_5_udkey_P_2_enc tid4) note_unified facts = this facts
            thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
          qed (insert facts, fastsimp+)?
        qed (insert facts, fastsimp+)?
      qed (insert facts, fastsimp+)?
    qed (insert facts, fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_isoiec_9798_2_5_udkey_state) B_non_injective_agreement_A:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_5_udkey_B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_5_udkey_B_3 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_5_udkey_A &
        ( tid1, isoiec_9798_2_5_udkey_A_3 ) : steps t &
        {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(AV ''P'' tid1),
           s(MV ''Kab'' tid1), LN ''TNa'' tid1, s(MV ''Text5'' tid1)
        |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''P'' tid0),
                s(MV ''Kab'' tid0), s(MV ''TNa'' tid0), s(MV ''Text5'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_5_enc_2_2'', s(MV ''TNp'' tid0),
                          s(MV ''Kab'' tid0), s(MV ''A'' tid0), s(MV ''Text2'' tid0)
                       |}
                       ( K ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_5_udkey_P_2_enc_1 tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''isoiec_9798_2_5_enc_3'', s(MV ''TNa'' tid0),
                            s(AV ''B'' tid0), s(MV ''Text5'' tid0)
                         |}
                         ( LN ''Kab'' tid1 ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest: P_secret_Kab intro: event_predOrdI)
    next
      case (isoiec_9798_2_5_udkey_A_3_enc tid2) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid2, LN ''Kab'' tid1,
                              s(AV ''B'' tid0), s(MV ''Text3'' tid2)
                           |}
                           ( K ( s(AV ''A'' tid2) ) ( s(AV ''P'' tid2) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastsimp dest: P_secret_Kab intro: event_predOrdI)
      next
        case (isoiec_9798_2_5_udkey_P_2_enc tid3) note_unified facts = this facts
        thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
      qed (insert facts, fastsimp+)?
    qed (insert facts, fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_isoiec_9798_2_5_udkey_state) A_non_injective_agreement_P:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_5_udkey_A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(AV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_5_udkey_A_2 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_5_udkey_P &
        ( tid1, isoiec_9798_2_5_udkey_P_2 ) : steps t &
        {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1), LN ''Kab'' tid1,
           s(MV ''TVPa'' tid1), s(MV ''Text3'' tid1)
        |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(AV ''P'' tid0),
                s(MV ''Kab'' tid0), LN ''TVPa'' tid0, s(MV ''Text3'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid0,
                          s(MV ''Kab'' tid0), s(AV ''B'' tid0), s(MV ''Text3'' tid0)
                       |}
                       ( K ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_5_udkey_P_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_isoiec_9798_2_5_udkey_state) B_non_injective_agreement_P:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_5_udkey_B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_5_udkey_B_3 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_5_udkey_P &
        ( tid1, isoiec_9798_2_5_udkey_P_2 ) : steps t &
        {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1), LN ''Kab'' tid1,
           LN ''TNp'' tid1, s(MV ''Text2'' tid1)
        |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''P'' tid0),
                s(MV ''Kab'' tid0), s(MV ''TNp'' tid0), s(MV ''Text2'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_5_enc_2_2'', s(MV ''TNp'' tid0),
                          s(MV ''Kab'' tid0), s(MV ''A'' tid0), s(MV ''Text2'' tid0)
                       |}
                       ( K ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_5_udkey_P_2_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
  qed (insert facts, fastsimp+)?
qed

role isoiec_9798_2_6_udkey_A
where "isoiec_9798_2_6_udkey_A =
  [ Recv ''1'' <| sMV ''B'', sAV ''A'', sMV ''Rb'', sMV ''Text1'' |>
  , Recv ''text_2'' ( sMV ''Text2'' )
  , Send ''2'' <| sAV ''A'', sAV ''P'', sN ''Ra'', sMV ''Rb'', sMV ''B'',
                  sMV ''Text2''
               |>
  , Recv ''3'' <| sAV ''P'', sAV ''A'', sMV ''Text5'',
                  PEnc <| sC ''isoiec_9798_2_6_enc_3_1'', sN ''Ra'', sMV ''Kab'',
                          sMV ''B'', sMV ''Text4''
                       |>
                       ( sK ''A'' ''P'' ),
                  sMV ''TokenPA_for_B''
               |>
  , Recv ''text_4'' <| sMV ''Text6'', sMV ''Text7'' |>
  , Send ''4'' <| sAV ''A'', sMV ''B'', sMV ''Text7'', sAV ''P'',
                  sMV ''TokenPA_for_B'',
                  PEnc <| sC ''isoiec_9798_2_6_enc_4'', sN ''Rpa'', sMV ''Rb'',
                          sMV ''Text6''
                       |>
                       ( sMV ''Kab'' )
               |>
  , Recv ''5'' <| sMV ''B'', sAV ''A'', sMV ''Text9'',
                  PEnc <| sC ''isoiec_9798_2_6_enc_5'', sMV ''Rb'', sN ''Rpa'',
                          sMV ''Text8''
                       |>
                       ( sMV ''Kab'' )
               |>
  ]"

role isoiec_9798_2_6_udkey_B
where "isoiec_9798_2_6_udkey_B =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''B'', sAV ''A'', sN ''Rb'', sMV ''Text1'' |>
  , Recv ''4'' <| sAV ''A'', sAV ''B'', sMV ''Text7'', sMV ''P'',
                  PEnc <| sC ''isoiec_9798_2_6_enc_3_2'', sN ''Rb'', sMV ''Kab'',
                          sAV ''A'', sMV ''Text3''
                       |>
                       ( PSymK ( sAV ''B'' ) ( sMV ''P'' ) ),
                  PEnc <| sC ''isoiec_9798_2_6_enc_4'', sMV ''Rpa'', sN ''Rb'',
                          sMV ''Text6''
                       |>
                       ( sMV ''Kab'' )
               |>
  , Recv ''text_5'' <| sMV ''Text8'', sMV ''Text9'' |>
  , Send ''5'' <| sAV ''B'', sAV ''A'', sMV ''Text9'',
                  PEnc <| sC ''isoiec_9798_2_6_enc_5'', sN ''Rb'', sMV ''Rpa'',
                          sMV ''Text8''
                       |>
                       ( sMV ''Kab'' )
               |>
  ]"

role isoiec_9798_2_6_udkey_P
where "isoiec_9798_2_6_udkey_P =
  [ Recv ''2'' <| sMV ''A'', sAV ''P'', sMV ''Ra'', sMV ''Rb'', sMV ''B'',
                  sMV ''Text2''
               |>
  , Recv ''text_3'' <| sMV ''Text3'', sMV ''Text4'', sMV ''Text5'' |>
  , Send ''3'' <| sAV ''P'', sMV ''A'', sMV ''Text5'',
                  PEnc <| sC ''isoiec_9798_2_6_enc_3_1'', sMV ''Ra'', sN ''Kab'',
                          sMV ''B'', sMV ''Text4''
                       |>
                       ( PSymK ( sMV ''A'' ) ( sAV ''P'' ) ),
                  PEnc <| sC ''isoiec_9798_2_6_enc_3_2'', sMV ''Rb'', sN ''Kab'',
                          sMV ''A'', sMV ''Text3''
                       |>
                       ( PSymK ( sMV ''B'' ) ( sAV ''P'' ) )
               |>
  ]"

protocol isoiec_9798_2_6_udkey
where "isoiec_9798_2_6_udkey =
{ isoiec_9798_2_6_udkey_A, isoiec_9798_2_6_udkey_B,
  isoiec_9798_2_6_udkey_P
}"

locale restricted_isoiec_9798_2_6_udkey_state = isoiec_9798_2_6_udkey_state

type_invariant isoiec_9798_2_6_udkey_msc_typing for isoiec_9798_2_6_udkey
where "isoiec_9798_2_6_udkey_msc_typing = mk_typing
  [ ((isoiec_9798_2_6_udkey_P, ''A''), (KnownT isoiec_9798_2_6_udkey_P_2))
  , ((isoiec_9798_2_6_udkey_A, ''B''), (KnownT isoiec_9798_2_6_udkey_A_1))
  , ((isoiec_9798_2_6_udkey_P, ''B''), (KnownT isoiec_9798_2_6_udkey_P_2))
  , ((isoiec_9798_2_6_udkey_A, ''Kab''),
     (SumT (KnownT isoiec_9798_2_6_udkey_A_3) (NonceT isoiec_9798_2_6_udkey_P ''Kab'')))
  , ((isoiec_9798_2_6_udkey_B, ''Kab''),
     (SumT (KnownT isoiec_9798_2_6_udkey_B_4) (NonceT isoiec_9798_2_6_udkey_P ''Kab'')))
  , ((isoiec_9798_2_6_udkey_B, ''P''), (KnownT isoiec_9798_2_6_udkey_B_4))
  , ((isoiec_9798_2_6_udkey_P, ''Ra''), (KnownT isoiec_9798_2_6_udkey_P_2))
  , ((isoiec_9798_2_6_udkey_A, ''Rb''), (KnownT isoiec_9798_2_6_udkey_A_1))
  , ((isoiec_9798_2_6_udkey_P, ''Rb''), (KnownT isoiec_9798_2_6_udkey_P_2))
  , ((isoiec_9798_2_6_udkey_B, ''Rpa''),
     (SumT (KnownT isoiec_9798_2_6_udkey_B_4) (NonceT isoiec_9798_2_6_udkey_A ''Rpa'')))
  , ((isoiec_9798_2_6_udkey_A, ''Text1''),
     (KnownT isoiec_9798_2_6_udkey_A_1))
  , ((isoiec_9798_2_6_udkey_B, ''Text1''),
     (KnownT isoiec_9798_2_6_udkey_B_text_1))
  , ((isoiec_9798_2_6_udkey_A, ''Text2''),
     (KnownT isoiec_9798_2_6_udkey_A_text_2))
  , ((isoiec_9798_2_6_udkey_P, ''Text2''),
     (KnownT isoiec_9798_2_6_udkey_P_2))
  , ((isoiec_9798_2_6_udkey_B, ''Text3''),
     (KnownT isoiec_9798_2_6_udkey_B_4))
  , ((isoiec_9798_2_6_udkey_P, ''Text3''),
     (KnownT isoiec_9798_2_6_udkey_P_text_3))
  , ((isoiec_9798_2_6_udkey_A, ''Text4''),
     (KnownT isoiec_9798_2_6_udkey_A_3))
  , ((isoiec_9798_2_6_udkey_P, ''Text4''),
     (KnownT isoiec_9798_2_6_udkey_P_text_3))
  , ((isoiec_9798_2_6_udkey_A, ''Text5''),
     (KnownT isoiec_9798_2_6_udkey_A_3))
  , ((isoiec_9798_2_6_udkey_P, ''Text5''),
     (KnownT isoiec_9798_2_6_udkey_P_text_3))
  , ((isoiec_9798_2_6_udkey_A, ''Text6''),
     (KnownT isoiec_9798_2_6_udkey_A_text_4))
  , ((isoiec_9798_2_6_udkey_B, ''Text6''),
     (KnownT isoiec_9798_2_6_udkey_B_4))
  , ((isoiec_9798_2_6_udkey_A, ''Text7''),
     (KnownT isoiec_9798_2_6_udkey_A_text_4))
  , ((isoiec_9798_2_6_udkey_B, ''Text7''),
     (KnownT isoiec_9798_2_6_udkey_B_4))
  , ((isoiec_9798_2_6_udkey_A, ''Text8''),
     (KnownT isoiec_9798_2_6_udkey_A_5))
  , ((isoiec_9798_2_6_udkey_B, ''Text8''),
     (KnownT isoiec_9798_2_6_udkey_B_text_5))
  , ((isoiec_9798_2_6_udkey_A, ''Text9''),
     (KnownT isoiec_9798_2_6_udkey_A_5))
  , ((isoiec_9798_2_6_udkey_B, ''Text9''),
     (KnownT isoiec_9798_2_6_udkey_B_text_5))
  , ((isoiec_9798_2_6_udkey_A, ''TokenPA_for_B''),
     (KnownT isoiec_9798_2_6_udkey_A_3))
  ]"

sublocale isoiec_9798_2_6_udkey_state < isoiec_9798_2_6_udkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_2_6_udkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_2_6_udkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_2_6_udkey_A_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_A_1_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_A_3_Kab t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid0,
               s(MV ''Kab'' tid0), s(MV ''B'' tid0), s(MV ''Text4'' tid0)
            |}
            ( K ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_udkey_A_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid0,
               s(MV ''Kab'' tid0), s(MV ''B'' tid0), s(MV ''Text4'' tid0)
            |}
            ( K ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_udkey_A_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_A_3_TokenPA_for_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_A_text_4_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_A_text_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_A_5_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_5'', s(MV ''Rb'' tid0), LN ''Rpa'' tid0,
               s(MV ''Text8'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_udkey_A_5_Text9 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_B_4_Kab t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid0,
               s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''Text3'' tid0)
            |}
            ( K ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_udkey_B_4_P t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_B_4_Rpa t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_4'', s(MV ''Rpa'' tid0), LN ''Rb'' tid0,
               s(MV ''Text6'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_udkey_B_4_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid0,
               s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''Text3'' tid0)
            |}
            ( K ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_udkey_B_4_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_4'', s(MV ''Rpa'' tid0), LN ''Rb'' tid0,
               s(MV ''Text6'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_udkey_B_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_B_text_5_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_B_text_5_Text9 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_P_2_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_P_2_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_P_2_Ra t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_P_2_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_P_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_P_text_3_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_P_text_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_P_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_2_6_udkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_2_6_udkey_state begin

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

lemma (in restricted_isoiec_9798_2_6_udkey_state) P_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_6_udkey_P"
    "RLKR(s(AV ''P'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "LN ''Kab'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''Kab'' tid0 ")
  case isoiec_9798_2_6_udkey_P_3_Kab note_unified facts = this facts
  thus ?thesis by (fastsimp dest!: ltk_secrecy)
next
  case isoiec_9798_2_6_udkey_P_3_Kab_1 note_unified facts = this facts
  thus ?thesis by (fastsimp dest!: ltk_secrecy)
qed (insert facts, fastsimp+)?

lemma (in restricted_isoiec_9798_2_6_udkey_state) A_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_6_udkey_A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''P'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_6_udkey_A_3 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid0,
                          s(MV ''Kab'' tid0), s(MV ''B'' tid0), s(MV ''Text4'' tid0)
                       |}
                       ( K ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_6_udkey_P_3_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp dest: P_secret_Kab intro: event_predOrdI)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_isoiec_9798_2_6_udkey_state) B_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_6_udkey_B"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_6_udkey_B_4 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid0,
                          s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''Text3'' tid0)
                       |}
                       ( K ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_6_udkey_P_3_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp dest: P_secret_Kab intro: event_predOrdI)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_isoiec_9798_2_6_udkey_state) A_non_injective_agreement_B:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_6_udkey_A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''P'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_6_udkey_A_5 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_6_udkey_B &
        ( tid1, isoiec_9798_2_6_udkey_B_5 ) : steps t &
        {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(MV ''P'' tid1),
           s(MV ''Kab'' tid1), s(MV ''Rpa'' tid1), LN ''Rb'' tid1,
           s(MV ''Text6'' tid1), s(MV ''Text8'' tid1)
        |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), s(AV ''P'' tid0),
                s(MV ''Kab'' tid0), LN ''Rpa'' tid0, s(MV ''Rb'' tid0),
                s(MV ''Text6'' tid0), s(MV ''Text8'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid0,
                          s(MV ''Kab'' tid0), s(MV ''B'' tid0), s(MV ''Text4'' tid0)
                       |}
                       ( K ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_6_udkey_P_3_enc tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''isoiec_9798_2_6_enc_5'', s(MV ''Rb'' tid0), LN ''Rpa'' tid0,
                            s(MV ''Text8'' tid0)
                         |}
                         ( LN ''Kab'' tid1 ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest: P_secret_Kab intro: event_predOrdI)
    next
      case (isoiec_9798_2_6_udkey_B_5_enc tid2) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid2, LN ''Kab'' tid1,
                              s(AV ''A'' tid2), s(MV ''Text3'' tid2)
                           |}
                           ( K ( s(AV ''B'' tid2) ) ( s(MV ''P'' tid2) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastsimp dest: P_secret_Kab intro: event_predOrdI)
      next
        case (isoiec_9798_2_6_udkey_P_3_enc_1 tid3) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_2_6_enc_4'', LN ''Rpa'' tid0, LN ''Rb'' tid2,
                                s(MV ''Text6'' tid2)
                             |}
                             ( LN ''Kab'' tid1 ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastsimp dest: P_secret_Kab intro: event_predOrdI)
        next
          case (isoiec_9798_2_6_udkey_A_4_enc tid3) note_unified facts = this facts
          thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
        qed (insert facts, fastsimp+)?
      qed (insert facts, fastsimp+)?
    qed (insert facts, fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_isoiec_9798_2_6_udkey_state) B_non_injective_agreement_A:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_6_udkey_B"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_6_udkey_B_4 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_6_udkey_A &
        ( tid1, isoiec_9798_2_6_udkey_A_4 ) : steps t &
        {| s(AV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1),
           s(MV ''Kab'' tid1), LN ''Rpa'' tid1, s(MV ''Rb'' tid1),
           s(MV ''Text6'' tid1)
        |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''P'' tid0),
                s(MV ''Kab'' tid0), s(MV ''Rpa'' tid0), LN ''Rb'' tid0,
                s(MV ''Text6'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid0,
                          s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''Text3'' tid0)
                       |}
                       ( K ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_6_udkey_P_3_enc_1 tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''isoiec_9798_2_6_enc_4'', s(MV ''Rpa'' tid0), LN ''Rb'' tid0,
                            s(MV ''Text6'' tid0)
                         |}
                         ( LN ''Kab'' tid1 ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest: P_secret_Kab intro: event_predOrdI)
    next
      case (isoiec_9798_2_6_udkey_A_4_enc tid2) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid2, LN ''Kab'' tid1,
                              s(MV ''B'' tid2), s(MV ''Text4'' tid2)
                           |}
                           ( K ( s(AV ''A'' tid2) ) ( s(AV ''P'' tid2) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastsimp dest: P_secret_Kab intro: event_predOrdI)
      next
        case (isoiec_9798_2_6_udkey_P_3_enc tid3) note_unified facts = this facts
        thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
      qed (insert facts, fastsimp+)?
    qed (insert facts, fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_isoiec_9798_2_6_udkey_state) A_non_injective_agreement_P:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_6_udkey_A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''P'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_6_udkey_A_3 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_6_udkey_P &
        ( tid1, isoiec_9798_2_6_udkey_P_3 ) : steps t &
        {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1),
           s(MV ''Ra'' tid1), LN ''Kab'' tid1, s(MV ''Text4'' tid1)
        |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), s(AV ''P'' tid0),
                LN ''Ra'' tid0, s(MV ''Kab'' tid0), s(MV ''Text4'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid0,
                          s(MV ''Kab'' tid0), s(MV ''B'' tid0), s(MV ''Text4'' tid0)
                       |}
                       ( K ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_6_udkey_P_3_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_isoiec_9798_2_6_udkey_state) B_non_injective_agreement_P:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_6_udkey_B"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_6_udkey_B_4 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_6_udkey_P &
        ( tid1, isoiec_9798_2_6_udkey_P_3 ) : steps t &
        {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1),
           s(MV ''Rb'' tid1), LN ''Kab'' tid1, s(MV ''Text3'' tid1)
        |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''P'' tid0),
                LN ''Rb'' tid0, s(MV ''Kab'' tid0), s(MV ''Text3'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid0,
                          s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''Text3'' tid0)
                       |}
                       ( K ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_6_udkey_P_3_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
  qed (insert facts, fastsimp+)?
qed

end