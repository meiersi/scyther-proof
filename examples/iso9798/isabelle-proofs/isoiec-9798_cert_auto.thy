theory "isoiec-9798_cert_auto"
imports
  "ESPLogic"
begin

role isoiec_9798_2_1_bdkey_A
where "isoiec_9798_2_1_bdkey_A =
  [ Send ''leak_A'' ( sN ''TNA'' )
  , Recv ''text_1'' <| sMV ''Text1'', sMV ''Text2'' |>
  , Send ''1'' <| sAV ''A'', sAV ''B'', sMV ''Text2'',
                  PEnc <| sC ''isoiec_9798_2_1_enc_1'', sN ''TNA'', sAV ''B'',
                          sMV ''Text1''
                       |>
                       ( sKbd (AVar ''A'') (AVar ''B'') )
               |>
  ]"

role isoiec_9798_2_1_bdkey_B
where "isoiec_9798_2_1_bdkey_B =
  [ Recv ''1'' <| sMV ''A'', sAV ''B'', sMV ''Text2'',
                  PEnc <| sC ''isoiec_9798_2_1_enc_1'', sMV ''TNA'', sAV ''B'',
                          sMV ''Text1''
                       |>
                       ( sKbd (MVar ''A'') (AVar ''B'') )
               |>
  ]"

protocol isoiec_9798_2_1_bdkey
where "isoiec_9798_2_1_bdkey =
{ isoiec_9798_2_1_bdkey_A, isoiec_9798_2_1_bdkey_B }"

locale restricted_isoiec_9798_2_1_bdkey_state = isoiec_9798_2_1_bdkey_state

type_invariant isoiec_9798_2_1_bdkey_msc_typing for isoiec_9798_2_1_bdkey
where "isoiec_9798_2_1_bdkey_msc_typing = mk_typing
  [ ((isoiec_9798_2_1_bdkey_B, ''A''), (KnownT isoiec_9798_2_1_bdkey_B_1))
  , ((isoiec_9798_2_1_bdkey_B, ''TNA''),
     (SumT (KnownT isoiec_9798_2_1_bdkey_B_1) (NonceT isoiec_9798_2_1_bdkey_A ''TNA'')))
  , ((isoiec_9798_2_1_bdkey_A, ''Text1''),
     (KnownT isoiec_9798_2_1_bdkey_A_text_1))
  , ((isoiec_9798_2_1_bdkey_B, ''Text1''),
     (KnownT isoiec_9798_2_1_bdkey_B_1))
  , ((isoiec_9798_2_1_bdkey_A, ''Text2''),
     (KnownT isoiec_9798_2_1_bdkey_A_text_1))
  , ((isoiec_9798_2_1_bdkey_B, ''Text2''),
     (KnownT isoiec_9798_2_1_bdkey_B_1))
  ]"

sublocale isoiec_9798_2_1_bdkey_state < isoiec_9798_2_1_bdkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_2_1_bdkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_2_1_bdkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_2_1_bdkey_A_text_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_1_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_1_bdkey_A_text_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_1_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_1_bdkey_B_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_1_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_1_bdkey_B_1_TNA t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_1_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_1_enc_1'', s(MV ''TNA'' tid0),
               s(AV ''B'' tid0), s(MV ''Text1'' tid0)
            |}
            ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_1_bdkey_B_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_1_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_1_enc_1'', s(MV ''TNA'' tid0),
               s(AV ''B'' tid0), s(MV ''Text1'' tid0)
            |}
            ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_1_bdkey_B_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_1_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_2_1_bdkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_2_1_bdkey_state begin

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

lemma (in restricted_isoiec_9798_2_1_bdkey_state) B_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_1_bdkey_B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_1_bdkey_B_1 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_1_bdkey_A &
        ( tid1, isoiec_9798_2_1_bdkey_A_1 ) : steps t &
        {| s(AV ''A'' tid1), s(AV ''B'' tid1), LN ''TNA'' tid1,
           s(MV ''Text1'' tid1)
        |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''TNA'' tid0),
                s(MV ''Text1'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_1_enc_1'', s(MV ''TNA'' tid0),
                          s(AV ''B'' tid0), s(MV ''Text1'' tid0)
                       |}
                       ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_1_bdkey_A_1_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (insert facts, fastforce+)?
qed

role isoiec_9798_2_2_bdkey_A
where "isoiec_9798_2_2_bdkey_A =
  [ Recv ''1'' <| sMV ''B'', sAV ''A'', sMV ''RB'', sMV ''Text1'' |>
  , Recv ''text_2'' <| sMV ''Text2'', sMV ''Text3'' |>
  , Send ''2'' <| sAV ''A'', sMV ''B'', sMV ''Text3'',
                  PEnc <| sC ''isoiec_9798_2_2_enc_2'', sMV ''RB'', sMV ''B'',
                          sMV ''Text2''
                       |>
                       ( sKbd (MVar ''B'') (AVar ''A'') )
               |>
  ]"

role isoiec_9798_2_2_bdkey_B
where "isoiec_9798_2_2_bdkey_B =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''B'', sAV ''A'', sN ''RB'', sMV ''Text1'' |>
  , Recv ''2'' <| sAV ''A'', sAV ''B'', sMV ''Text3'',
                  PEnc <| sC ''isoiec_9798_2_2_enc_2'', sN ''RB'', sAV ''B'', sMV ''Text2''
                       |>
                       ( sKbd (AVar ''B'') (AVar ''A'') )
               |>
  ]"

protocol isoiec_9798_2_2_bdkey
where "isoiec_9798_2_2_bdkey =
{ isoiec_9798_2_2_bdkey_A, isoiec_9798_2_2_bdkey_B }"

locale restricted_isoiec_9798_2_2_bdkey_state = isoiec_9798_2_2_bdkey_state

type_invariant isoiec_9798_2_2_bdkey_msc_typing for isoiec_9798_2_2_bdkey
where "isoiec_9798_2_2_bdkey_msc_typing = mk_typing
  [ ((isoiec_9798_2_2_bdkey_A, ''B''), (KnownT isoiec_9798_2_2_bdkey_A_1))
  , ((isoiec_9798_2_2_bdkey_A, ''RB''), (KnownT isoiec_9798_2_2_bdkey_A_1))
  , ((isoiec_9798_2_2_bdkey_A, ''Text1''),
     (KnownT isoiec_9798_2_2_bdkey_A_1))
  , ((isoiec_9798_2_2_bdkey_B, ''Text1''),
     (KnownT isoiec_9798_2_2_bdkey_B_text_1))
  , ((isoiec_9798_2_2_bdkey_A, ''Text2''),
     (KnownT isoiec_9798_2_2_bdkey_A_text_2))
  , ((isoiec_9798_2_2_bdkey_B, ''Text2''),
     (KnownT isoiec_9798_2_2_bdkey_B_2))
  , ((isoiec_9798_2_2_bdkey_A, ''Text3''),
     (KnownT isoiec_9798_2_2_bdkey_A_text_2))
  , ((isoiec_9798_2_2_bdkey_B, ''Text3''),
     (KnownT isoiec_9798_2_2_bdkey_B_2))
  ]"

sublocale isoiec_9798_2_2_bdkey_state < isoiec_9798_2_2_bdkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_2_2_bdkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_2_2_bdkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_2_2_bdkey_A_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_2_bdkey_A_1_RB t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_2_bdkey_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_2_bdkey_A_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_2_bdkey_A_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_2_bdkey_B_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_2_enc_2'', LN ''RB'' tid0, s(AV ''B'' tid0),
               s(MV ''Text2'' tid0)
            |}
            ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_2_bdkey_B_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_2_2_bdkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_2_2_bdkey_state begin

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

lemma (in restricted_isoiec_9798_2_2_bdkey_state) B_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_2_bdkey_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_2_bdkey_B_2 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_2_bdkey_A &
          ( tid1, isoiec_9798_2_2_bdkey_A_2 ) : steps t &
          {| s(AV ''A'' tid1), s(MV ''B'' tid1), s(MV ''RB'' tid1),
             s(MV ''Text2'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), LN ''RB'' tid0,
                  s(MV ''Text2'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_2_enc_2'', LN ''RB'' tid0, s(AV ''B'' tid0),
                              s(MV ''Text2'' tid0)
                           |}
                           ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_2_bdkey_A_2_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

role isoiec_9798_2_3_bdkey_A
where "isoiec_9798_2_3_bdkey_A =
  [ Send ''leak_A'' ( sN ''TNA'' )
  , Recv ''text_1'' <| sMV ''Text1'', sMV ''Text2'' |>
  , Send ''1'' <| sAV ''A'', sAV ''B'', sMV ''Text2'',
                  PEnc <| sC ''isoiec_9798_2_3_enc_1'', sN ''TNA'', sAV ''B'',
                          sMV ''Text1''
                       |>
                       ( sKbd (AVar ''A'') (AVar ''B'') )
               |>
  , Recv ''2'' <| sAV ''B'', sAV ''A'', sMV ''Text4'',
                  PEnc <| sC ''isoiec_9798_2_3_enc_2'', sMV ''TNB'', sAV ''A'',
                          sMV ''Text3''
                       |>
                       ( sKbd (AVar ''B'') (AVar ''A'') )
               |>
  ]"

role isoiec_9798_2_3_bdkey_B
where "isoiec_9798_2_3_bdkey_B =
  [ Send ''leak_B'' ( sN ''TNB'' )
  , Recv ''1'' <| sMV ''A'', sAV ''B'', sMV ''Text2'',
                  PEnc <| sC ''isoiec_9798_2_3_enc_1'', sMV ''TNA'', sAV ''B'',
                          sMV ''Text1''
                       |>
                       ( sKbd (MVar ''A'') (AVar ''B'') )
               |>
  , Recv ''text_2'' <| sMV ''Text3'', sMV ''Text4'' |>
  , Send ''2'' <| sAV ''B'', sMV ''A'', sMV ''Text4'',
                  PEnc <| sC ''isoiec_9798_2_3_enc_2'', sN ''TNB'', sMV ''A'',
                          sMV ''Text3''
                       |>
                       ( sKbd (AVar ''B'') (MVar ''A'') )
               |>
  ]"

protocol isoiec_9798_2_3_bdkey
where "isoiec_9798_2_3_bdkey =
{ isoiec_9798_2_3_bdkey_A, isoiec_9798_2_3_bdkey_B }"

locale restricted_isoiec_9798_2_3_bdkey_state = isoiec_9798_2_3_bdkey_state

type_invariant isoiec_9798_2_3_bdkey_msc_typing for isoiec_9798_2_3_bdkey
where "isoiec_9798_2_3_bdkey_msc_typing = mk_typing
  [ ((isoiec_9798_2_3_bdkey_B, ''A''), (KnownT isoiec_9798_2_3_bdkey_B_1))
  , ((isoiec_9798_2_3_bdkey_B, ''TNA''),
     (SumT (KnownT isoiec_9798_2_3_bdkey_B_1) (NonceT isoiec_9798_2_3_bdkey_A ''TNA'')))
  , ((isoiec_9798_2_3_bdkey_A, ''TNB''),
     (SumT (KnownT isoiec_9798_2_3_bdkey_A_2) (NonceT isoiec_9798_2_3_bdkey_B ''TNB'')))
  , ((isoiec_9798_2_3_bdkey_A, ''Text1''),
     (KnownT isoiec_9798_2_3_bdkey_A_text_1))
  , ((isoiec_9798_2_3_bdkey_B, ''Text1''),
     (KnownT isoiec_9798_2_3_bdkey_B_1))
  , ((isoiec_9798_2_3_bdkey_A, ''Text2''),
     (KnownT isoiec_9798_2_3_bdkey_A_text_1))
  , ((isoiec_9798_2_3_bdkey_B, ''Text2''),
     (KnownT isoiec_9798_2_3_bdkey_B_1))
  , ((isoiec_9798_2_3_bdkey_A, ''Text3''),
     (KnownT isoiec_9798_2_3_bdkey_A_2))
  , ((isoiec_9798_2_3_bdkey_B, ''Text3''),
     (KnownT isoiec_9798_2_3_bdkey_B_text_2))
  , ((isoiec_9798_2_3_bdkey_A, ''Text4''),
     (KnownT isoiec_9798_2_3_bdkey_A_2))
  , ((isoiec_9798_2_3_bdkey_B, ''Text4''),
     (KnownT isoiec_9798_2_3_bdkey_B_text_2))
  ]"

sublocale isoiec_9798_2_3_bdkey_state < isoiec_9798_2_3_bdkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_2_3_bdkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_2_3_bdkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_2_3_bdkey_A_text_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_3_bdkey_A_text_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_3_bdkey_A_2_TNB t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_3_enc_2'', s(MV ''TNB'' tid0),
               s(AV ''A'' tid0), s(MV ''Text3'' tid0)
            |}
            ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_3_bdkey_A_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_3_enc_2'', s(MV ''TNB'' tid0),
               s(AV ''A'' tid0), s(MV ''Text3'' tid0)
            |}
            ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_3_bdkey_A_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_3_bdkey_B_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_3_bdkey_B_1_TNA t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_3_enc_1'', s(MV ''TNA'' tid0),
               s(AV ''B'' tid0), s(MV ''Text1'' tid0)
            |}
            ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_3_bdkey_B_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_3_enc_1'', s(MV ''TNA'' tid0),
               s(AV ''B'' tid0), s(MV ''Text1'' tid0)
            |}
            ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_3_bdkey_B_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_3_bdkey_B_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_3_bdkey_B_text_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_2_3_bdkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_2_3_bdkey_state begin

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

lemma (in restricted_isoiec_9798_2_3_bdkey_state) A_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_3_bdkey_A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_3_bdkey_A_2 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_3_bdkey_B &
        ( tid1, isoiec_9798_2_3_bdkey_B_2 ) : steps t &
        {| s(MV ''A'' tid1), s(AV ''B'' tid1), LN ''TNB'' tid1,
           s(MV ''Text3'' tid1)
        |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''TNB'' tid0),
                s(MV ''Text3'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_3_enc_2'', s(MV ''TNB'' tid0),
                          s(AV ''A'' tid0), s(MV ''Text3'' tid0)
                       |}
                       ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_3_bdkey_B_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_isoiec_9798_2_3_bdkey_state) B_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_3_bdkey_B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_3_bdkey_B_1 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_3_bdkey_A &
        ( tid1, isoiec_9798_2_3_bdkey_A_1 ) : steps t &
        {| s(AV ''A'' tid1), s(AV ''B'' tid1), LN ''TNA'' tid1,
           s(MV ''Text1'' tid1)
        |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''TNA'' tid0),
                s(MV ''Text1'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_3_enc_1'', s(MV ''TNA'' tid0),
                          s(AV ''B'' tid0), s(MV ''Text1'' tid0)
                       |}
                       ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''A'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_3_bdkey_A_1_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (insert facts, fastforce+)?
qed

role isoiec_9798_2_4_bdkey_A
where "isoiec_9798_2_4_bdkey_A =
  [ Recv ''1'' <| sMV ''B'', sAV ''A'', sMV ''RB'', sMV ''Text1'' |>
  , Recv ''text_2'' <| sMV ''Text2'', sMV ''Text3'' |>
  , Send ''2'' <| sAV ''A'', sMV ''B'', sMV ''Text3'',
                  PEnc <| sC ''isoiec_9798_2_4_enc_1'', sN ''RA'', sMV ''RB'', sMV ''B'',
                          sMV ''Text2''
                       |>
                       ( sKbd (AVar ''A'') (MVar ''B'') )
               |>
  , Recv ''3'' <| sMV ''B'', sAV ''A'', sMV ''Text5'',
                  PEnc <| sC ''isoiec_9798_2_4_enc_2'', sMV ''RB'', sN ''RA'',
                          sMV ''Text4''
                       |>
                       ( sKbd (AVar ''A'') (MVar ''B'') )
               |>
  ]"

role isoiec_9798_2_4_bdkey_B
where "isoiec_9798_2_4_bdkey_B =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''B'', sAV ''A'', sN ''RB'', sMV ''Text1'' |>
  , Recv ''2'' <| sAV ''A'', sAV ''B'', sMV ''Text3'',
                  PEnc <| sC ''isoiec_9798_2_4_enc_1'', sMV ''RA'', sN ''RB'', sAV ''B'',
                          sMV ''Text2''
                       |>
                       ( sKbd (AVar ''A'') (AVar ''B'') )
               |>
  , Recv ''text_3'' <| sMV ''Text4'', sMV ''Text5'' |>
  , Send ''3'' <| sAV ''B'', sAV ''A'', sMV ''Text5'',
                  PEnc <| sC ''isoiec_9798_2_4_enc_2'', sN ''RB'', sMV ''RA'',
                          sMV ''Text4''
                       |>
                       ( sKbd (AVar ''A'') (AVar ''B'') )
               |>
  ]"

protocol isoiec_9798_2_4_bdkey
where "isoiec_9798_2_4_bdkey =
{ isoiec_9798_2_4_bdkey_A, isoiec_9798_2_4_bdkey_B }"

locale restricted_isoiec_9798_2_4_bdkey_state = isoiec_9798_2_4_bdkey_state

type_invariant isoiec_9798_2_4_bdkey_msc_typing for isoiec_9798_2_4_bdkey
where "isoiec_9798_2_4_bdkey_msc_typing = mk_typing
  [ ((isoiec_9798_2_4_bdkey_A, ''B''), (KnownT isoiec_9798_2_4_bdkey_A_1))
  , ((isoiec_9798_2_4_bdkey_B, ''RA''),
     (SumT (KnownT isoiec_9798_2_4_bdkey_B_2) (NonceT isoiec_9798_2_4_bdkey_A ''RA'')))
  , ((isoiec_9798_2_4_bdkey_A, ''RB''), (KnownT isoiec_9798_2_4_bdkey_A_1))
  , ((isoiec_9798_2_4_bdkey_A, ''Text1''),
     (KnownT isoiec_9798_2_4_bdkey_A_1))
  , ((isoiec_9798_2_4_bdkey_B, ''Text1''),
     (KnownT isoiec_9798_2_4_bdkey_B_text_1))
  , ((isoiec_9798_2_4_bdkey_A, ''Text2''),
     (KnownT isoiec_9798_2_4_bdkey_A_text_2))
  , ((isoiec_9798_2_4_bdkey_B, ''Text2''),
     (KnownT isoiec_9798_2_4_bdkey_B_2))
  , ((isoiec_9798_2_4_bdkey_A, ''Text3''),
     (KnownT isoiec_9798_2_4_bdkey_A_text_2))
  , ((isoiec_9798_2_4_bdkey_B, ''Text3''),
     (KnownT isoiec_9798_2_4_bdkey_B_2))
  , ((isoiec_9798_2_4_bdkey_A, ''Text4''),
     (KnownT isoiec_9798_2_4_bdkey_A_3))
  , ((isoiec_9798_2_4_bdkey_B, ''Text4''),
     (KnownT isoiec_9798_2_4_bdkey_B_text_3))
  , ((isoiec_9798_2_4_bdkey_A, ''Text5''),
     (KnownT isoiec_9798_2_4_bdkey_A_3))
  , ((isoiec_9798_2_4_bdkey_B, ''Text5''),
     (KnownT isoiec_9798_2_4_bdkey_B_text_3))
  ]"

sublocale isoiec_9798_2_4_bdkey_state < isoiec_9798_2_4_bdkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_2_4_bdkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_2_4_bdkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_2_4_bdkey_A_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_bdkey_A_1_RB t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_bdkey_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_bdkey_A_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_bdkey_A_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_bdkey_A_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_4_enc_2'', s(MV ''RB'' tid0), LN ''RA'' tid0,
               s(MV ''Text4'' tid0)
            |}
            ( Kbd ( s(AV ''A'' tid0) ) ( s(MV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_4_bdkey_A_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_bdkey_B_2_RA t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_4_enc_1'', s(MV ''RA'' tid0), LN ''RB'' tid0,
               s(AV ''B'' tid0), s(MV ''Text2'' tid0)
            |}
            ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_4_bdkey_B_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_4_enc_1'', s(MV ''RA'' tid0), LN ''RB'' tid0,
               s(AV ''B'' tid0), s(MV ''Text2'' tid0)
            |}
            ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_4_bdkey_B_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_bdkey_B_text_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_bdkey_B_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_2_4_bdkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_2_4_bdkey_state begin

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

lemma (in restricted_isoiec_9798_2_4_bdkey_state) A_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_4_bdkey_A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(MV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_4_bdkey_A_3 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_4_bdkey_B &
          ( tid1, isoiec_9798_2_4_bdkey_B_3 ) : steps t &
          {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(MV ''RA'' tid1), LN ''RB'' tid1,
             s(MV ''Text2'' tid1), s(MV ''Text4'' tid1)
          |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), LN ''RA'' tid0,
                  s(MV ''RB'' tid0), s(MV ''Text2'' tid0), s(MV ''Text4'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_4_enc_2'', s(MV ''RB'' tid0), LN ''RA'' tid0,
                              s(MV ''Text4'' tid0)
                           |}
                           ( Kbd ( s(AV ''A'' tid0) ) ( s(MV ''B'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_4_bdkey_B_3_enc tid1) note_unified facts = this facts
        hence "Kbd ( s(AV ''A'' tid1) )
                   ( s(AV ''B'' tid1) ) = Kbd ( s(AV ''A'' tid0) ) ( s(MV ''B'' tid0) )"
          by simp note facts = this facts
        thus ?thesis proof(cases rule: Kbd_cases)
          case noswap note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''isoiec_9798_2_4_enc_1'', LN ''RA'' tid0, LN ''RB'' tid1,
                                  s(AV ''B'' tid1), s(MV ''Text2'' tid1)
                               |}
                               ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid1) ) ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest!: ltk_secrecy)
          next
            case (isoiec_9798_2_4_bdkey_A_2_enc tid2) note_unified facts = this facts
            thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
          qed (insert facts, fastforce+)?
        next
          case swapped note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''isoiec_9798_2_4_enc_1'', LN ''RA'' tid0, LN ''RB'' tid1,
                                  s(AV ''A'' tid0), s(MV ''Text2'' tid1)
                               |}
                               ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''A'' tid1) ) ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest!: ltk_secrecy)
          next
            case (isoiec_9798_2_4_bdkey_A_2_enc tid2) note_unified facts = this facts
            thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
          qed (insert facts, fastforce+)?
        qed (fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_2_4_bdkey_state) B_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_4_bdkey_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_4_bdkey_B_2 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_4_bdkey_A &
          ( tid1, isoiec_9798_2_4_bdkey_A_2 ) : steps t &
          {| s(AV ''A'' tid1), s(MV ''B'' tid1), LN ''RA'' tid1, s(MV ''RB'' tid1),
             s(MV ''Text2'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''RA'' tid0),
                  LN ''RB'' tid0, s(MV ''Text2'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_4_enc_1'', s(MV ''RA'' tid0), LN ''RB'' tid0,
                              s(AV ''B'' tid0), s(MV ''Text2'' tid0)
                           |}
                           ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_4_bdkey_A_2_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

role isoiec_9798_2_5_bdkey_A
where "isoiec_9798_2_5_bdkey_A =
  [ Send ''leak_A'' <| sN ''TVPa'', sN ''TNa'' |>
  , Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''A'', sAV ''P'', sN ''TVPa'', sAV ''B'',
                  sMV ''Text1''
               |>
  , Recv ''2'' <| sAV ''P'', sAV ''A'', sMV ''Text4'',
                  PEnc <| sC ''isoiec_9798_2_5_enc_2_1'', sN ''TVPa'', sMV ''Kab'',
                          sAV ''A'', sAV ''B'', sMV ''Text3''
                       |>
                       ( sKbd (AVar ''A'') (AVar ''P'') ),
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

role isoiec_9798_2_5_bdkey_B
where "isoiec_9798_2_5_bdkey_B =
  [ Send ''leak_B'' ( sN ''TNb'' )
  , Recv ''3'' <| sMV ''A'', sAV ''B'', sMV ''Text6'', sMV ''P'',
                  PEnc <| sC ''isoiec_9798_2_5_enc_2_2'', sMV ''TNp'', sMV ''Kab'',
                          sMV ''A'', sAV ''B'', sMV ''Text2''
                       |>
                       ( sKbd (AVar ''B'') (MVar ''P'') ),
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

role isoiec_9798_2_5_bdkey_P
where "isoiec_9798_2_5_bdkey_P =
  [ Send ''leak_P'' ( sN ''TNp'' )
  , Recv ''1'' <| sMV ''A'', sAV ''P'', sMV ''TVPa'', sMV ''B'',
                  sMV ''Text1''
               |>
  , Recv ''text_2'' <| sMV ''Text2'', sMV ''Text3'', sMV ''Text4'' |>
  , Send ''2'' <| sAV ''P'', sMV ''A'', sMV ''Text4'',
                  PEnc <| sC ''isoiec_9798_2_5_enc_2_1'', sMV ''TVPa'', sN ''Kab'',
                          sMV ''A'', sMV ''B'', sMV ''Text3''
                       |>
                       ( sKbd (MVar ''A'') (AVar ''P'') ),
                  PEnc <| sC ''isoiec_9798_2_5_enc_2_2'', sN ''TNp'', sN ''Kab'',
                          sMV ''A'', sMV ''B'', sMV ''Text2''
                       |>
                       ( sKbd (MVar ''B'') (AVar ''P'') )
               |>
  ]"

protocol isoiec_9798_2_5_bdkey
where "isoiec_9798_2_5_bdkey =
{ isoiec_9798_2_5_bdkey_A, isoiec_9798_2_5_bdkey_B,
  isoiec_9798_2_5_bdkey_P
}"

locale restricted_isoiec_9798_2_5_bdkey_state = isoiec_9798_2_5_bdkey_state

type_invariant isoiec_9798_2_5_bdkey_msc_typing for isoiec_9798_2_5_bdkey
where "isoiec_9798_2_5_bdkey_msc_typing = mk_typing
  [ ((isoiec_9798_2_5_bdkey_B, ''A''), (KnownT isoiec_9798_2_5_bdkey_B_3))
  , ((isoiec_9798_2_5_bdkey_P, ''A''), (KnownT isoiec_9798_2_5_bdkey_P_1))
  , ((isoiec_9798_2_5_bdkey_P, ''B''), (KnownT isoiec_9798_2_5_bdkey_P_1))
  , ((isoiec_9798_2_5_bdkey_A, ''Kab''),
     (SumT (KnownT isoiec_9798_2_5_bdkey_A_2) (NonceT isoiec_9798_2_5_bdkey_P ''Kab'')))
  , ((isoiec_9798_2_5_bdkey_B, ''Kab''),
     (SumT (KnownT isoiec_9798_2_5_bdkey_B_3) (NonceT isoiec_9798_2_5_bdkey_P ''Kab'')))
  , ((isoiec_9798_2_5_bdkey_B, ''P''), (KnownT isoiec_9798_2_5_bdkey_B_3))
  , ((isoiec_9798_2_5_bdkey_B, ''TNa''),
     (SumT (KnownT isoiec_9798_2_5_bdkey_B_3) (NonceT isoiec_9798_2_5_bdkey_A ''TNa'')))
  , ((isoiec_9798_2_5_bdkey_A, ''TNb''),
     (SumT (KnownT isoiec_9798_2_5_bdkey_A_4) (NonceT isoiec_9798_2_5_bdkey_B ''TNb'')))
  , ((isoiec_9798_2_5_bdkey_B, ''TNp''),
     (SumT (KnownT isoiec_9798_2_5_bdkey_B_3) (NonceT isoiec_9798_2_5_bdkey_P ''TNp'')))
  , ((isoiec_9798_2_5_bdkey_P, ''TVPa''),
     (KnownT isoiec_9798_2_5_bdkey_P_1))
  , ((isoiec_9798_2_5_bdkey_A, ''Text1''),
     (KnownT isoiec_9798_2_5_bdkey_A_text_1))
  , ((isoiec_9798_2_5_bdkey_P, ''Text1''),
     (KnownT isoiec_9798_2_5_bdkey_P_1))
  , ((isoiec_9798_2_5_bdkey_B, ''Text2''),
     (KnownT isoiec_9798_2_5_bdkey_B_3))
  , ((isoiec_9798_2_5_bdkey_P, ''Text2''),
     (KnownT isoiec_9798_2_5_bdkey_P_text_2))
  , ((isoiec_9798_2_5_bdkey_A, ''Text3''),
     (KnownT isoiec_9798_2_5_bdkey_A_2))
  , ((isoiec_9798_2_5_bdkey_P, ''Text3''),
     (KnownT isoiec_9798_2_5_bdkey_P_text_2))
  , ((isoiec_9798_2_5_bdkey_A, ''Text4''),
     (KnownT isoiec_9798_2_5_bdkey_A_2))
  , ((isoiec_9798_2_5_bdkey_P, ''Text4''),
     (KnownT isoiec_9798_2_5_bdkey_P_text_2))
  , ((isoiec_9798_2_5_bdkey_A, ''Text5''),
     (KnownT isoiec_9798_2_5_bdkey_A_text_3))
  , ((isoiec_9798_2_5_bdkey_B, ''Text5''),
     (KnownT isoiec_9798_2_5_bdkey_B_3))
  , ((isoiec_9798_2_5_bdkey_A, ''Text6''),
     (KnownT isoiec_9798_2_5_bdkey_A_text_3))
  , ((isoiec_9798_2_5_bdkey_B, ''Text6''),
     (KnownT isoiec_9798_2_5_bdkey_B_3))
  , ((isoiec_9798_2_5_bdkey_A, ''Text7''),
     (KnownT isoiec_9798_2_5_bdkey_A_4))
  , ((isoiec_9798_2_5_bdkey_B, ''Text7''),
     (KnownT isoiec_9798_2_5_bdkey_B_text_4))
  , ((isoiec_9798_2_5_bdkey_A, ''Text8''),
     (KnownT isoiec_9798_2_5_bdkey_A_4))
  , ((isoiec_9798_2_5_bdkey_B, ''Text8''),
     (KnownT isoiec_9798_2_5_bdkey_B_text_4))
  , ((isoiec_9798_2_5_bdkey_A, ''TokenPA_for_B''),
     (KnownT isoiec_9798_2_5_bdkey_A_2))
  ]"

sublocale isoiec_9798_2_5_bdkey_state < isoiec_9798_2_5_bdkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_2_5_bdkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_2_5_bdkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_2_5_bdkey_A_2_Kab t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid0,
               s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(AV ''B'' tid0),
               s(MV ''Text3'' tid0)
            |}
            ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_bdkey_A_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid0,
               s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(AV ''B'' tid0),
               s(MV ''Text3'' tid0)
            |}
            ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_bdkey_A_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_bdkey_A_2_TokenPA_for_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_bdkey_A_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_bdkey_A_text_3_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_bdkey_A_4_TNb t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_4'', s(MV ''TNb'' tid0),
               s(AV ''A'' tid0), s(MV ''Text7'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_bdkey_A_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_4'', s(MV ''TNb'' tid0),
               s(AV ''A'' tid0), s(MV ''Text7'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_bdkey_A_4_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_bdkey_B_3_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_bdkey_B_3_Kab t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_2_2'', s(MV ''TNp'' tid0),
               s(MV ''Kab'' tid0), s(MV ''A'' tid0), s(AV ''B'' tid0),
               s(MV ''Text2'' tid0)
            |}
            ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_bdkey_B_3_P t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_bdkey_B_3_TNa t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_3'', s(MV ''TNa'' tid0),
               s(AV ''B'' tid0), s(MV ''Text5'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_bdkey_B_3_TNp t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_2_2'', s(MV ''TNp'' tid0),
               s(MV ''Kab'' tid0), s(MV ''A'' tid0), s(AV ''B'' tid0),
               s(MV ''Text2'' tid0)
            |}
            ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_bdkey_B_3_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_2_2'', s(MV ''TNp'' tid0),
               s(MV ''Kab'' tid0), s(MV ''A'' tid0), s(AV ''B'' tid0),
               s(MV ''Text2'' tid0)
            |}
            ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_bdkey_B_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_enc_3'', s(MV ''TNa'' tid0),
               s(AV ''B'' tid0), s(MV ''Text5'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_bdkey_B_3_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_bdkey_B_text_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_bdkey_B_text_4_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_bdkey_P_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_bdkey_P_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_bdkey_P_1_TVPa t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_bdkey_P_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_bdkey_P_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_bdkey_P_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_bdkey_P_text_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_2_5_bdkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_2_5_bdkey_state begin

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

lemma (in restricted_isoiec_9798_2_5_bdkey_state) P_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_5_bdkey_P"
    "RLKR(s(AV ''P'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "LN ''Kab'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''Kab'' tid0 ")
  case isoiec_9798_2_5_bdkey_P_2_Kab note_unified facts = this facts
  thus ?thesis by (fastforce dest!: ltk_secrecy)
next
  case isoiec_9798_2_5_bdkey_P_2_Kab_1 note_unified facts = this facts
  thus ?thesis by (fastforce dest!: ltk_secrecy)
qed (insert facts, fastforce+)?

lemma (in restricted_isoiec_9798_2_5_bdkey_state) A_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_5_bdkey_A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(AV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_5_bdkey_A_2 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid0,
                          s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(AV ''B'' tid0),
                          s(MV ''Text3'' tid0)
                       |}
                       ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_5_bdkey_P_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_isoiec_9798_2_5_bdkey_state) B_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_5_bdkey_B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_5_bdkey_B_3 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_5_enc_2_2'', s(MV ''TNp'' tid0),
                          s(MV ''Kab'' tid0), s(MV ''A'' tid0), s(AV ''B'' tid0),
                          s(MV ''Text2'' tid0)
                       |}
                       ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_5_bdkey_P_2_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_isoiec_9798_2_5_bdkey_state) A_injective_agreement_B:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_5_bdkey_A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          RLKR(s(AV ''P'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_5_bdkey_A_4 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_5_bdkey_B &
          ( tid1, isoiec_9798_2_5_bdkey_B_4 ) : steps t &
          {| s(MV ''A'' tid1), s(AV ''B'' tid1), s(MV ''P'' tid1),
             s(MV ''Kab'' tid1), s(MV ''TNa'' tid1), s(MV ''Text5'' tid1),
             LN ''TNb'' tid1, s(MV ''Text7'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(AV ''P'' tid0),
                  s(MV ''Kab'' tid0), LN ''TNa'' tid0, s(MV ''Text5'' tid0),
                  s(MV ''TNb'' tid0), s(MV ''Text7'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid0,
                              s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(AV ''B'' tid0),
                              s(MV ''Text3'' tid0)
                           |}
                           ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_5_bdkey_P_2_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_2_5_enc_4'', s(MV ''TNb'' tid0),
                                s(AV ''A'' tid0), s(MV ''Text7'' tid0)
                             |}
                             ( LN ''Kab'' tid1 ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
        next
          case (isoiec_9798_2_5_bdkey_B_4_enc tid2) note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''isoiec_9798_2_5_enc_2_2'', s(MV ''TNp'' tid2),
                                  LN ''Kab'' tid1, s(AV ''A'' tid0), s(AV ''B'' tid2), s(MV ''Text2'' tid2)
                               |}
                               ( Kbd ( s(AV ''B'' tid2) ) ( s(MV ''P'' tid2) ) ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
          next
            case (isoiec_9798_2_5_bdkey_P_2_enc_1 tid3) note_unified facts = this facts
            thus ?thesis proof(sources! "
                             Enc {| LC ''isoiec_9798_2_5_enc_3'', s(MV ''TNa'' tid2),
                                    s(AV ''B'' tid0), s(MV ''Text5'' tid2)
                                 |}
                                 ( LN ''Kab'' tid1 ) ")
              case fake note_unified facts = this facts
              thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
            next
              case (isoiec_9798_2_5_bdkey_A_3_enc tid3) note_unified facts = this facts
              thus ?thesis proof(sources! "
                               Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid3, LN ''Kab'' tid1,
                                      s(AV ''A'' tid3), s(AV ''B'' tid0), s(MV ''Text3'' tid3)
                                   |}
                                   ( Kbd ( s(AV ''A'' tid3) ) ( s(AV ''P'' tid3) ) ) ")
                case fake note_unified facts = this facts
                thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
              next
                case (isoiec_9798_2_5_bdkey_P_2_enc tid4) note_unified facts = this facts
                thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
              qed (insert facts, fastforce+)?
            qed (insert facts, fastforce+)?
          qed (insert facts, fastforce+)?
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_2_5_bdkey_state) B_non_injective_agreement_A:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_5_bdkey_B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_5_bdkey_B_3 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_5_bdkey_A &
        ( tid1, isoiec_9798_2_5_bdkey_A_3 ) : steps t &
        {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(AV ''P'' tid1),
           s(MV ''Kab'' tid1), LN ''TNa'' tid1, s(MV ''Text5'' tid1)
        |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''P'' tid0),
                s(MV ''Kab'' tid0), s(MV ''TNa'' tid0), s(MV ''Text5'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_5_enc_2_2'', s(MV ''TNp'' tid0),
                          s(MV ''Kab'' tid0), s(MV ''A'' tid0), s(AV ''B'' tid0),
                          s(MV ''Text2'' tid0)
                       |}
                       ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_5_bdkey_P_2_enc_1 tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''isoiec_9798_2_5_enc_3'', s(MV ''TNa'' tid0),
                            s(AV ''B'' tid0), s(MV ''Text5'' tid0)
                         |}
                         ( LN ''Kab'' tid1 ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
    next
      case (isoiec_9798_2_5_bdkey_A_3_enc tid2) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid2, LN ''Kab'' tid1,
                              s(AV ''A'' tid2), s(AV ''B'' tid0), s(MV ''Text3'' tid2)
                           |}
                           ( Kbd ( s(AV ''A'' tid2) ) ( s(AV ''P'' tid2) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
      next
        case (isoiec_9798_2_5_bdkey_P_2_enc tid3) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed (insert facts, fastforce+)?
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_isoiec_9798_2_5_bdkey_state) A_injective_agreement_P:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_5_bdkey_A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          RLKR(s(AV ''P'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_5_bdkey_A_2 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_5_bdkey_P &
          ( tid1, isoiec_9798_2_5_bdkey_P_2 ) : steps t &
          {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1), LN ''Kab'' tid1,
             s(MV ''TVPa'' tid1), s(MV ''Text3'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(AV ''P'' tid0),
                  s(MV ''Kab'' tid0), LN ''TVPa'' tid0, s(MV ''Text3'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid0,
                              s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(AV ''B'' tid0),
                              s(MV ''Text3'' tid0)
                           |}
                           ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_5_bdkey_P_2_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_2_5_bdkey_state) B_non_injective_agreement_P:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_5_bdkey_B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_5_bdkey_B_3 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_5_bdkey_P &
        ( tid1, isoiec_9798_2_5_bdkey_P_2 ) : steps t &
        {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1), LN ''Kab'' tid1,
           LN ''TNp'' tid1, s(MV ''Text2'' tid1)
        |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''P'' tid0),
                s(MV ''Kab'' tid0), s(MV ''TNp'' tid0), s(MV ''Text2'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_5_enc_2_2'', s(MV ''TNp'' tid0),
                          s(MV ''Kab'' tid0), s(MV ''A'' tid0), s(AV ''B'' tid0),
                          s(MV ''Text2'' tid0)
                       |}
                       ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_5_bdkey_P_2_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (insert facts, fastforce+)?
qed

role isoiec_9798_2_6_bdkey_A
where "isoiec_9798_2_6_bdkey_A =
  [ Recv ''1'' <| sMV ''B'', sAV ''A'', sMV ''Rb'', sMV ''Text1'' |>
  , Recv ''text_2'' ( sMV ''Text2'' )
  , Send ''2'' <| sAV ''A'', sAV ''P'', sN ''Ra'', sMV ''Rb'', sMV ''B'',
                  sMV ''Text2''
               |>
  , Recv ''3'' <| sAV ''P'', sAV ''A'', sMV ''Text5'',
                  PEnc <| sC ''isoiec_9798_2_6_enc_3_1'', sN ''Ra'', sMV ''Kab'',
                          sAV ''A'', sMV ''B'', sMV ''Text4''
                       |>
                       ( sKbd (AVar ''A'') (AVar ''P'') ),
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

role isoiec_9798_2_6_bdkey_B
where "isoiec_9798_2_6_bdkey_B =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''B'', sAV ''A'', sN ''Rb'', sMV ''Text1'' |>
  , Recv ''4'' <| sAV ''A'', sAV ''B'', sMV ''Text7'', sMV ''P'',
                  PEnc <| sC ''isoiec_9798_2_6_enc_3_2'', sN ''Rb'', sMV ''Kab'',
                          sAV ''A'', sAV ''B'', sMV ''Text3''
                       |>
                       ( sKbd (AVar ''B'') (MVar ''P'') ),
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

role isoiec_9798_2_6_bdkey_P
where "isoiec_9798_2_6_bdkey_P =
  [ Recv ''2'' <| sMV ''A'', sAV ''P'', sMV ''Ra'', sMV ''Rb'', sMV ''B'',
                  sMV ''Text2''
               |>
  , Recv ''text_3'' <| sMV ''Text3'', sMV ''Text4'', sMV ''Text5'' |>
  , Send ''3'' <| sAV ''P'', sMV ''A'', sMV ''Text5'',
                  PEnc <| sC ''isoiec_9798_2_6_enc_3_1'', sMV ''Ra'', sN ''Kab'',
                          sMV ''A'', sMV ''B'', sMV ''Text4''
                       |>
                       ( sKbd (MVar ''A'') (AVar ''P'') ),
                  PEnc <| sC ''isoiec_9798_2_6_enc_3_2'', sMV ''Rb'', sN ''Kab'',
                          sMV ''A'', sMV ''B'', sMV ''Text3''
                       |>
                       ( sKbd (MVar ''B'') (AVar ''P'') )
               |>
  ]"

protocol isoiec_9798_2_6_bdkey
where "isoiec_9798_2_6_bdkey =
{ isoiec_9798_2_6_bdkey_A, isoiec_9798_2_6_bdkey_B,
  isoiec_9798_2_6_bdkey_P
}"

locale restricted_isoiec_9798_2_6_bdkey_state = isoiec_9798_2_6_bdkey_state

type_invariant isoiec_9798_2_6_bdkey_msc_typing for isoiec_9798_2_6_bdkey
where "isoiec_9798_2_6_bdkey_msc_typing = mk_typing
  [ ((isoiec_9798_2_6_bdkey_P, ''A''), (KnownT isoiec_9798_2_6_bdkey_P_2))
  , ((isoiec_9798_2_6_bdkey_A, ''B''), (KnownT isoiec_9798_2_6_bdkey_A_1))
  , ((isoiec_9798_2_6_bdkey_P, ''B''), (KnownT isoiec_9798_2_6_bdkey_P_2))
  , ((isoiec_9798_2_6_bdkey_A, ''Kab''),
     (SumT (KnownT isoiec_9798_2_6_bdkey_A_3) (NonceT isoiec_9798_2_6_bdkey_P ''Kab'')))
  , ((isoiec_9798_2_6_bdkey_B, ''Kab''),
     (SumT (KnownT isoiec_9798_2_6_bdkey_B_4) (NonceT isoiec_9798_2_6_bdkey_P ''Kab'')))
  , ((isoiec_9798_2_6_bdkey_B, ''P''), (KnownT isoiec_9798_2_6_bdkey_B_4))
  , ((isoiec_9798_2_6_bdkey_P, ''Ra''), (KnownT isoiec_9798_2_6_bdkey_P_2))
  , ((isoiec_9798_2_6_bdkey_A, ''Rb''), (KnownT isoiec_9798_2_6_bdkey_A_1))
  , ((isoiec_9798_2_6_bdkey_P, ''Rb''), (KnownT isoiec_9798_2_6_bdkey_P_2))
  , ((isoiec_9798_2_6_bdkey_B, ''Rpa''),
     (SumT (KnownT isoiec_9798_2_6_bdkey_B_4) (NonceT isoiec_9798_2_6_bdkey_A ''Rpa'')))
  , ((isoiec_9798_2_6_bdkey_A, ''Text1''),
     (KnownT isoiec_9798_2_6_bdkey_A_1))
  , ((isoiec_9798_2_6_bdkey_B, ''Text1''),
     (KnownT isoiec_9798_2_6_bdkey_B_text_1))
  , ((isoiec_9798_2_6_bdkey_A, ''Text2''),
     (KnownT isoiec_9798_2_6_bdkey_A_text_2))
  , ((isoiec_9798_2_6_bdkey_P, ''Text2''),
     (KnownT isoiec_9798_2_6_bdkey_P_2))
  , ((isoiec_9798_2_6_bdkey_B, ''Text3''),
     (KnownT isoiec_9798_2_6_bdkey_B_4))
  , ((isoiec_9798_2_6_bdkey_P, ''Text3''),
     (KnownT isoiec_9798_2_6_bdkey_P_text_3))
  , ((isoiec_9798_2_6_bdkey_A, ''Text4''),
     (KnownT isoiec_9798_2_6_bdkey_A_3))
  , ((isoiec_9798_2_6_bdkey_P, ''Text4''),
     (KnownT isoiec_9798_2_6_bdkey_P_text_3))
  , ((isoiec_9798_2_6_bdkey_A, ''Text5''),
     (KnownT isoiec_9798_2_6_bdkey_A_3))
  , ((isoiec_9798_2_6_bdkey_P, ''Text5''),
     (KnownT isoiec_9798_2_6_bdkey_P_text_3))
  , ((isoiec_9798_2_6_bdkey_A, ''Text6''),
     (KnownT isoiec_9798_2_6_bdkey_A_text_4))
  , ((isoiec_9798_2_6_bdkey_B, ''Text6''),
     (KnownT isoiec_9798_2_6_bdkey_B_4))
  , ((isoiec_9798_2_6_bdkey_A, ''Text7''),
     (KnownT isoiec_9798_2_6_bdkey_A_text_4))
  , ((isoiec_9798_2_6_bdkey_B, ''Text7''),
     (KnownT isoiec_9798_2_6_bdkey_B_4))
  , ((isoiec_9798_2_6_bdkey_A, ''Text8''),
     (KnownT isoiec_9798_2_6_bdkey_A_5))
  , ((isoiec_9798_2_6_bdkey_B, ''Text8''),
     (KnownT isoiec_9798_2_6_bdkey_B_text_5))
  , ((isoiec_9798_2_6_bdkey_A, ''Text9''),
     (KnownT isoiec_9798_2_6_bdkey_A_5))
  , ((isoiec_9798_2_6_bdkey_B, ''Text9''),
     (KnownT isoiec_9798_2_6_bdkey_B_text_5))
  , ((isoiec_9798_2_6_bdkey_A, ''TokenPA_for_B''),
     (KnownT isoiec_9798_2_6_bdkey_A_3))
  ]"

sublocale isoiec_9798_2_6_bdkey_state < isoiec_9798_2_6_bdkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_2_6_bdkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_2_6_bdkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_2_6_bdkey_A_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_A_1_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_A_3_Kab t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid0,
               s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''B'' tid0),
               s(MV ''Text4'' tid0)
            |}
            ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_bdkey_A_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid0,
               s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''B'' tid0),
               s(MV ''Text4'' tid0)
            |}
            ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_bdkey_A_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_A_3_TokenPA_for_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_A_text_4_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_A_text_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_A_5_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_5'', s(MV ''Rb'' tid0), LN ''Rpa'' tid0,
               s(MV ''Text8'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_bdkey_A_5_Text9 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_B_4_Kab t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid0,
               s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(AV ''B'' tid0),
               s(MV ''Text3'' tid0)
            |}
            ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_bdkey_B_4_P t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_B_4_Rpa t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_4'', s(MV ''Rpa'' tid0), LN ''Rb'' tid0,
               s(MV ''Text6'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_bdkey_B_4_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid0,
               s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(AV ''B'' tid0),
               s(MV ''Text3'' tid0)
            |}
            ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_bdkey_B_4_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_4'', s(MV ''Rpa'' tid0), LN ''Rb'' tid0,
               s(MV ''Text6'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_bdkey_B_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_B_text_5_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_B_text_5_Text9 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_P_2_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_P_2_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_P_2_Ra t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_P_2_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_P_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_P_text_3_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_P_text_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_bdkey_P_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_2_6_bdkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_2_6_bdkey_state begin

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

lemma (in restricted_isoiec_9798_2_6_bdkey_state) P_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_6_bdkey_P"
    "RLKR(s(AV ''P'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "LN ''Kab'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''Kab'' tid0 ")
  case isoiec_9798_2_6_bdkey_P_3_Kab note_unified facts = this facts
  thus ?thesis by (fastforce dest!: ltk_secrecy)
next
  case isoiec_9798_2_6_bdkey_P_3_Kab_1 note_unified facts = this facts
  thus ?thesis by (fastforce dest!: ltk_secrecy)
qed (insert facts, fastforce+)?

lemma (in restricted_isoiec_9798_2_6_bdkey_state) A_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_6_bdkey_A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''P'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_6_bdkey_A_3 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid0,
                          s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''B'' tid0),
                          s(MV ''Text4'' tid0)
                       |}
                       ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_6_bdkey_P_3_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_isoiec_9798_2_6_bdkey_state) B_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_6_bdkey_B"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_6_bdkey_B_4 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid0,
                          s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(AV ''B'' tid0),
                          s(MV ''Text3'' tid0)
                       |}
                       ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_6_bdkey_P_3_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_isoiec_9798_2_6_bdkey_state) A_injective_agreement_B:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_6_bdkey_A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''P'' tid0)) ~: reveals t &
          RLKR(s(MV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_6_bdkey_A_5 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_6_bdkey_B &
          ( tid1, isoiec_9798_2_6_bdkey_B_5 ) : steps t &
          {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(MV ''P'' tid1),
             s(MV ''Kab'' tid1), s(MV ''Rpa'' tid1), LN ''Rb'' tid1,
             s(MV ''Text6'' tid1), s(MV ''Text8'' tid1)
          |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), s(AV ''P'' tid0),
                  s(MV ''Kab'' tid0), LN ''Rpa'' tid0, s(MV ''Rb'' tid0),
                  s(MV ''Text6'' tid0), s(MV ''Text8'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid0,
                              s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''B'' tid0),
                              s(MV ''Text4'' tid0)
                           |}
                           ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_6_bdkey_P_3_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_2_6_enc_5'', s(MV ''Rb'' tid0), LN ''Rpa'' tid0,
                                s(MV ''Text8'' tid0)
                             |}
                             ( LN ''Kab'' tid1 ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
        next
          case (isoiec_9798_2_6_bdkey_B_5_enc tid2) note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid2, LN ''Kab'' tid1,
                                  s(AV ''A'' tid2), s(AV ''B'' tid2), s(MV ''Text3'' tid2)
                               |}
                               ( Kbd ( s(AV ''B'' tid2) ) ( s(MV ''P'' tid2) ) ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
          next
            case (isoiec_9798_2_6_bdkey_P_3_enc_1 tid3) note_unified facts = this facts
            thus ?thesis proof(sources! "
                             Enc {| LC ''isoiec_9798_2_6_enc_4'', LN ''Rpa'' tid0, LN ''Rb'' tid2,
                                    s(MV ''Text6'' tid2)
                                 |}
                                 ( LN ''Kab'' tid1 ) ")
              case fake note_unified facts = this facts
              thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
            next
              case (isoiec_9798_2_6_bdkey_A_4_enc tid3) note_unified facts = this facts
              thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
            qed (insert facts, fastforce+)?
          qed (insert facts, fastforce+)?
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_2_6_bdkey_state) B_injective_agreement_A:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_6_bdkey_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          RLKR(s(MV ''P'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_6_bdkey_B_4 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_6_bdkey_A &
          ( tid1, isoiec_9798_2_6_bdkey_A_4 ) : steps t &
          {| s(AV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1),
             s(MV ''Kab'' tid1), LN ''Rpa'' tid1, s(MV ''Rb'' tid1),
             s(MV ''Text6'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''P'' tid0),
                  s(MV ''Kab'' tid0), s(MV ''Rpa'' tid0), LN ''Rb'' tid0,
                  s(MV ''Text6'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid0,
                              s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(AV ''B'' tid0),
                              s(MV ''Text3'' tid0)
                           |}
                           ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_6_bdkey_P_3_enc_1 tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_2_6_enc_4'', s(MV ''Rpa'' tid0), LN ''Rb'' tid0,
                                s(MV ''Text6'' tid0)
                             |}
                             ( LN ''Kab'' tid1 ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
        next
          case (isoiec_9798_2_6_bdkey_A_4_enc tid2) note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid2, LN ''Kab'' tid1,
                                  s(AV ''A'' tid2), s(MV ''B'' tid2), s(MV ''Text4'' tid2)
                               |}
                               ( Kbd ( s(AV ''A'' tid2) ) ( s(AV ''P'' tid2) ) ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
          next
            case (isoiec_9798_2_6_bdkey_P_3_enc tid3) note_unified facts = this facts
            thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
          qed (insert facts, fastforce+)?
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_2_6_bdkey_state) A_injective_agreement_P:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_6_bdkey_A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''P'' tid0)) ~: reveals t &
          RLKR(s(MV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_6_bdkey_A_3 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_6_bdkey_P &
          ( tid1, isoiec_9798_2_6_bdkey_P_3 ) : steps t &
          {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1),
             s(MV ''Ra'' tid1), LN ''Kab'' tid1, s(MV ''Text4'' tid1)
          |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), s(AV ''P'' tid0),
                  LN ''Ra'' tid0, s(MV ''Kab'' tid0), s(MV ''Text4'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid0,
                              s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''B'' tid0),
                              s(MV ''Text4'' tid0)
                           |}
                           ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_6_bdkey_P_3_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_2_6_bdkey_state) B_injective_agreement_P:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_6_bdkey_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          RLKR(s(MV ''P'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_6_bdkey_B_4 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_6_bdkey_P &
          ( tid1, isoiec_9798_2_6_bdkey_P_3 ) : steps t &
          {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1),
             s(MV ''Rb'' tid1), LN ''Kab'' tid1, s(MV ''Text3'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''P'' tid0),
                  LN ''Rb'' tid0, s(MV ''Kab'' tid0), s(MV ''Text3'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid0,
                              s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(AV ''B'' tid0),
                              s(MV ''Text3'' tid0)
                           |}
                           ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_6_bdkey_P_3_enc_1 tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

role isoiec_9798_2_5_special_TTP_bdkey_A
where "isoiec_9798_2_5_special_TTP_bdkey_A =
  [ Send ''leak_A'' <| sN ''TVPa'', sN ''TNa'' |>
  , Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''A'', sAV ''P'', sN ''TVPa'', sAV ''B'',
                  sMV ''Text1''
               |>
  , Recv ''2'' <| sAV ''P'', sAV ''A'', sMV ''Text4'',
                  PEnc <| sC ''isoiec_9798_2_5_special_TTP_enc_2_1'', sN ''TVPa'',
                          sMV ''Kab'', sAV ''B'', sMV ''Text3''
                       |>
                       ( sKbd (AVar ''A'') (AVar ''P'') ),
                  sMV ''TokenPA_for_B''
               |>
  , Recv ''text_3'' <| sMV ''Text5'', sMV ''Text6'' |>
  , Send ''3'' <| sAV ''A'', sAV ''B'', sMV ''Text6'', sAV ''P'',
                  sMV ''TokenPA_for_B'',
                  PEnc <| sC ''isoiec_9798_2_5_special_TTP_enc_3'', sN ''TNa'', sAV ''B'',
                          sMV ''Text5''
                       |>
                       ( sMV ''Kab'' )
               |>
  , Recv ''4'' <| sAV ''B'', sAV ''A'', sMV ''Text8'',
                  PEnc <| sC ''isoiec_9798_2_5_special_TTP_enc_4'', sMV ''TNb'', sAV ''A'',
                          sMV ''Text7''
                       |>
                       ( sMV ''Kab'' )
               |>
  ]"

role isoiec_9798_2_5_special_TTP_bdkey_B
where "isoiec_9798_2_5_special_TTP_bdkey_B =
  [ Send ''leak_B'' ( sN ''TNb'' )
  , Recv ''3'' <| sMV ''A'', sAV ''B'', sMV ''Text6'', sMV ''P'',
                  PEnc <| sC ''isoiec_9798_2_5_special_TTP_enc_2_2'', sMV ''TNp'',
                          sMV ''Kab'', sMV ''A'', sMV ''Text2''
                       |>
                       ( sKbd (AVar ''B'') (MVar ''P'') ),
                  PEnc <| sC ''isoiec_9798_2_5_special_TTP_enc_3'', sMV ''TNa'', sAV ''B'',
                          sMV ''Text5''
                       |>
                       ( sMV ''Kab'' )
               |>
  , Recv ''text_4'' <| sMV ''Text7'', sMV ''Text8'' |>
  , Send ''4'' <| sAV ''B'', sMV ''A'', sMV ''Text8'',
                  PEnc <| sC ''isoiec_9798_2_5_special_TTP_enc_4'', sN ''TNb'', sMV ''A'',
                          sMV ''Text7''
                       |>
                       ( sMV ''Kab'' )
               |>
  ]"

role isoiec_9798_2_5_special_TTP_bdkey_P
where "isoiec_9798_2_5_special_TTP_bdkey_P =
  [ Send ''leak_P'' ( sN ''TNp'' )
  , Recv ''1'' <| sMV ''A'', sAV ''P'', sMV ''TVPa'', sMV ''B'',
                  sMV ''Text1''
               |>
  , Recv ''text_2'' <| sMV ''Text2'', sMV ''Text3'', sMV ''Text4'' |>
  , Send ''2'' <| sAV ''P'', sMV ''A'', sMV ''Text4'',
                  PEnc <| sC ''isoiec_9798_2_5_special_TTP_enc_2_1'', sMV ''TVPa'',
                          sN ''Kab'', sMV ''B'', sMV ''Text3''
                       |>
                       ( sKbd (MVar ''A'') (AVar ''P'') ),
                  PEnc <| sC ''isoiec_9798_2_5_special_TTP_enc_2_2'', sN ''TNp'',
                          sN ''Kab'', sMV ''A'', sMV ''Text2''
                       |>
                       ( sKbd (MVar ''B'') (AVar ''P'') )
               |>
  ]"

protocol isoiec_9798_2_5_special_TTP_bdkey
where "isoiec_9798_2_5_special_TTP_bdkey =
{ isoiec_9798_2_5_special_TTP_bdkey_A,
  isoiec_9798_2_5_special_TTP_bdkey_B, isoiec_9798_2_5_special_TTP_bdkey_P
}"

locale restricted_isoiec_9798_2_5_special_TTP_bdkey_state = isoiec_9798_2_5_special_TTP_bdkey_state +
  assumes different_actors_A_P:
    "!! tid0 tid1.
       [| roleMap r tid0 = Some isoiec_9798_2_5_special_TTP_bdkey_A;
         roleMap r tid1 = Some isoiec_9798_2_5_special_TTP_bdkey_P;
         s(AV ''P'' tid1) = s(AV ''A'' tid0)
       |] ==> False"

type_invariant isoiec_9798_2_5_special_TTP_bdkey_msc_typing for isoiec_9798_2_5_special_TTP_bdkey
where "isoiec_9798_2_5_special_TTP_bdkey_msc_typing = mk_typing
  [ ((isoiec_9798_2_5_special_TTP_bdkey_B, ''A''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_B_3))
  , ((isoiec_9798_2_5_special_TTP_bdkey_P, ''A''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_P_1))
  , ((isoiec_9798_2_5_special_TTP_bdkey_P, ''B''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_P_1))
  , ((isoiec_9798_2_5_special_TTP_bdkey_A, ''Kab''),
     (SumT (KnownT isoiec_9798_2_5_special_TTP_bdkey_A_2) (NonceT isoiec_9798_2_5_special_TTP_bdkey_P ''Kab'')))
  , ((isoiec_9798_2_5_special_TTP_bdkey_B, ''Kab''),
     (SumT (KnownT isoiec_9798_2_5_special_TTP_bdkey_B_3) (NonceT isoiec_9798_2_5_special_TTP_bdkey_P ''Kab'')))
  , ((isoiec_9798_2_5_special_TTP_bdkey_B, ''P''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_B_3))
  , ((isoiec_9798_2_5_special_TTP_bdkey_B, ''TNa''),
     (SumT (KnownT isoiec_9798_2_5_special_TTP_bdkey_B_3) (NonceT isoiec_9798_2_5_special_TTP_bdkey_A ''TNa'')))
  , ((isoiec_9798_2_5_special_TTP_bdkey_A, ''TNb''),
     (SumT (KnownT isoiec_9798_2_5_special_TTP_bdkey_A_4) (NonceT isoiec_9798_2_5_special_TTP_bdkey_B ''TNb'')))
  , ((isoiec_9798_2_5_special_TTP_bdkey_B, ''TNp''),
     (SumT (KnownT isoiec_9798_2_5_special_TTP_bdkey_B_3) (NonceT isoiec_9798_2_5_special_TTP_bdkey_P ''TNp'')))
  , ((isoiec_9798_2_5_special_TTP_bdkey_P, ''TVPa''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_P_1))
  , ((isoiec_9798_2_5_special_TTP_bdkey_A, ''Text1''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_A_text_1))
  , ((isoiec_9798_2_5_special_TTP_bdkey_P, ''Text1''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_P_1))
  , ((isoiec_9798_2_5_special_TTP_bdkey_B, ''Text2''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_B_3))
  , ((isoiec_9798_2_5_special_TTP_bdkey_P, ''Text2''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_P_text_2))
  , ((isoiec_9798_2_5_special_TTP_bdkey_A, ''Text3''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_A_2))
  , ((isoiec_9798_2_5_special_TTP_bdkey_P, ''Text3''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_P_text_2))
  , ((isoiec_9798_2_5_special_TTP_bdkey_A, ''Text4''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_A_2))
  , ((isoiec_9798_2_5_special_TTP_bdkey_P, ''Text4''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_P_text_2))
  , ((isoiec_9798_2_5_special_TTP_bdkey_A, ''Text5''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_A_text_3))
  , ((isoiec_9798_2_5_special_TTP_bdkey_B, ''Text5''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_B_3))
  , ((isoiec_9798_2_5_special_TTP_bdkey_A, ''Text6''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_A_text_3))
  , ((isoiec_9798_2_5_special_TTP_bdkey_B, ''Text6''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_B_3))
  , ((isoiec_9798_2_5_special_TTP_bdkey_A, ''Text7''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_A_4))
  , ((isoiec_9798_2_5_special_TTP_bdkey_B, ''Text7''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_B_text_4))
  , ((isoiec_9798_2_5_special_TTP_bdkey_A, ''Text8''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_A_4))
  , ((isoiec_9798_2_5_special_TTP_bdkey_B, ''Text8''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_B_text_4))
  , ((isoiec_9798_2_5_special_TTP_bdkey_A, ''TokenPA_for_B''),
     (KnownT isoiec_9798_2_5_special_TTP_bdkey_A_2))
  ]"

sublocale isoiec_9798_2_5_special_TTP_bdkey_state < isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_2_5_special_TTP_bdkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_2_5_special_TTP_bdkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_2_5_special_TTP_bdkey_A_2_Kab t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_2_1'', LN ''TVPa'' tid0,
               s(MV ''Kab'' tid0), s(AV ''B'' tid0), s(MV ''Text3'' tid0)
            |}
            ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_A_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_2_1'', LN ''TVPa'' tid0,
               s(MV ''Kab'' tid0), s(AV ''B'' tid0), s(MV ''Text3'' tid0)
            |}
            ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_A_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_A_2_TokenPA_for_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_A_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_A_text_3_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_A_4_TNb t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_4'', s(MV ''TNb'' tid0),
               s(AV ''A'' tid0), s(MV ''Text7'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_A_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_4'', s(MV ''TNb'' tid0),
               s(AV ''A'' tid0), s(MV ''Text7'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_A_4_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_B_3_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_B_3_Kab t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_2_2'', s(MV ''TNp'' tid0),
               s(MV ''Kab'' tid0), s(MV ''A'' tid0), s(MV ''Text2'' tid0)
            |}
            ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_B_3_P t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_B_3_TNa t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_3'', s(MV ''TNa'' tid0),
               s(AV ''B'' tid0), s(MV ''Text5'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_B_3_TNp t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_2_2'', s(MV ''TNp'' tid0),
               s(MV ''Kab'' tid0), s(MV ''A'' tid0), s(MV ''Text2'' tid0)
            |}
            ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_B_3_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_2_2'', s(MV ''TNp'' tid0),
               s(MV ''Kab'' tid0), s(MV ''A'' tid0), s(MV ''Text2'' tid0)
            |}
            ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_B_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_3'', s(MV ''TNa'' tid0),
               s(AV ''B'' tid0), s(MV ''Text5'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_B_3_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_B_text_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_B_text_4_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_P_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_P_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_P_1_TVPa t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_P_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_P_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_P_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_P_text_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_2_5_special_TTP_bdkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_2_5_special_TTP_bdkey_state begin

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


lemma (in restricted_isoiec_9798_2_5_special_TTP_bdkey_state) P_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_5_special_TTP_bdkey_P"
    "RLKR(s(AV ''P'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "LN ''Kab'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''Kab'' tid0 ")
  case isoiec_9798_2_5_special_TTP_bdkey_P_2_Kab note_unified facts = this facts
  thus ?thesis by (fastforce dest!: ltk_secrecy)
next
  case isoiec_9798_2_5_special_TTP_bdkey_P_2_Kab_1 note_unified facts = this facts
  thus ?thesis by (fastforce dest!: ltk_secrecy)
qed (insert facts, fastforce+)?

lemma (in restricted_isoiec_9798_2_5_special_TTP_bdkey_state) A_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_5_special_TTP_bdkey_A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(AV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_5_special_TTP_bdkey_A_2 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_2_1'', LN ''TVPa'' tid0,
                          s(MV ''Kab'' tid0), s(AV ''B'' tid0), s(MV ''Text3'' tid0)
                       |}
                       ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_P_2_enc tid1) note_unified facts = this facts
    hence "Kbd ( s(AV ''P'' tid1) )
               ( s(MV ''A'' tid1) ) = Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) )"
      by simp note facts = this facts
    thus ?thesis proof(cases rule: Kbd_cases)
      case noswap note_unified facts = this facts
      thus ?thesis by (fastforce dest: different_actors_A_P intro: event_predOrdI)
    next
      case swapped note_unified facts = this facts
      thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
    qed (fastforce+)?
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_isoiec_9798_2_5_special_TTP_bdkey_state) B_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_5_special_TTP_bdkey_B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_5_special_TTP_bdkey_B_3 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_2_2'', s(MV ''TNp'' tid0),
                          s(MV ''Kab'' tid0), s(MV ''A'' tid0), s(MV ''Text2'' tid0)
                       |}
                       ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_P_2_enc_1 tid1) note_unified facts = this facts
    hence "Kbd ( s(AV ''P'' tid1) )
               ( s(MV ''B'' tid1) ) = Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) )"
      by simp note facts = this facts
    thus ?thesis proof(cases rule: Kbd_cases)
      case noswap note_unified facts = this facts
      thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
    next
      case swapped note_unified facts = this facts
      thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
    qed (fastforce+)?
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_isoiec_9798_2_5_special_TTP_bdkey_state) A_injective_agreement_B:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_5_special_TTP_bdkey_A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          RLKR(s(AV ''P'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_5_special_TTP_bdkey_A_4 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_5_special_TTP_bdkey_B &
          ( tid1, isoiec_9798_2_5_special_TTP_bdkey_B_4 ) : steps t &
          {| s(MV ''A'' tid1), s(AV ''B'' tid1), s(MV ''P'' tid1),
             s(MV ''Kab'' tid1), s(MV ''TNa'' tid1), s(MV ''Text5'' tid1),
             LN ''TNb'' tid1, s(MV ''Text7'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(AV ''P'' tid0),
                  s(MV ''Kab'' tid0), LN ''TNa'' tid0, s(MV ''Text5'' tid0),
                  s(MV ''TNb'' tid0), s(MV ''Text7'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_2_1'', LN ''TVPa'' tid0,
                              s(MV ''Kab'' tid0), s(AV ''B'' tid0), s(MV ''Text3'' tid0)
                           |}
                           ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_5_special_TTP_bdkey_P_2_enc tid1) note_unified facts = this facts
        hence "Kbd ( s(AV ''P'' tid1) )
                   ( s(MV ''A'' tid1) ) = Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) )"
          by simp note facts = this facts
        thus ?thesis proof(cases rule: Kbd_cases)
          case noswap note_unified facts = this facts
          thus ?thesis by (fastforce dest: different_actors_A_P intro: event_predOrdI)
        next
          case swapped note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_4'', s(MV ''TNb'' tid0),
                                  s(AV ''A'' tid0), s(MV ''Text7'' tid0)
                               |}
                               ( LN ''Kab'' tid1 ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
          next
            case (isoiec_9798_2_5_special_TTP_bdkey_B_4_enc tid2) note_unified facts = this facts
            thus ?thesis proof(sources! "
                             Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_3'', s(MV ''TNa'' tid2),
                                    s(AV ''B'' tid2), s(MV ''Text5'' tid2)
                                 |}
                                 ( LN ''Kab'' tid1 ) ")
              case fake note_unified facts = this facts
              thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
            next
              case (isoiec_9798_2_5_special_TTP_bdkey_A_3_enc tid3) note_unified facts = this facts
              thus ?thesis proof(sources! "
                               Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_2_1'', LN ''TVPa'' tid3,
                                      LN ''Kab'' tid1, s(AV ''B'' tid2), s(MV ''Text3'' tid3)
                                   |}
                                   ( Kbd ( s(AV ''A'' tid3) ) ( s(AV ''P'' tid3) ) ) ")
                case fake note_unified facts = this facts
                thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
              next
                case (isoiec_9798_2_5_special_TTP_bdkey_P_2_enc tid4) note_unified facts = this facts
                thus ?thesis proof(sources! "
                                 Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_2_2'', s(MV ''TNp'' tid2),
                                        LN ''Kab'' tid1, s(AV ''A'' tid0), s(MV ''Text2'' tid2)
                                     |}
                                     ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid2) ) ) ")
                  case fake note_unified facts = this facts
                  thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
                next
                  case (isoiec_9798_2_5_special_TTP_bdkey_P_2_enc_1 tid3) note_unified facts = this facts
                  thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
                qed (insert facts, fastforce+)?
              qed (insert facts, fastforce+)?
            qed (insert facts, fastforce+)?
          qed (insert facts, fastforce+)?
        qed (fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_2_5_special_TTP_bdkey_state) B_non_injective_agreement_A:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_5_special_TTP_bdkey_B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_5_special_TTP_bdkey_B_3 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_5_special_TTP_bdkey_A &
        ( tid1, isoiec_9798_2_5_special_TTP_bdkey_A_3 ) : steps t &
        {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(AV ''P'' tid1),
           s(MV ''Kab'' tid1), LN ''TNa'' tid1, s(MV ''Text5'' tid1)
        |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''P'' tid0),
                s(MV ''Kab'' tid0), s(MV ''TNa'' tid0), s(MV ''Text5'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_3'', s(MV ''TNa'' tid0),
                          s(AV ''B'' tid0), s(MV ''Text5'' tid0)
                       |}
                       ( s(MV ''Kab'' tid0) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest: B_secret_Kab intro: event_predOrdI)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_A_3_enc tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_2_1'', LN ''TVPa'' tid1,
                            s(MV ''Kab'' tid0), s(AV ''B'' tid0), s(MV ''Text3'' tid1)
                         |}
                         ( Kbd ( s(AV ''A'' tid1) ) ( s(AV ''P'' tid1) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastforce dest: B_secret_Kab intro: event_predOrdI)
    next
      case (isoiec_9798_2_5_special_TTP_bdkey_P_2_enc tid2) note_unified facts = this facts
      hence "Kbd ( s(AV ''P'' tid2) )
                 ( s(MV ''A'' tid2) ) = Kbd ( s(AV ''A'' tid1) ) ( s(AV ''P'' tid1) )"
        by simp note facts = this facts
      thus ?thesis proof(cases rule: Kbd_cases)
        case noswap note_unified facts = this facts
        thus ?thesis by (fastforce dest: different_actors_A_P intro: event_predOrdI)
      next
        case swapped note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_2_2'', s(MV ''TNp'' tid0),
                                LN ''Kab'' tid2, s(MV ''A'' tid0), s(MV ''Text2'' tid0)
                             |}
                             ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest!: ltk_secrecy)
        next
          case (isoiec_9798_2_5_special_TTP_bdkey_P_2_enc_1 tid3) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (insert facts, fastforce+)?
      qed (fastforce+)?
    qed (insert facts, fastforce+)?
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_isoiec_9798_2_5_special_TTP_bdkey_state) A_injective_agreement_P:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_5_special_TTP_bdkey_A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          RLKR(s(AV ''P'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_5_special_TTP_bdkey_A_2 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_5_special_TTP_bdkey_P &
          ( tid1, isoiec_9798_2_5_special_TTP_bdkey_P_2 ) : steps t &
          {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1), LN ''Kab'' tid1,
             s(MV ''TVPa'' tid1), s(MV ''Text3'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(AV ''P'' tid0),
                  s(MV ''Kab'' tid0), LN ''TVPa'' tid0, s(MV ''Text3'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_2_1'', LN ''TVPa'' tid0,
                              s(MV ''Kab'' tid0), s(AV ''B'' tid0), s(MV ''Text3'' tid0)
                           |}
                           ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_5_special_TTP_bdkey_P_2_enc tid1) note_unified facts = this facts
        hence "Kbd ( s(AV ''P'' tid1) )
                   ( s(MV ''A'' tid1) ) = Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) )"
          by simp note facts = this facts
        thus ?thesis proof(cases rule: Kbd_cases)
          case noswap note_unified facts = this facts
          thus ?thesis by (fastforce dest: different_actors_A_P intro: event_predOrdI)
        next
          case swapped note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_2_5_special_TTP_bdkey_state) B_non_injective_agreement_P:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_5_special_TTP_bdkey_B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_5_special_TTP_bdkey_B_3 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_2_5_special_TTP_bdkey_P &
        ( tid1, isoiec_9798_2_5_special_TTP_bdkey_P_2 ) : steps t &
        {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1), LN ''Kab'' tid1,
           LN ''TNp'' tid1, s(MV ''Text2'' tid1)
        |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''P'' tid0),
                s(MV ''Kab'' tid0), s(MV ''TNp'' tid0), s(MV ''Text2'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_2_2'', s(MV ''TNp'' tid0),
                          s(MV ''Kab'' tid0), s(MV ''A'' tid0), s(MV ''Text2'' tid0)
                       |}
                       ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_5_special_TTP_bdkey_P_2_enc_1 tid1) note_unified facts = this facts
    hence "Kbd ( s(AV ''P'' tid1) )
               ( s(MV ''B'' tid1) ) = Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) )"
      by simp note facts = this facts
    thus ?thesis proof(cases rule: Kbd_cases)
      case noswap note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_3'', s(MV ''TNa'' tid0),
                              s(AV ''B'' tid0), s(MV ''Text5'' tid0)
                           |}
                           ( LN ''Kab'' tid1 ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
      next
        case (isoiec_9798_2_5_special_TTP_bdkey_A_3_enc tid2) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_2_5_special_TTP_enc_2_1'', LN ''TVPa'' tid2,
                                LN ''Kab'' tid1, s(AV ''B'' tid0), s(MV ''Text3'' tid2)
                             |}
                             ( Kbd ( s(AV ''A'' tid2) ) ( s(AV ''P'' tid2) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
        next
          case (isoiec_9798_2_5_special_TTP_bdkey_P_2_enc tid3) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    next
      case swapped note_unified facts = this facts
      thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
    qed (fastforce+)?
  qed (insert facts, fastforce+)?
qed

role isoiec_9798_2_6_special_TTP_bdkey_A
where "isoiec_9798_2_6_special_TTP_bdkey_A =
  [ Recv ''1'' <| sMV ''B'', sAV ''A'', sMV ''Rb'', sMV ''Text1'' |>
  , Recv ''text_2'' ( sMV ''Text2'' )
  , Send ''2'' <| sAV ''A'', sAV ''P'', sN ''Ra'', sMV ''Rb'', sMV ''B'',
                  sMV ''Text2''
               |>
  , Recv ''3'' <| sAV ''P'', sAV ''A'', sMV ''Text5'',
                  PEnc <| sC ''isoiec_9798_2_6_special_TTP_enc_3_1'', sN ''Ra'',
                          sMV ''Kab'', sMV ''B'', sMV ''Text4''
                       |>
                       ( sKbd (AVar ''A'') (AVar ''P'') ),
                  sMV ''TokenPA_for_B''
               |>
  , Recv ''text_4'' <| sMV ''Text6'', sMV ''Text7'' |>
  , Send ''4'' <| sAV ''A'', sMV ''B'', sMV ''Text7'', sAV ''P'',
                  sMV ''TokenPA_for_B'',
                  PEnc <| sC ''isoiec_9798_2_6_special_TTP_enc_4'', sN ''Rpa'', sMV ''Rb'',
                          sMV ''Text6''
                       |>
                       ( sMV ''Kab'' )
               |>
  , Recv ''5'' <| sMV ''B'', sAV ''A'', sMV ''Text9'',
                  PEnc <| sC ''isoiec_9798_2_6_special_TTP_enc_5'', sMV ''Rb'', sN ''Rpa'',
                          sMV ''Text8''
                       |>
                       ( sMV ''Kab'' )
               |>
  ]"

role isoiec_9798_2_6_special_TTP_bdkey_B
where "isoiec_9798_2_6_special_TTP_bdkey_B =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''B'', sAV ''A'', sN ''Rb'', sMV ''Text1'' |>
  , Recv ''4'' <| sAV ''A'', sAV ''B'', sMV ''Text7'', sMV ''P'',
                  PEnc <| sC ''isoiec_9798_2_6_special_TTP_enc_3_2'', sN ''Rb'',
                          sMV ''Kab'', sAV ''A'', sMV ''Text3''
                       |>
                       ( sKbd (AVar ''B'') (MVar ''P'') ),
                  PEnc <| sC ''isoiec_9798_2_6_special_TTP_enc_4'', sMV ''Rpa'', sN ''Rb'',
                          sMV ''Text6''
                       |>
                       ( sMV ''Kab'' )
               |>
  , Recv ''text_5'' <| sMV ''Text8'', sMV ''Text9'' |>
  , Send ''5'' <| sAV ''B'', sAV ''A'', sMV ''Text9'',
                  PEnc <| sC ''isoiec_9798_2_6_special_TTP_enc_5'', sN ''Rb'', sMV ''Rpa'',
                          sMV ''Text8''
                       |>
                       ( sMV ''Kab'' )
               |>
  ]"

role isoiec_9798_2_6_special_TTP_bdkey_P
where "isoiec_9798_2_6_special_TTP_bdkey_P =
  [ Recv ''2'' <| sMV ''A'', sAV ''P'', sMV ''Ra'', sMV ''Rb'', sMV ''B'',
                  sMV ''Text2''
               |>
  , Recv ''text_3'' <| sMV ''Text3'', sMV ''Text4'', sMV ''Text5'' |>
  , Send ''3'' <| sAV ''P'', sMV ''A'', sMV ''Text5'',
                  PEnc <| sC ''isoiec_9798_2_6_special_TTP_enc_3_1'', sMV ''Ra'',
                          sN ''Kab'', sMV ''B'', sMV ''Text4''
                       |>
                       ( sKbd (MVar ''A'') (AVar ''P'') ),
                  PEnc <| sC ''isoiec_9798_2_6_special_TTP_enc_3_2'', sMV ''Rb'',
                          sN ''Kab'', sMV ''A'', sMV ''Text3''
                       |>
                       ( sKbd (MVar ''B'') (AVar ''P'') )
               |>
  ]"

protocol isoiec_9798_2_6_special_TTP_bdkey
where "isoiec_9798_2_6_special_TTP_bdkey =
{ isoiec_9798_2_6_special_TTP_bdkey_A,
  isoiec_9798_2_6_special_TTP_bdkey_B, isoiec_9798_2_6_special_TTP_bdkey_P
}"

locale restricted_isoiec_9798_2_6_special_TTP_bdkey_state = isoiec_9798_2_6_special_TTP_bdkey_state +
  assumes different_actors_A_P:
    "!! tid0 tid1.
       [| roleMap r tid0 = Some isoiec_9798_2_6_special_TTP_bdkey_A;
         roleMap r tid1 = Some isoiec_9798_2_6_special_TTP_bdkey_P;
         s(AV ''P'' tid1) = s(AV ''A'' tid0)
       |] ==> False"
  assumes different_actors_B_P:
    "!! tid0 tid1.
       [| roleMap r tid0 = Some isoiec_9798_2_6_special_TTP_bdkey_B;
         roleMap r tid1 = Some isoiec_9798_2_6_special_TTP_bdkey_P;
         s(AV ''P'' tid1) = s(AV ''B'' tid0)
       |] ==> False"

type_invariant isoiec_9798_2_6_special_TTP_bdkey_msc_typing for isoiec_9798_2_6_special_TTP_bdkey
where "isoiec_9798_2_6_special_TTP_bdkey_msc_typing = mk_typing
  [ ((isoiec_9798_2_6_special_TTP_bdkey_P, ''A''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_P_2))
  , ((isoiec_9798_2_6_special_TTP_bdkey_A, ''B''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_A_1))
  , ((isoiec_9798_2_6_special_TTP_bdkey_P, ''B''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_P_2))
  , ((isoiec_9798_2_6_special_TTP_bdkey_A, ''Kab''),
     (SumT (KnownT isoiec_9798_2_6_special_TTP_bdkey_A_3) (NonceT isoiec_9798_2_6_special_TTP_bdkey_P ''Kab'')))
  , ((isoiec_9798_2_6_special_TTP_bdkey_B, ''Kab''),
     (SumT (KnownT isoiec_9798_2_6_special_TTP_bdkey_B_4) (NonceT isoiec_9798_2_6_special_TTP_bdkey_P ''Kab'')))
  , ((isoiec_9798_2_6_special_TTP_bdkey_B, ''P''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_B_4))
  , ((isoiec_9798_2_6_special_TTP_bdkey_P, ''Ra''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_P_2))
  , ((isoiec_9798_2_6_special_TTP_bdkey_A, ''Rb''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_A_1))
  , ((isoiec_9798_2_6_special_TTP_bdkey_P, ''Rb''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_P_2))
  , ((isoiec_9798_2_6_special_TTP_bdkey_B, ''Rpa''),
     (SumT (KnownT isoiec_9798_2_6_special_TTP_bdkey_B_4) (NonceT isoiec_9798_2_6_special_TTP_bdkey_A ''Rpa'')))
  , ((isoiec_9798_2_6_special_TTP_bdkey_A, ''Text1''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_A_1))
  , ((isoiec_9798_2_6_special_TTP_bdkey_B, ''Text1''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_B_text_1))
  , ((isoiec_9798_2_6_special_TTP_bdkey_A, ''Text2''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_A_text_2))
  , ((isoiec_9798_2_6_special_TTP_bdkey_P, ''Text2''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_P_2))
  , ((isoiec_9798_2_6_special_TTP_bdkey_B, ''Text3''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_B_4))
  , ((isoiec_9798_2_6_special_TTP_bdkey_P, ''Text3''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_P_text_3))
  , ((isoiec_9798_2_6_special_TTP_bdkey_A, ''Text4''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_A_3))
  , ((isoiec_9798_2_6_special_TTP_bdkey_P, ''Text4''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_P_text_3))
  , ((isoiec_9798_2_6_special_TTP_bdkey_A, ''Text5''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_A_3))
  , ((isoiec_9798_2_6_special_TTP_bdkey_P, ''Text5''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_P_text_3))
  , ((isoiec_9798_2_6_special_TTP_bdkey_A, ''Text6''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_A_text_4))
  , ((isoiec_9798_2_6_special_TTP_bdkey_B, ''Text6''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_B_4))
  , ((isoiec_9798_2_6_special_TTP_bdkey_A, ''Text7''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_A_text_4))
  , ((isoiec_9798_2_6_special_TTP_bdkey_B, ''Text7''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_B_4))
  , ((isoiec_9798_2_6_special_TTP_bdkey_A, ''Text8''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_A_5))
  , ((isoiec_9798_2_6_special_TTP_bdkey_B, ''Text8''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_B_text_5))
  , ((isoiec_9798_2_6_special_TTP_bdkey_A, ''Text9''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_A_5))
  , ((isoiec_9798_2_6_special_TTP_bdkey_B, ''Text9''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_B_text_5))
  , ((isoiec_9798_2_6_special_TTP_bdkey_A, ''TokenPA_for_B''),
     (KnownT isoiec_9798_2_6_special_TTP_bdkey_A_3))
  ]"

sublocale isoiec_9798_2_6_special_TTP_bdkey_state < isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_2_6_special_TTP_bdkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_2_6_special_TTP_bdkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_2_6_special_TTP_bdkey_A_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_A_1_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_A_3_Kab t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_3_1'', LN ''Ra'' tid0,
               s(MV ''Kab'' tid0), s(MV ''B'' tid0), s(MV ''Text4'' tid0)
            |}
            ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_A_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_3_1'', LN ''Ra'' tid0,
               s(MV ''Kab'' tid0), s(MV ''B'' tid0), s(MV ''Text4'' tid0)
            |}
            ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_A_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_A_3_TokenPA_for_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_A_text_4_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_A_text_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_A_5_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_5'', s(MV ''Rb'' tid0),
               LN ''Rpa'' tid0, s(MV ''Text8'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_A_5_Text9 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_B_4_Kab t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_3_2'', LN ''Rb'' tid0,
               s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''Text3'' tid0)
            |}
            ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_B_4_P t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_B_4_Rpa t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_4'', s(MV ''Rpa'' tid0),
               LN ''Rb'' tid0, s(MV ''Text6'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_B_4_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_3_2'', LN ''Rb'' tid0,
               s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''Text3'' tid0)
            |}
            ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_B_4_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_4'', s(MV ''Rpa'' tid0),
               LN ''Rb'' tid0, s(MV ''Text6'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_B_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_B_text_5_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_B_text_5_Text9 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_P_2_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_P_2_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_P_2_Ra t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_P_2_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_P_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_P_text_3_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_P_text_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_P_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_2_6_special_TTP_bdkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_2_6_special_TTP_bdkey_state begin

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



lemma (in restricted_isoiec_9798_2_6_special_TTP_bdkey_state) P_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_6_special_TTP_bdkey_P"
    "RLKR(s(AV ''P'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "LN ''Kab'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''Kab'' tid0 ")
  case isoiec_9798_2_6_special_TTP_bdkey_P_3_Kab note_unified facts = this facts
  thus ?thesis by (fastforce dest!: ltk_secrecy)
next
  case isoiec_9798_2_6_special_TTP_bdkey_P_3_Kab_1 note_unified facts = this facts
  thus ?thesis by (fastforce dest!: ltk_secrecy)
qed (insert facts, fastforce+)?

lemma (in restricted_isoiec_9798_2_6_special_TTP_bdkey_state) A_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_6_special_TTP_bdkey_A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''P'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_6_special_TTP_bdkey_A_3 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_3_1'', LN ''Ra'' tid0,
                          s(MV ''Kab'' tid0), s(MV ''B'' tid0), s(MV ''Text4'' tid0)
                       |}
                       ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_P_3_enc tid1) note_unified facts = this facts
    hence "Kbd ( s(AV ''P'' tid1) )
               ( s(MV ''A'' tid1) ) = Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) )"
      by simp note facts = this facts
    thus ?thesis proof(cases rule: Kbd_cases)
      case noswap note_unified facts = this facts
      thus ?thesis by (fastforce dest: different_actors_A_P intro: event_predOrdI)
    next
      case swapped note_unified facts = this facts
      thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
    qed (fastforce+)?
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_isoiec_9798_2_6_special_TTP_bdkey_state) B_secret_Kab:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_2_6_special_TTP_bdkey_B"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''P'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_2_6_special_TTP_bdkey_B_4 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_3_2'', LN ''Rb'' tid0,
                          s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''Text3'' tid0)
                       |}
                       ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_6_special_TTP_bdkey_P_3_enc_1 tid1) note_unified facts = this facts
    hence "Kbd ( s(AV ''P'' tid1) )
               ( s(MV ''B'' tid1) ) = Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) )"
      by simp note facts = this facts
    thus ?thesis proof(cases rule: Kbd_cases)
      case noswap note_unified facts = this facts
      thus ?thesis by (fastforce dest: different_actors_B_P intro: event_predOrdI)
    next
      case swapped note_unified facts = this facts
      thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
    qed (fastforce+)?
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_isoiec_9798_2_6_special_TTP_bdkey_state) A_injective_agreement_B:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_6_special_TTP_bdkey_A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''P'' tid0)) ~: reveals t &
          RLKR(s(MV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_6_special_TTP_bdkey_A_5 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_6_special_TTP_bdkey_B &
          ( tid1, isoiec_9798_2_6_special_TTP_bdkey_B_5 ) : steps t &
          {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(MV ''P'' tid1),
             s(MV ''Kab'' tid1), s(MV ''Rpa'' tid1), LN ''Rb'' tid1,
             s(MV ''Text6'' tid1), s(MV ''Text8'' tid1)
          |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), s(AV ''P'' tid0),
                  s(MV ''Kab'' tid0), LN ''Rpa'' tid0, s(MV ''Rb'' tid0),
                  s(MV ''Text6'' tid0), s(MV ''Text8'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_3_1'', LN ''Ra'' tid0,
                              s(MV ''Kab'' tid0), s(MV ''B'' tid0), s(MV ''Text4'' tid0)
                           |}
                           ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_6_special_TTP_bdkey_P_3_enc tid1) note_unified facts = this facts
        hence "Kbd ( s(AV ''P'' tid1) )
                   ( s(MV ''A'' tid1) ) = Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) )"
          by simp note facts = this facts
        thus ?thesis proof(cases rule: Kbd_cases)
          case noswap note_unified facts = this facts
          thus ?thesis by (fastforce dest: different_actors_A_P intro: event_predOrdI)
        next
          case swapped note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_5'', s(MV ''Rb'' tid0),
                                  LN ''Rpa'' tid0, s(MV ''Text8'' tid0)
                               |}
                               ( LN ''Kab'' tid1 ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
          next
            case (isoiec_9798_2_6_special_TTP_bdkey_B_5_enc tid2) note_unified facts = this facts
            thus ?thesis proof(sources! "
                             Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_3_2'', LN ''Rb'' tid2,
                                    LN ''Kab'' tid1, s(AV ''A'' tid2), s(MV ''Text3'' tid2)
                                 |}
                                 ( Kbd ( s(AV ''B'' tid2) ) ( s(MV ''P'' tid2) ) ) ")
              case fake note_unified facts = this facts
              thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
            next
              case (isoiec_9798_2_6_special_TTP_bdkey_P_3_enc_1 tid3) note_unified facts = this facts
              hence "Kbd ( s(AV ''P'' tid0) )
                         ( s(MV ''B'' tid0) ) = Kbd ( s(AV ''B'' tid2) ) ( s(MV ''P'' tid2) )"
                by simp note facts = this facts
              thus ?thesis proof(cases rule: Kbd_cases)
                case noswap note_unified facts = this facts
                thus ?thesis by (fastforce dest: different_actors_B_P intro: event_predOrdI)
              next
                case swapped note_unified facts = this facts
                thus ?thesis proof(sources! "
                                 Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_4'', LN ''Rpa'' tid0,
                                        LN ''Rb'' tid2, s(MV ''Text6'' tid2)
                                     |}
                                     ( LN ''Kab'' tid1 ) ")
                  case fake note_unified facts = this facts
                  thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
                next
                  case (isoiec_9798_2_6_special_TTP_bdkey_A_4_enc tid3) note_unified facts = this facts
                  thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
                qed (insert facts, fastforce+)?
              qed (fastforce+)?
            qed (insert facts, fastforce+)?
          qed (insert facts, fastforce+)?
        qed (fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_2_6_special_TTP_bdkey_state) B_injective_agreement_A:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_6_special_TTP_bdkey_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          RLKR(s(MV ''P'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_6_special_TTP_bdkey_B_4 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_6_special_TTP_bdkey_A &
          ( tid1, isoiec_9798_2_6_special_TTP_bdkey_A_4 ) : steps t &
          {| s(AV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1),
             s(MV ''Kab'' tid1), LN ''Rpa'' tid1, s(MV ''Rb'' tid1),
             s(MV ''Text6'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''P'' tid0),
                  s(MV ''Kab'' tid0), s(MV ''Rpa'' tid0), LN ''Rb'' tid0,
                  s(MV ''Text6'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_3_2'', LN ''Rb'' tid0,
                              s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''Text3'' tid0)
                           |}
                           ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_6_special_TTP_bdkey_P_3_enc_1 tid1) note_unified facts = this facts
        hence "Kbd ( s(AV ''P'' tid1) )
                   ( s(MV ''B'' tid1) ) = Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) )"
          by simp note facts = this facts
        thus ?thesis proof(cases rule: Kbd_cases)
          case noswap note_unified facts = this facts
          thus ?thesis by (fastforce dest: different_actors_B_P intro: event_predOrdI)
        next
          case swapped note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_4'', s(MV ''Rpa'' tid0),
                                  LN ''Rb'' tid0, s(MV ''Text6'' tid0)
                               |}
                               ( LN ''Kab'' tid1 ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
          next
            case (isoiec_9798_2_6_special_TTP_bdkey_A_4_enc tid2) note_unified facts = this facts
            thus ?thesis proof(sources! "
                             Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_3_1'', LN ''Ra'' tid2,
                                    LN ''Kab'' tid1, s(MV ''B'' tid2), s(MV ''Text4'' tid2)
                                 |}
                                 ( Kbd ( s(AV ''A'' tid2) ) ( s(AV ''P'' tid2) ) ) ")
              case fake note_unified facts = this facts
              thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
            next
              case (isoiec_9798_2_6_special_TTP_bdkey_P_3_enc tid3) note_unified facts = this facts
              hence "Kbd ( s(AV ''A'' tid2) )
                         ( s(AV ''P'' tid2) ) = Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid1) )"
                by simp note facts = this facts
              thus ?thesis proof(cases rule: Kbd_cases)
                case noswap note_unified facts = this facts
                thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
              next
                case swapped note_unified facts = this facts
                thus ?thesis by (fastforce dest: different_actors_A_P intro: event_predOrdI)
              qed (fastforce+)?
            qed (insert facts, fastforce+)?
          qed (insert facts, fastforce+)?
        qed (fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_2_6_special_TTP_bdkey_state) A_injective_agreement_P:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_6_special_TTP_bdkey_A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''P'' tid0)) ~: reveals t &
          RLKR(s(MV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_6_special_TTP_bdkey_A_3 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_6_special_TTP_bdkey_P &
          ( tid1, isoiec_9798_2_6_special_TTP_bdkey_P_3 ) : steps t &
          {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1),
             s(MV ''Ra'' tid1), LN ''Kab'' tid1, s(MV ''Text4'' tid1)
          |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), s(AV ''P'' tid0),
                  LN ''Ra'' tid0, s(MV ''Kab'' tid0), s(MV ''Text4'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_3_1'', LN ''Ra'' tid0,
                              s(MV ''Kab'' tid0), s(MV ''B'' tid0), s(MV ''Text4'' tid0)
                           |}
                           ( Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_6_special_TTP_bdkey_P_3_enc tid1) note_unified facts = this facts
        hence "Kbd ( s(AV ''P'' tid1) )
                   ( s(MV ''A'' tid1) ) = Kbd ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) )"
          by simp note facts = this facts
        thus ?thesis proof(cases rule: Kbd_cases)
          case noswap note_unified facts = this facts
          thus ?thesis by (fastforce dest: different_actors_A_P intro: event_predOrdI)
        next
          case swapped note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_2_6_special_TTP_bdkey_state) B_injective_agreement_P:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_6_special_TTP_bdkey_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          RLKR(s(MV ''P'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_6_special_TTP_bdkey_B_4 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_6_special_TTP_bdkey_P &
          ( tid1, isoiec_9798_2_6_special_TTP_bdkey_P_3 ) : steps t &
          {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1),
             s(MV ''Rb'' tid1), LN ''Kab'' tid1, s(MV ''Text3'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''P'' tid0),
                  LN ''Rb'' tid0, s(MV ''Kab'' tid0), s(MV ''Text3'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_6_special_TTP_enc_3_2'', LN ''Rb'' tid0,
                              s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''Text3'' tid0)
                           |}
                           ( Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_6_special_TTP_bdkey_P_3_enc_1 tid1) note_unified facts = this facts
        hence "Kbd ( s(AV ''P'' tid1) )
                   ( s(MV ''B'' tid1) ) = Kbd ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) )"
          by simp note facts = this facts
        thus ?thesis proof(cases rule: Kbd_cases)
          case noswap note_unified facts = this facts
          thus ?thesis by (fastforce dest: different_actors_B_P intro: event_predOrdI)
        next
          case swapped note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

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
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_1_udkey_A_text_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_1_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_1_udkey_B_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_1_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_1_udkey_B_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_1_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_1_udkey_A_1_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (insert facts, fastforce+)?
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
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_2_udkey_A_1_RB t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_2_udkey_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_2_udkey_A_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_2_udkey_A_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_2_udkey_B_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_2_enc_2'', LN ''RB'' tid0, s(MV ''Text2'' tid0)
            |}
            ( K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_2_udkey_B_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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

lemma (in restricted_isoiec_9798_2_2_udkey_state) B_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_2_udkey_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_2_udkey_B_2 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_2_udkey_A &
          ( tid1, isoiec_9798_2_2_udkey_A_2 ) : steps t &
          {| s(AV ''A'' tid1), s(MV ''B'' tid1), s(MV ''RB'' tid1),
             s(MV ''Text2'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), LN ''RB'' tid0,
                  s(MV ''Text2'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_2_enc_2'', LN ''RB'' tid0, s(MV ''Text2'' tid0)
                           |}
                           ( K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_2_udkey_A_2_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
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
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_3_udkey_A_text_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_3_udkey_A_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_3_udkey_B_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_3_udkey_B_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_3_udkey_B_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_3_udkey_B_text_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_3_udkey_B_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (insert facts, fastforce+)?
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
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_3_udkey_A_1_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (insert facts, fastforce+)?
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
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_udkey_A_1_RB t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_udkey_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_udkey_A_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_udkey_A_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_4_udkey_A_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_4_udkey_B_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_udkey_B_text_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_4_udkey_B_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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

lemma (in restricted_isoiec_9798_2_4_udkey_state) A_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_4_udkey_A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(MV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_4_udkey_A_3 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_4_udkey_B &
          ( tid1, isoiec_9798_2_4_udkey_B_3 ) : steps t &
          {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(MV ''RA'' tid1), LN ''RB'' tid1,
             s(MV ''Text2'' tid1), s(MV ''Text4'' tid1)
          |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), LN ''RA'' tid0,
                  s(MV ''RB'' tid0), s(MV ''Text2'' tid0), s(MV ''Text4'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_4_enc_2'', s(MV ''RB'' tid0), LN ''RA'' tid0,
                              s(MV ''Text4'' tid0)
                           |}
                           ( K ( s(MV ''B'' tid0) ) ( s(AV ''A'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_4_udkey_B_3_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_2_4_enc_1'', LN ''RA'' tid0, LN ''RB'' tid1,
                                s(MV ''Text2'' tid1)
                             |}
                             ( K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid1) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest!: ltk_secrecy)
        next
          case (isoiec_9798_2_4_udkey_A_2_enc tid2) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_2_4_udkey_state) B_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_4_udkey_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_4_udkey_B_2 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_4_udkey_A &
          ( tid1, isoiec_9798_2_4_udkey_A_2 ) : steps t &
          {| s(AV ''A'' tid1), s(MV ''B'' tid1), LN ''RA'' tid1, s(MV ''RB'' tid1),
             s(MV ''Text2'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''RA'' tid0),
                  LN ''RB'' tid0, s(MV ''Text2'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_4_enc_1'', s(MV ''RA'' tid0), LN ''RB'' tid0,
                              s(MV ''Text2'' tid0)
                           |}
                           ( K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_4_udkey_A_2_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_udkey_A_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_A_2_TokenPA_for_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_A_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_A_text_3_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_udkey_A_4_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_B_3_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_udkey_B_3_P t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_5_udkey_B_3_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_B_text_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_B_text_4_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_P_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_P_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_P_1_TVPa t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_P_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_P_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_P_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_5_udkey_P_text_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_5_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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
  thus ?thesis by (fastforce dest!: ltk_secrecy)
next
  case isoiec_9798_2_5_udkey_P_2_Kab_1 note_unified facts = this facts
  thus ?thesis by (fastforce dest!: ltk_secrecy)
qed (insert facts, fastforce+)?

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
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_5_udkey_P_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
  qed (insert facts, fastforce+)?
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
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_5_udkey_P_2_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_isoiec_9798_2_5_udkey_state) A_injective_agreement_B:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_5_udkey_A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          RLKR(s(AV ''P'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_5_udkey_A_4 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_5_udkey_B &
          ( tid1, isoiec_9798_2_5_udkey_B_4 ) : steps t &
          {| s(MV ''A'' tid1), s(AV ''B'' tid1), s(MV ''P'' tid1),
             s(MV ''Kab'' tid1), s(MV ''TNa'' tid1), s(MV ''Text5'' tid1),
             LN ''TNb'' tid1, s(MV ''Text7'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(AV ''P'' tid0),
                  s(MV ''Kab'' tid0), LN ''TNa'' tid0, s(MV ''Text5'' tid0),
                  s(MV ''TNb'' tid0), s(MV ''Text7'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid0,
                              s(MV ''Kab'' tid0), s(AV ''B'' tid0), s(MV ''Text3'' tid0)
                           |}
                           ( K ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_5_udkey_P_2_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_2_5_enc_4'', s(MV ''TNb'' tid0),
                                s(AV ''A'' tid0), s(MV ''Text7'' tid0)
                             |}
                             ( LN ''Kab'' tid1 ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
        next
          case (isoiec_9798_2_5_udkey_B_4_enc tid2) note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''isoiec_9798_2_5_enc_2_2'', s(MV ''TNp'' tid2),
                                  LN ''Kab'' tid1, s(AV ''A'' tid0), s(MV ''Text2'' tid2)
                               |}
                               ( K ( s(AV ''B'' tid2) ) ( s(MV ''P'' tid2) ) ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
          next
            case (isoiec_9798_2_5_udkey_P_2_enc_1 tid3) note_unified facts = this facts
            thus ?thesis proof(sources! "
                             Enc {| LC ''isoiec_9798_2_5_enc_3'', s(MV ''TNa'' tid2),
                                    s(AV ''B'' tid0), s(MV ''Text5'' tid2)
                                 |}
                                 ( LN ''Kab'' tid1 ) ")
              case fake note_unified facts = this facts
              thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
            next
              case (isoiec_9798_2_5_udkey_A_3_enc tid3) note_unified facts = this facts
              thus ?thesis proof(sources! "
                               Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid3, LN ''Kab'' tid1,
                                      s(AV ''B'' tid0), s(MV ''Text3'' tid3)
                                   |}
                                   ( K ( s(AV ''A'' tid3) ) ( s(AV ''P'' tid3) ) ) ")
                case fake note_unified facts = this facts
                thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
              next
                case (isoiec_9798_2_5_udkey_P_2_enc tid4) note_unified facts = this facts
                thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
              qed (insert facts, fastforce+)?
            qed (insert facts, fastforce+)?
          qed (insert facts, fastforce+)?
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
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
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_5_udkey_P_2_enc_1 tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''isoiec_9798_2_5_enc_3'', s(MV ''TNa'' tid0),
                            s(AV ''B'' tid0), s(MV ''Text5'' tid0)
                         |}
                         ( LN ''Kab'' tid1 ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
    next
      case (isoiec_9798_2_5_udkey_A_3_enc tid2) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid2, LN ''Kab'' tid1,
                              s(AV ''B'' tid0), s(MV ''Text3'' tid2)
                           |}
                           ( K ( s(AV ''A'' tid2) ) ( s(AV ''P'' tid2) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
      next
        case (isoiec_9798_2_5_udkey_P_2_enc tid3) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed (insert facts, fastforce+)?
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_isoiec_9798_2_5_udkey_state) A_injective_agreement_P:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_5_udkey_A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          RLKR(s(AV ''P'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_5_udkey_A_2 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_5_udkey_P &
          ( tid1, isoiec_9798_2_5_udkey_P_2 ) : steps t &
          {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1), LN ''Kab'' tid1,
             s(MV ''TVPa'' tid1), s(MV ''Text3'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(AV ''P'' tid0),
                  s(MV ''Kab'' tid0), LN ''TVPa'' tid0, s(MV ''Text3'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_5_enc_2_1'', LN ''TVPa'' tid0,
                              s(MV ''Kab'' tid0), s(AV ''B'' tid0), s(MV ''Text3'' tid0)
                           |}
                           ( K ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_5_udkey_P_2_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
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
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_5_udkey_P_2_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (insert facts, fastforce+)?
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
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_A_1_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_udkey_A_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_A_3_TokenPA_for_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_A_text_4_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_A_text_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_udkey_A_5_Text9 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_udkey_B_4_P t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
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
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_2_6_udkey_B_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_B_text_5_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_B_text_5_Text9 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_P_2_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_P_2_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_P_2_Ra t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_P_2_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_P_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_P_text_3_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_P_text_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_2_6_udkey_P_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_2_6_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
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
  thus ?thesis by (fastforce dest!: ltk_secrecy)
next
  case isoiec_9798_2_6_udkey_P_3_Kab_1 note_unified facts = this facts
  thus ?thesis by (fastforce dest!: ltk_secrecy)
qed (insert facts, fastforce+)?

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
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_6_udkey_P_3_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
  qed (insert facts, fastforce+)?
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
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_2_6_udkey_P_3_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_isoiec_9798_2_6_udkey_state) A_injective_agreement_B:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_6_udkey_A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''P'' tid0)) ~: reveals t &
          RLKR(s(MV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_6_udkey_A_5 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_6_udkey_B &
          ( tid1, isoiec_9798_2_6_udkey_B_5 ) : steps t &
          {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(MV ''P'' tid1),
             s(MV ''Kab'' tid1), s(MV ''Rpa'' tid1), LN ''Rb'' tid1,
             s(MV ''Text6'' tid1), s(MV ''Text8'' tid1)
          |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), s(AV ''P'' tid0),
                  s(MV ''Kab'' tid0), LN ''Rpa'' tid0, s(MV ''Rb'' tid0),
                  s(MV ''Text6'' tid0), s(MV ''Text8'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid0,
                              s(MV ''Kab'' tid0), s(MV ''B'' tid0), s(MV ''Text4'' tid0)
                           |}
                           ( K ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_6_udkey_P_3_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_2_6_enc_5'', s(MV ''Rb'' tid0), LN ''Rpa'' tid0,
                                s(MV ''Text8'' tid0)
                             |}
                             ( LN ''Kab'' tid1 ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
        next
          case (isoiec_9798_2_6_udkey_B_5_enc tid2) note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid2, LN ''Kab'' tid1,
                                  s(AV ''A'' tid2), s(MV ''Text3'' tid2)
                               |}
                               ( K ( s(AV ''B'' tid2) ) ( s(MV ''P'' tid2) ) ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
          next
            case (isoiec_9798_2_6_udkey_P_3_enc_1 tid3) note_unified facts = this facts
            thus ?thesis proof(sources! "
                             Enc {| LC ''isoiec_9798_2_6_enc_4'', LN ''Rpa'' tid0, LN ''Rb'' tid2,
                                    s(MV ''Text6'' tid2)
                                 |}
                                 ( LN ''Kab'' tid1 ) ")
              case fake note_unified facts = this facts
              thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
            next
              case (isoiec_9798_2_6_udkey_A_4_enc tid3) note_unified facts = this facts
              thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
            qed (insert facts, fastforce+)?
          qed (insert facts, fastforce+)?
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_2_6_udkey_state) B_injective_agreement_A:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_6_udkey_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          RLKR(s(MV ''P'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_6_udkey_B_4 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_6_udkey_A &
          ( tid1, isoiec_9798_2_6_udkey_A_4 ) : steps t &
          {| s(AV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1),
             s(MV ''Kab'' tid1), LN ''Rpa'' tid1, s(MV ''Rb'' tid1),
             s(MV ''Text6'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''P'' tid0),
                  s(MV ''Kab'' tid0), s(MV ''Rpa'' tid0), LN ''Rb'' tid0,
                  s(MV ''Text6'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid0,
                              s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''Text3'' tid0)
                           |}
                           ( K ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_6_udkey_P_3_enc_1 tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_2_6_enc_4'', s(MV ''Rpa'' tid0), LN ''Rb'' tid0,
                                s(MV ''Text6'' tid0)
                             |}
                             ( LN ''Kab'' tid1 ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
        next
          case (isoiec_9798_2_6_udkey_A_4_enc tid2) note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid2, LN ''Kab'' tid1,
                                  s(MV ''B'' tid2), s(MV ''Text4'' tid2)
                               |}
                               ( K ( s(AV ''A'' tid2) ) ( s(AV ''P'' tid2) ) ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest: P_secret_Kab intro: event_predOrdI)
          next
            case (isoiec_9798_2_6_udkey_P_3_enc tid3) note_unified facts = this facts
            thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
          qed (insert facts, fastforce+)?
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_2_6_udkey_state) A_injective_agreement_P:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_6_udkey_A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''P'' tid0)) ~: reveals t &
          RLKR(s(MV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_6_udkey_A_3 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_6_udkey_P &
          ( tid1, isoiec_9798_2_6_udkey_P_3 ) : steps t &
          {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1),
             s(MV ''Ra'' tid1), LN ''Kab'' tid1, s(MV ''Text4'' tid1)
          |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), s(AV ''P'' tid0),
                  LN ''Ra'' tid0, s(MV ''Kab'' tid0), s(MV ''Text4'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid0,
                              s(MV ''Kab'' tid0), s(MV ''B'' tid0), s(MV ''Text4'' tid0)
                           |}
                           ( K ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_6_udkey_P_3_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_2_6_udkey_state) B_injective_agreement_P:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_2_6_udkey_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          RLKR(s(MV ''P'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_2_6_udkey_B_4 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_2_6_udkey_P &
          ( tid1, isoiec_9798_2_6_udkey_P_3 ) : steps t &
          {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''P'' tid1),
             s(MV ''Rb'' tid1), LN ''Kab'' tid1, s(MV ''Text3'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''P'' tid0),
                  LN ''Rb'' tid0, s(MV ''Kab'' tid0), s(MV ''Text3'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid0,
                              s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''Text3'' tid0)
                           |}
                           ( K ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_2_6_udkey_P_3_enc_1 tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

role isoiec_9798_3_1_A
where "isoiec_9798_3_1_A =
  [ Send ''leak_A'' ( sN ''TNA'' )
  , Recv ''text_1'' <| sMV ''Text1'', sMV ''Text2'' |>
  , Send ''1'' <| sAV ''A'', sAV ''B'', sMV ''Text2'',
                  PSign <| sC ''isoiec_9798_3_1_sig_1'', sN ''TNA'', sAV ''B'',
                           sMV ''Text1''
                        |>
                        ( sPK ''A'' )
               |>
  ]"

role isoiec_9798_3_1_B
where "isoiec_9798_3_1_B =
  [ Recv ''1'' <| sMV ''A'', sAV ''B'', sMV ''Text2'',
                  PSign <| sC ''isoiec_9798_3_1_sig_1'', sMV ''TNA'', sAV ''B'',
                           sMV ''Text1''
                        |>
                        ( PAsymPK ( sMV ''A'' ) )
               |>
  ]"

protocol isoiec_9798_3_1
where "isoiec_9798_3_1 = { isoiec_9798_3_1_A, isoiec_9798_3_1_B }"

locale restricted_isoiec_9798_3_1_state = isoiec_9798_3_1_state

type_invariant isoiec_9798_3_1_msc_typing for isoiec_9798_3_1
where "isoiec_9798_3_1_msc_typing = mk_typing
  [ ((isoiec_9798_3_1_B, ''A''), (KnownT isoiec_9798_3_1_B_1))
  , ((isoiec_9798_3_1_B, ''TNA''), (KnownT isoiec_9798_3_1_B_1))
  , ((isoiec_9798_3_1_A, ''Text1''), (KnownT isoiec_9798_3_1_A_text_1))
  , ((isoiec_9798_3_1_B, ''Text1''), (KnownT isoiec_9798_3_1_B_1))
  , ((isoiec_9798_3_1_A, ''Text2''), (KnownT isoiec_9798_3_1_A_text_1))
  , ((isoiec_9798_3_1_B, ''Text2''), (KnownT isoiec_9798_3_1_B_1))
  ]"

sublocale isoiec_9798_3_1_state < isoiec_9798_3_1_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_3_1_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_3_1_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_3_1_A_text_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_1_A_text_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_1_B_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_1_B_1_TNA t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_1_B_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_1_B_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_3_1_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_3_1_state begin

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

lemma (in restricted_isoiec_9798_3_1_state) B_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_3_1_B"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_3_1_B_1 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_3_1_A &
        ( tid1, isoiec_9798_3_1_A_1 ) : steps t &
        {| s(AV ''A'' tid1), s(AV ''B'' tid1), LN ''TNA'' tid1,
           s(MV ''Text1'' tid1)
        |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''TNA'' tid0),
                s(MV ''Text1'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_3_1_sig_1'', s(MV ''TNA'' tid0),
                          s(AV ''B'' tid0), s(MV ''Text1'' tid0)
                       |}
                       ( SK ( s(MV ''A'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_3_1_A_1_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (insert facts, fastforce+)?
qed

role isoiec_9798_3_2_A
where "isoiec_9798_3_2_A =
  [ Recv ''1'' <| sMV ''B'', sAV ''A'', sMV ''Rb'', sMV ''Text1'' |>
  , Recv ''text_2'' <| sMV ''Text2'', sMV ''Text3'' |>
  , Send ''2'' <| sAV ''A'', sMV ''B'', sMV ''Text3'',
                  PSign <| sC ''isoiec_9798_3_2_sig_2'', sN ''Ra'', sMV ''Rb'', sMV ''B'',
                           sMV ''Text2''
                        |>
                        ( sPK ''A'' )
               |>
  ]"

role isoiec_9798_3_2_B
where "isoiec_9798_3_2_B =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''B'', sAV ''A'', sN ''Rb'', sMV ''Text1'' |>
  , Recv ''2'' <| sAV ''A'', sAV ''B'', sMV ''Text3'',
                  PSign <| sC ''isoiec_9798_3_2_sig_2'', sMV ''Ra'', sN ''Rb'', sAV ''B'',
                           sMV ''Text2''
                        |>
                        ( sPK ''A'' )
               |>
  ]"

protocol isoiec_9798_3_2
where "isoiec_9798_3_2 = { isoiec_9798_3_2_A, isoiec_9798_3_2_B }"

locale restricted_isoiec_9798_3_2_state = isoiec_9798_3_2_state

type_invariant isoiec_9798_3_2_msc_typing for isoiec_9798_3_2
where "isoiec_9798_3_2_msc_typing = mk_typing
  [ ((isoiec_9798_3_2_A, ''B''), (KnownT isoiec_9798_3_2_A_1))
  , ((isoiec_9798_3_2_B, ''Ra''), (KnownT isoiec_9798_3_2_B_2))
  , ((isoiec_9798_3_2_A, ''Rb''), (KnownT isoiec_9798_3_2_A_1))
  , ((isoiec_9798_3_2_A, ''Text1''), (KnownT isoiec_9798_3_2_A_1))
  , ((isoiec_9798_3_2_B, ''Text1''), (KnownT isoiec_9798_3_2_B_text_1))
  , ((isoiec_9798_3_2_A, ''Text2''), (KnownT isoiec_9798_3_2_A_text_2))
  , ((isoiec_9798_3_2_B, ''Text2''), (KnownT isoiec_9798_3_2_B_2))
  , ((isoiec_9798_3_2_A, ''Text3''), (KnownT isoiec_9798_3_2_A_text_2))
  , ((isoiec_9798_3_2_B, ''Text3''), (KnownT isoiec_9798_3_2_B_2))
  ]"

sublocale isoiec_9798_3_2_state < isoiec_9798_3_2_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_3_2_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_3_2_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_3_2_A_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_2_A_1_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_2_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_2_A_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_2_A_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_2_B_2_Ra t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_2_B_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_2_B_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_3_2_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_3_2_state begin

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

lemma (in restricted_isoiec_9798_3_2_state) B_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_2_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_2_B_2 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_2_A &
          ( tid1, isoiec_9798_3_2_A_2 ) : steps t &
          {| s(AV ''A'' tid1), s(MV ''B'' tid1), LN ''Ra'' tid1, s(MV ''Rb'' tid1),
             s(MV ''Text2'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''Ra'' tid0),
                  LN ''Rb'' tid0, s(MV ''Text2'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_3_2_sig_2'', s(MV ''Ra'' tid0), LN ''Rb'' tid0,
                              s(AV ''B'' tid0), s(MV ''Text2'' tid0)
                           |}
                           ( SK ( s(AV ''A'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_2_A_2_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

role isoiec_9798_3_3_A
where "isoiec_9798_3_3_A =
  [ Send ''leak_A'' ( sN ''TNA'' )
  , Recv ''text_1'' <| sMV ''Text1'', sMV ''Text2'' |>
  , Send ''1'' <| sAV ''A'', sAV ''B'', sMV ''Text2'',
                  PSign <| sC ''isoiec_9798_3_3_sig_1'', sN ''TNA'', sAV ''B'',
                           sMV ''Text1''
                        |>
                        ( sPK ''A'' )
               |>
  , Recv ''2'' <| sAV ''A'', sAV ''B'', sMV ''Text4'',
                  PSign <| sC ''isoiec_9798_3_3_sig_2'', sMV ''TNB'', sAV ''A'',
                           sMV ''Text3''
                        |>
                        ( sPK ''B'' )
               |>
  ]"

role isoiec_9798_3_3_B
where "isoiec_9798_3_3_B =
  [ Send ''leak_B'' ( sN ''TNB'' )
  , Recv ''1'' <| sMV ''A'', sAV ''B'', sMV ''Text2'',
                  PSign <| sC ''isoiec_9798_3_3_sig_1'', sMV ''TNA'', sAV ''B'',
                           sMV ''Text1''
                        |>
                        ( PAsymPK ( sMV ''A'' ) )
               |>
  , Recv ''text_2'' <| sMV ''Text3'', sMV ''Text4'' |>
  , Send ''2'' <| sMV ''A'', sAV ''B'', sMV ''Text4'',
                  PSign <| sC ''isoiec_9798_3_3_sig_2'', sN ''TNB'', sMV ''A'',
                           sMV ''Text3''
                        |>
                        ( sPK ''B'' )
               |>
  ]"

protocol isoiec_9798_3_3
where "isoiec_9798_3_3 = { isoiec_9798_3_3_A, isoiec_9798_3_3_B }"

locale restricted_isoiec_9798_3_3_state = isoiec_9798_3_3_state

type_invariant isoiec_9798_3_3_msc_typing for isoiec_9798_3_3
where "isoiec_9798_3_3_msc_typing = mk_typing
  [ ((isoiec_9798_3_3_B, ''A''), (KnownT isoiec_9798_3_3_B_1))
  , ((isoiec_9798_3_3_B, ''TNA''), (KnownT isoiec_9798_3_3_B_1))
  , ((isoiec_9798_3_3_A, ''TNB''), (KnownT isoiec_9798_3_3_A_2))
  , ((isoiec_9798_3_3_A, ''Text1''), (KnownT isoiec_9798_3_3_A_text_1))
  , ((isoiec_9798_3_3_B, ''Text1''), (KnownT isoiec_9798_3_3_B_1))
  , ((isoiec_9798_3_3_A, ''Text2''), (KnownT isoiec_9798_3_3_A_text_1))
  , ((isoiec_9798_3_3_B, ''Text2''), (KnownT isoiec_9798_3_3_B_1))
  , ((isoiec_9798_3_3_A, ''Text3''), (KnownT isoiec_9798_3_3_A_2))
  , ((isoiec_9798_3_3_B, ''Text3''), (KnownT isoiec_9798_3_3_B_text_2))
  , ((isoiec_9798_3_3_A, ''Text4''), (KnownT isoiec_9798_3_3_A_2))
  , ((isoiec_9798_3_3_B, ''Text4''), (KnownT isoiec_9798_3_3_B_text_2))
  ]"

sublocale isoiec_9798_3_3_state < isoiec_9798_3_3_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_3_3_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_3_3_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_3_3_A_text_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_A_text_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_A_2_TNB t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_A_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_A_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_B_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_B_1_TNA t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_B_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_B_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_B_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_B_text_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_3_3_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_3_3_state begin

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

lemma (in restricted_isoiec_9798_3_3_state) A_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_3_3_A"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_3_3_A_2 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_3_3_B &
        ( tid1, isoiec_9798_3_3_B_2 ) : steps t &
        {| s(MV ''A'' tid1), s(AV ''B'' tid1), LN ''TNB'' tid1,
           s(MV ''Text3'' tid1)
        |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''TNB'' tid0),
                s(MV ''Text3'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_3_3_sig_2'', s(MV ''TNB'' tid0),
                          s(AV ''A'' tid0), s(MV ''Text3'' tid0)
                       |}
                       ( SK ( s(AV ''B'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_3_3_B_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_isoiec_9798_3_3_state) B_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_3_3_B"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_3_3_B_1 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_3_3_A &
        ( tid1, isoiec_9798_3_3_A_1 ) : steps t &
        {| s(AV ''A'' tid1), s(AV ''B'' tid1), LN ''TNA'' tid1,
           s(MV ''Text1'' tid1)
        |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''TNA'' tid0),
                s(MV ''Text1'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''isoiec_9798_3_3_sig_1'', s(MV ''TNA'' tid0),
                          s(AV ''B'' tid0), s(MV ''Text1'' tid0)
                       |}
                       ( SK ( s(MV ''A'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_3_3_A_1_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (insert facts, fastforce+)?
qed

role isoiec_9798_3_4_A
where "isoiec_9798_3_4_A =
  [ Recv ''1'' <| sMV ''B'', sAV ''A'', sMV ''RB'', sMV ''Text1'' |>
  , Recv ''text_2'' <| sMV ''Text2'', sMV ''Text3'' |>
  , Send ''2'' <| sAV ''A'', sMV ''B'', sMV ''Text3'',
                  PSign <| sC ''isoiec_9798_3_4_sig_1'', sN ''RA'', sMV ''RB'', sMV ''B'',
                           sMV ''Text2''
                        |>
                        ( sPK ''A'' )
               |>
  , Recv ''3'' <| sMV ''B'', sAV ''A'', sMV ''Text5'',
                  PSign <| sC ''isoiec_9798_3_4_sig_2'', sMV ''RB'', sN ''RA'', sAV ''A'',
                           sMV ''Text4''
                        |>
                        ( PAsymPK ( sMV ''B'' ) )
               |>
  ]"

role isoiec_9798_3_4_B
where "isoiec_9798_3_4_B =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''B'', sAV ''A'', sN ''RB'', sMV ''Text1'' |>
  , Recv ''2'' <| sAV ''A'', sAV ''B'', sMV ''Text3'',
                  PSign <| sC ''isoiec_9798_3_4_sig_1'', sMV ''RA'', sN ''RB'', sAV ''B'',
                           sMV ''Text2''
                        |>
                        ( sPK ''A'' )
               |>
  , Recv ''text_3'' <| sMV ''Text4'', sMV ''Text5'' |>
  , Send ''3'' <| sAV ''B'', sAV ''A'', sMV ''Text5'',
                  PSign <| sC ''isoiec_9798_3_4_sig_2'', sN ''RB'', sMV ''RA'', sAV ''A'',
                           sMV ''Text4''
                        |>
                        ( sPK ''B'' )
               |>
  ]"

protocol isoiec_9798_3_4
where "isoiec_9798_3_4 = { isoiec_9798_3_4_A, isoiec_9798_3_4_B }"

locale restricted_isoiec_9798_3_4_state = isoiec_9798_3_4_state

type_invariant isoiec_9798_3_4_msc_typing for isoiec_9798_3_4
where "isoiec_9798_3_4_msc_typing = mk_typing
  [ ((isoiec_9798_3_4_A, ''B''), (KnownT isoiec_9798_3_4_A_1))
  , ((isoiec_9798_3_4_B, ''RA''), (KnownT isoiec_9798_3_4_B_2))
  , ((isoiec_9798_3_4_A, ''RB''), (KnownT isoiec_9798_3_4_A_1))
  , ((isoiec_9798_3_4_A, ''Text1''), (KnownT isoiec_9798_3_4_A_1))
  , ((isoiec_9798_3_4_B, ''Text1''), (KnownT isoiec_9798_3_4_B_text_1))
  , ((isoiec_9798_3_4_A, ''Text2''), (KnownT isoiec_9798_3_4_A_text_2))
  , ((isoiec_9798_3_4_B, ''Text2''), (KnownT isoiec_9798_3_4_B_2))
  , ((isoiec_9798_3_4_A, ''Text3''), (KnownT isoiec_9798_3_4_A_text_2))
  , ((isoiec_9798_3_4_B, ''Text3''), (KnownT isoiec_9798_3_4_B_2))
  , ((isoiec_9798_3_4_A, ''Text4''), (KnownT isoiec_9798_3_4_A_3))
  , ((isoiec_9798_3_4_B, ''Text4''), (KnownT isoiec_9798_3_4_B_text_3))
  , ((isoiec_9798_3_4_A, ''Text5''), (KnownT isoiec_9798_3_4_A_3))
  , ((isoiec_9798_3_4_B, ''Text5''), (KnownT isoiec_9798_3_4_B_text_3))
  ]"

sublocale isoiec_9798_3_4_state < isoiec_9798_3_4_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_3_4_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_3_4_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_3_4_A_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_A_1_RB t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_A_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_A_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_A_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_A_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_B_2_RA t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_B_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_B_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_B_text_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_B_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_3_4_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_3_4_state begin

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

lemma (in restricted_isoiec_9798_3_4_state) A_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_4_A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(MV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_4_A_3 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_4_B &
          ( tid1, isoiec_9798_3_4_B_3 ) : steps t &
          {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(MV ''RA'' tid1), LN ''RB'' tid1,
             s(MV ''Text2'' tid1), s(MV ''Text4'' tid1)
          |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), LN ''RA'' tid0,
                  s(MV ''RB'' tid0), s(MV ''Text2'' tid0), s(MV ''Text4'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_3_4_sig_2'', s(MV ''RB'' tid0), LN ''RA'' tid0,
                              s(AV ''A'' tid0), s(MV ''Text4'' tid0)
                           |}
                           ( SK ( s(MV ''B'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_4_B_3_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_4_sig_1'', LN ''RA'' tid0, LN ''RB'' tid1,
                                s(AV ''B'' tid1), s(MV ''Text2'' tid1)
                             |}
                             ( SK ( s(AV ''A'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_4_A_2_enc tid2) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_3_4_state) B_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_4_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_4_B_2 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_4_A &
          ( tid1, isoiec_9798_3_4_A_2 ) : steps t &
          {| s(AV ''A'' tid1), s(MV ''B'' tid1), LN ''RA'' tid1, s(MV ''RB'' tid1),
             s(MV ''Text2'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''RA'' tid0),
                  LN ''RB'' tid0, s(MV ''Text2'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_3_4_sig_1'', s(MV ''RA'' tid0), LN ''RB'' tid0,
                              s(AV ''B'' tid0), s(MV ''Text2'' tid0)
                           |}
                           ( SK ( s(AV ''A'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_4_A_2_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

role isoiec_9798_3_5_A
where "isoiec_9798_3_5_A =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''A'', sAV ''B'', sN ''RA'', sMV ''Text1'' |>
  , Recv ''2'' <| sAV ''B'', sAV ''A'', sMV ''RB'', sMV ''Text2'' |>
  , Recv ''3'' <| sAV ''B'', sAV ''A'', sMV ''Text6'',
                  PSign <| sC ''isoiec_9798_3_5_sig_1'', sMV ''RB'', sN ''RA'', sAV ''A'',
                           sMV ''Text5''
                        |>
                        ( sPK ''B'' )
               |>
  , Recv ''text_4'' <| sMV ''Text3'', sMV ''Text4'' |>
  , Send ''4'' <| sAV ''A'', sAV ''B'', sMV ''Text4'',
                  PSign <| sC ''isoiec_9798_3_5_sig_2'', sN ''RA'', sMV ''RB'', sAV ''B'',
                           sMV ''Text3''
                        |>
                        ( sPK ''A'' )
               |>
  ]"

role isoiec_9798_3_5_B
where "isoiec_9798_3_5_B =
  [ Recv ''1'' <| sMV ''A'', sAV ''B'', sMV ''RA'', sMV ''Text1'' |>
  , Recv ''text_2'' ( sMV ''Text2'' )
  , Send ''2'' <| sAV ''B'', sMV ''A'', sN ''RB'', sMV ''Text2'' |>
  , Recv ''text_3'' <| sMV ''Text5'', sMV ''Text6'' |>
  , Send ''3'' <| sAV ''B'', sMV ''A'', sMV ''Text6'',
                  PSign <| sC ''isoiec_9798_3_5_sig_1'', sN ''RB'', sMV ''RA'', sMV ''A'',
                           sMV ''Text5''
                        |>
                        ( sPK ''B'' )
               |>
  , Recv ''4'' <| sMV ''A'', sAV ''B'', sMV ''Text4'',
                  PSign <| sC ''isoiec_9798_3_5_sig_2'', sMV ''RA'', sN ''RB'', sAV ''B'',
                           sMV ''Text3''
                        |>
                        ( PAsymPK ( sMV ''A'' ) )
               |>
  ]"

protocol isoiec_9798_3_5
where "isoiec_9798_3_5 = { isoiec_9798_3_5_A, isoiec_9798_3_5_B }"

locale restricted_isoiec_9798_3_5_state = isoiec_9798_3_5_state

type_invariant isoiec_9798_3_5_msc_typing for isoiec_9798_3_5
where "isoiec_9798_3_5_msc_typing = mk_typing
  [ ((isoiec_9798_3_5_B, ''A''), (KnownT isoiec_9798_3_5_B_1))
  , ((isoiec_9798_3_5_B, ''RA''), (KnownT isoiec_9798_3_5_B_1))
  , ((isoiec_9798_3_5_A, ''RB''), (KnownT isoiec_9798_3_5_A_2))
  , ((isoiec_9798_3_5_A, ''Text1''), (KnownT isoiec_9798_3_5_A_text_1))
  , ((isoiec_9798_3_5_B, ''Text1''), (KnownT isoiec_9798_3_5_B_1))
  , ((isoiec_9798_3_5_A, ''Text2''), (KnownT isoiec_9798_3_5_A_2))
  , ((isoiec_9798_3_5_B, ''Text2''), (KnownT isoiec_9798_3_5_B_text_2))
  , ((isoiec_9798_3_5_A, ''Text3''), (KnownT isoiec_9798_3_5_A_text_4))
  , ((isoiec_9798_3_5_B, ''Text3''), (KnownT isoiec_9798_3_5_B_4))
  , ((isoiec_9798_3_5_A, ''Text4''), (KnownT isoiec_9798_3_5_A_text_4))
  , ((isoiec_9798_3_5_B, ''Text4''), (KnownT isoiec_9798_3_5_B_4))
  , ((isoiec_9798_3_5_A, ''Text5''), (KnownT isoiec_9798_3_5_A_3))
  , ((isoiec_9798_3_5_B, ''Text5''), (KnownT isoiec_9798_3_5_B_text_3))
  , ((isoiec_9798_3_5_A, ''Text6''), (KnownT isoiec_9798_3_5_A_3))
  , ((isoiec_9798_3_5_B, ''Text6''), (KnownT isoiec_9798_3_5_B_text_3))
  ]"

sublocale isoiec_9798_3_5_state < isoiec_9798_3_5_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_3_5_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_3_5_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_3_5_A_2_RB t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_A_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_A_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_A_3_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_A_text_4_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_A_text_4_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_B_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_B_1_RA t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_B_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_B_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_B_text_3_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_B_4_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_B_4_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_3_5_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_3_5_state begin

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

lemma (in restricted_isoiec_9798_3_5_state) A_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_5_A &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_5_A_3 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_5_B &
          ( tid1, isoiec_9798_3_5_B_3 ) : steps t &
          {| s(MV ''A'' tid1), s(AV ''B'' tid1), s(MV ''RA'' tid1), LN ''RB'' tid1,
             s(MV ''Text5'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), LN ''RA'' tid0,
                  s(MV ''RB'' tid0), s(MV ''Text5'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_3_5_sig_1'', s(MV ''RB'' tid0), LN ''RA'' tid0,
                              s(AV ''A'' tid0), s(MV ''Text5'' tid0)
                           |}
                           ( SK ( s(AV ''B'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_5_B_3_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_3_5_state) B_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_5_B &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          RLKR(s(MV ''A'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_5_B_4 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_5_A &
          ( tid1, isoiec_9798_3_5_A_4 ) : steps t &
          {| s(AV ''A'' tid1), s(AV ''B'' tid1), LN ''RA'' tid1, s(MV ''RB'' tid1),
             s(MV ''Text3'' tid1), s(MV ''Text5'' tid1)
          |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''RA'' tid0),
                  LN ''RB'' tid0, s(MV ''Text3'' tid0), s(MV ''Text5'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_3_5_sig_2'', s(MV ''RA'' tid0), LN ''RB'' tid0,
                              s(AV ''B'' tid0), s(MV ''Text3'' tid0)
                           |}
                           ( SK ( s(MV ''A'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_5_A_4_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_5_sig_1'', LN ''RB'' tid0, LN ''RA'' tid1,
                                s(AV ''A'' tid1), s(MV ''Text5'' tid1)
                             |}
                             ( SK ( s(AV ''B'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_5_B_3_enc tid2) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

role isoiec_9798_3_6_1_A
where "isoiec_9798_3_6_1_A =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''A'', sAV ''B'', sN ''Ra'', sMV ''Text1'' |>
  , Recv ''2'' <| sAV ''A'', sAV ''B'', sN ''Ra'', sMV ''Rb'',
                  sMV ''Text3'', sMV ''TokenBA''
               |>
  , Recv ''text_3'' ( sMV ''Text4'' )
  , Send ''3'' <| sAV ''A'', sAV ''T'', sN ''Rpa'', sMV ''Rb'', sAV ''B'',
                  sMV ''Text4''
               |>
  , Recv ''4'' <| sAV ''T'', sAV ''A'', sMV ''Text7'', sAV ''A'',
                  sPK ''A'', sAV ''B'', sMV ''pkB'',
                  PSign <| sC ''isoiec_9798_3_6_opt_1_sig_4_1'', sN ''Rpa'', sAV ''B'',
                           sMV ''pkB'', sMV ''Text6''
                        |>
                        ( sPK ''T'' ),
                  sMV ''TokenTA_for_B''
               |>
  , Send ''check_4_out'' ( PEnc <| sC ''check_4'', sMV ''TokenBA'' |>
                                ( sN ''check_nonce_4'' )
                         )
  , Recv ''check_4_in'' ( PEnc <| sC ''check_4'',
                                  PSign <| sC ''isoiec_9798_3_6_opt_1_sig_2'', sAV ''B'', sN ''Ra'',
                                           sMV ''Rb'', sAV ''A'', sMV ''Text2''
                                        |>
                                        ( sMV ''pkB'' )
                               |>
                               ( sN ''check_nonce_4'' )
                        )
  , Recv ''text_5'' <| sMV ''Text8'', sMV ''Text9'' |>
  , Send ''5'' <| sAV ''A'', sAV ''B'', sMV ''Text9'', sAV ''T'',
                  sMV ''TokenTA_for_B'',
                  PSign <| sC ''isoiec_9798_3_6_opt_1_sig_5'', sMV ''Rb'', sN ''Ra'',
                           sAV ''B'', sAV ''A'', sMV ''Text8''
                        |>
                        ( sPK ''A'' )
               |>
  ]"

role isoiec_9798_3_6_1_B
where "isoiec_9798_3_6_1_B =
  [ Recv ''1'' <| sMV ''A'', sAV ''B'', sMV ''Ra'', sMV ''Text1'' |>
  , Recv ''text_2'' <| sMV ''Text2'', sMV ''Text3'' |>
  , Send ''2'' <| sMV ''A'', sAV ''B'', sMV ''Ra'', sN ''Rb'',
                  sMV ''Text3'',
                  PSign <| sC ''isoiec_9798_3_6_opt_1_sig_2'', sAV ''B'', sMV ''Ra'',
                           sN ''Rb'', sMV ''A'', sMV ''Text2''
                        |>
                        ( sPK ''B'' )
               |>
  , Recv ''5'' <| sMV ''A'', sAV ''B'', sMV ''Text9'', sMV ''T'',
                  PSign <| sC ''isoiec_9798_3_6_opt_1_sig_4_2'', sN ''Rb'', sMV ''A'',
                           sMV ''pkA'', sMV ''Text5''
                        |>
                        ( PAsymPK ( sMV ''T'' ) ),
                  PSign <| sC ''isoiec_9798_3_6_opt_1_sig_5'', sN ''Rb'', sMV ''Ra'',
                           sAV ''B'', sMV ''A'', sMV ''Text8''
                        |>
                        ( sMV ''pkA'' )
               |>
  ]"

role isoiec_9798_3_6_1_T
where "isoiec_9798_3_6_1_T =
  [ Recv ''3'' <| sMV ''A'', sAV ''T'', sMV ''Rpa'', sMV ''Rb'', sMV ''B'',
                  sMV ''Text4''
               |>
  , Recv ''text_4'' <| sMV ''Text5'', sMV ''Text6'', sMV ''Text7'' |>
  , Send ''4'' <| sAV ''T'', sMV ''A'', sMV ''Text7'', sMV ''A'',
                  PAsymPK ( sMV ''A'' ), sMV ''B'', PAsymPK ( sMV ''B'' ),
                  PSign <| sC ''isoiec_9798_3_6_opt_1_sig_4_1'', sMV ''Rpa'', sMV ''B'',
                           PAsymPK ( sMV ''B'' ), sMV ''Text6''
                        |>
                        ( sPK ''T'' ),
                  PSign <| sC ''isoiec_9798_3_6_opt_1_sig_4_2'', sMV ''Rb'', sMV ''A'',
                           PAsymPK ( sMV ''A'' ), sMV ''Text5''
                        |>
                        ( sPK ''T'' )
               |>
  ]"

protocol isoiec_9798_3_6_1
where "isoiec_9798_3_6_1 =
{ isoiec_9798_3_6_1_A, isoiec_9798_3_6_1_B, isoiec_9798_3_6_1_T }"

locale restricted_isoiec_9798_3_6_1_state = isoiec_9798_3_6_1_state

type_invariant isoiec_9798_3_6_1_msc_typing for isoiec_9798_3_6_1
where "isoiec_9798_3_6_1_msc_typing = mk_typing
  [ ((isoiec_9798_3_6_1_B, ''A''), (KnownT isoiec_9798_3_6_1_B_1))
  , ((isoiec_9798_3_6_1_T, ''A''), (KnownT isoiec_9798_3_6_1_T_3))
  , ((isoiec_9798_3_6_1_T, ''B''), (KnownT isoiec_9798_3_6_1_T_3))
  , ((isoiec_9798_3_6_1_B, ''Ra''), (KnownT isoiec_9798_3_6_1_B_1))
  , ((isoiec_9798_3_6_1_A, ''Rb''), (KnownT isoiec_9798_3_6_1_A_2))
  , ((isoiec_9798_3_6_1_T, ''Rb''), (KnownT isoiec_9798_3_6_1_T_3))
  , ((isoiec_9798_3_6_1_T, ''Rpa''), (KnownT isoiec_9798_3_6_1_T_3))
  , ((isoiec_9798_3_6_1_B, ''T''), (KnownT isoiec_9798_3_6_1_B_5))
  , ((isoiec_9798_3_6_1_A, ''Text1''), (KnownT isoiec_9798_3_6_1_A_text_1))
  , ((isoiec_9798_3_6_1_B, ''Text1''), (KnownT isoiec_9798_3_6_1_B_1))
  , ((isoiec_9798_3_6_1_A, ''Text2''),
     (KnownT isoiec_9798_3_6_1_A_check_4_in))
  , ((isoiec_9798_3_6_1_B, ''Text2''), (KnownT isoiec_9798_3_6_1_B_text_2))
  , ((isoiec_9798_3_6_1_A, ''Text3''), (KnownT isoiec_9798_3_6_1_A_2))
  , ((isoiec_9798_3_6_1_B, ''Text3''), (KnownT isoiec_9798_3_6_1_B_text_2))
  , ((isoiec_9798_3_6_1_A, ''Text4''), (KnownT isoiec_9798_3_6_1_A_text_3))
  , ((isoiec_9798_3_6_1_T, ''Text4''), (KnownT isoiec_9798_3_6_1_T_3))
  , ((isoiec_9798_3_6_1_B, ''Text5''), (KnownT isoiec_9798_3_6_1_B_5))
  , ((isoiec_9798_3_6_1_T, ''Text5''), (KnownT isoiec_9798_3_6_1_T_text_4))
  , ((isoiec_9798_3_6_1_A, ''Text6''), (KnownT isoiec_9798_3_6_1_A_4))
  , ((isoiec_9798_3_6_1_T, ''Text6''), (KnownT isoiec_9798_3_6_1_T_text_4))
  , ((isoiec_9798_3_6_1_A, ''Text7''), (KnownT isoiec_9798_3_6_1_A_4))
  , ((isoiec_9798_3_6_1_T, ''Text7''), (KnownT isoiec_9798_3_6_1_T_text_4))
  , ((isoiec_9798_3_6_1_A, ''Text8''), (KnownT isoiec_9798_3_6_1_A_text_5))
  , ((isoiec_9798_3_6_1_B, ''Text8''), (KnownT isoiec_9798_3_6_1_B_5))
  , ((isoiec_9798_3_6_1_A, ''Text9''), (KnownT isoiec_9798_3_6_1_A_text_5))
  , ((isoiec_9798_3_6_1_B, ''Text9''), (KnownT isoiec_9798_3_6_1_B_5))
  , ((isoiec_9798_3_6_1_A, ''TokenBA''), (KnownT isoiec_9798_3_6_1_A_2))
  , ((isoiec_9798_3_6_1_A, ''TokenTA_for_B''),
     (KnownT isoiec_9798_3_6_1_A_4))
  , ((isoiec_9798_3_6_1_B, ''pkA''), (KnownT isoiec_9798_3_6_1_B_5))
  , ((isoiec_9798_3_6_1_A, ''pkB''), (KnownT isoiec_9798_3_6_1_A_4))
  ]"

sublocale isoiec_9798_3_6_1_state < isoiec_9798_3_6_1_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_3_6_1_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_3_6_1_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_3_6_1_A_2_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_A_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_A_2_TokenBA t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_A_4_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_A_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_A_4_TokenTA_for_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_A_4_pkB t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_A_check_4_in_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''check_4'',
               {| LC ''isoiec_9798_3_6_opt_1_sig_2'', s(AV ''B'' tid0), LN ''Ra'' tid0,
                  s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''Text2'' tid0)
               |},
               Enc {| LC ''isoiec_9798_3_6_opt_1_sig_2'', s(AV ''B'' tid0),
                      LN ''Ra'' tid0, s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''Text2'' tid0)
                   |}
                   ( inv(s(MV ''pkB'' tid0)) )
            |}
            ( LN ''check_nonce_4'' tid0 ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_3_6_1_A_text_5_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_A_text_5_Text9 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_1_Ra t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_5_T t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_5_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_5_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_5_Text9 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_5_pkA t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_T_3_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_T_3_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_T_3_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_T_3_Rpa t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_T_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_T_text_4_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_T_text_4_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_T_text_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_3_6_1_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_3_6_1_state begin

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

lemma (in restricted_isoiec_9798_3_6_1_state) A_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_6_1_A &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          RLKR(s(AV ''T'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_6_1_A_5 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_6_1_B &
          ( tid1, isoiec_9798_3_6_1_B_2 ) : steps t &
          {| s(MV ''A'' tid1), s(AV ''B'' tid1), s(MV ''Ra'' tid1), LN ''Rb'' tid1,
             s(MV ''Text2'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), LN ''Ra'' tid0,
                  s(MV ''Rb'' tid0), s(MV ''Text2'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''check_4'',
                              {| LC ''isoiec_9798_3_6_opt_1_sig_2'', s(AV ''B'' tid0), LN ''Ra'' tid0,
                                 s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''Text2'' tid0)
                              |},
                              Enc {| LC ''isoiec_9798_3_6_opt_1_sig_2'', s(AV ''B'' tid0),
                                     LN ''Ra'' tid0, s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''Text2'' tid0)
                                  |}
                                  ( inv(s(MV ''pkB'' tid0)) )
                           |}
                           ( LN ''check_nonce_4'' tid0 ) ")
        case fake note_unified facts = this facts
        thus ?thesis proof(sources! " LN ''check_nonce_4'' tid0 ")
        qed (insert facts, fastforce+)?
      next
        case (isoiec_9798_3_6_1_A_check_4_out_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_6_opt_1_sig_2'', s(AV ''B'' tid0),
                                LN ''Ra'' tid0, s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''Text2'' tid0)
                             |}
                             ( inv(s(MV ''pkB'' tid0)) ) ")
          case fake note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''isoiec_9798_3_6_opt_1_sig_4_1'', LN ''Rpa'' tid0,
                                  s(AV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text6'' tid0)
                               |}
                               ( SK ( s(AV ''T'' tid0) ) ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest!: ltk_secrecy)
          next
            case (isoiec_9798_3_6_1_T_4_enc tid1) note_unified facts = this facts
            thus ?thesis by (fastforce dest!: ltk_secrecy)
          qed (insert facts, fastforce+)?
        next
          case (isoiec_9798_3_6_1_B_2_enc tid1) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_3_6_1_state) B_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_6_1_B &
          RLKR(s(MV ''A'' tid0)) ~: reveals t &
          RLKR(s(MV ''T'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_6_1_B_5 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_6_1_A &
          ( tid1, isoiec_9798_3_6_1_A_5 ) : steps t &
          {| s(AV ''A'' tid1), s(AV ''B'' tid1), LN ''Ra'' tid1, s(MV ''Rb'' tid1),
             s(MV ''Text8'' tid1)
          |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''Ra'' tid0),
                  LN ''Rb'' tid0, s(MV ''Text8'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_3_6_opt_1_sig_4_2'', LN ''Rb'' tid0,
                              s(MV ''A'' tid0), s(MV ''pkA'' tid0), s(MV ''Text5'' tid0)
                           |}
                           ( SK ( s(MV ''T'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_6_1_T_4_enc_1 tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_6_opt_1_sig_5'', LN ''Rb'' tid0,
                                s(MV ''Ra'' tid0), s(AV ''B'' tid0), s(MV ''A'' tid0),
                                s(MV ''Text8'' tid0)
                             |}
                             ( SK ( s(MV ''A'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_6_1_A_5_enc tid2) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_3_6_1_state) A_injective_agreement_T:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_6_1_A &
          RLKR(s(AV ''T'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_6_1_A_5 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_6_1_T &
          ( tid1, isoiec_9798_3_6_1_T_4 ) : steps t &
          {| s(MV ''B'' tid1), s(AV ''T'' tid1), s(MV ''Rpa'' tid1),
             PK ( s(MV ''B'' tid1) ), s(MV ''Text6'' tid1)
          |} = {| s(AV ''B'' tid0), s(AV ''T'' tid0), LN ''Rpa'' tid0,
                  s(MV ''pkB'' tid0), s(MV ''Text6'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_3_6_opt_1_sig_4_1'', LN ''Rpa'' tid0,
                              s(AV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text6'' tid0)
                           |}
                           ( SK ( s(AV ''T'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_6_1_T_4_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_3_6_1_state) B_injective_agreement_T:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_6_1_B &
          RLKR(s(MV ''T'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_6_1_B_5 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_6_1_T &
          ( tid1, isoiec_9798_3_6_1_T_4 ) : steps t &
          {| s(MV ''A'' tid1), s(AV ''T'' tid1), s(MV ''Rb'' tid1),
             PK ( s(MV ''A'' tid1) ), s(MV ''Text5'' tid1)
          |} = {| s(MV ''A'' tid0), s(MV ''T'' tid0), LN ''Rb'' tid0,
                  s(MV ''pkA'' tid0), s(MV ''Text5'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_3_6_opt_1_sig_4_2'', LN ''Rb'' tid0,
                              s(MV ''A'' tid0), s(MV ''pkA'' tid0), s(MV ''Text5'' tid0)
                           |}
                           ( SK ( s(MV ''T'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_6_1_T_4_enc_1 tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

role isoiec_9798_3_6_2_A
where "isoiec_9798_3_6_2_A =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''A'', sAV ''B'', sN ''Ra'', sMV ''Text1'' |>
  , Recv ''2'' <| sAV ''A'', sAV ''B'', sN ''Ra'', sMV ''Rb'',
                  sMV ''Text3'', sMV ''TokenBA''
               |>
  , Recv ''text_3'' ( sMV ''Text4'' )
  , Send ''3'' <| sAV ''A'', sAV ''T'', sN ''Rpa'', sMV ''Rb'', sAV ''B'',
                  sMV ''Text4''
               |>
  , Recv ''4'' <| sAV ''T'', sAV ''A'', sMV ''Text7'', sAV ''A'',
                  sPK ''A'', sAV ''B'', sMV ''pkB'', sMV ''TokenTA''
               |>
  , Send ''check_4_out'' ( PEnc <| sC ''check_4'', sMV ''TokenTA'',
                                   sMV ''TokenBA''
                                |>
                                ( sN ''check_nonce_4'' )
                         )
  , Recv ''check_4_in'' ( PEnc <| sC ''check_4'',
                                  PSign <| sC ''isoiec_9798_3_6_opt_2_sig_4'', sN ''Rpa'', sMV ''Rb'',
                                           sAV ''A'', sMV ''pkA'', sAV ''B'', sMV ''pkB'', sMV ''Text5''
                                        |>
                                        ( sPK ''T'' ),
                                  PSign <| sC ''isoiec_9798_3_6_opt_2_sig_2'', sAV ''B'', sN ''Ra'',
                                           sMV ''Rb'', sAV ''A'', sMV ''Text2''
                                        |>
                                        ( sMV ''pkB'' )
                               |>
                               ( sN ''check_nonce_4'' )
                        )
  , Recv ''text_5'' <| sMV ''Text8'', sMV ''Text9'' |>
  , Send ''5'' <| sAV ''A'', sAV ''B'', sN ''Rpa'', sMV ''Text9'',
                  sAV ''T'', sMV ''TokenTA'',
                  PSign <| sC ''isoiec_9798_3_6_opt_2_sig_5'', sMV ''Rb'', sN ''Ra'',
                           sAV ''B'', sAV ''A'', sMV ''Text8''
                        |>
                        ( sPK ''A'' )
               |>
  ]"

role isoiec_9798_3_6_2_B
where "isoiec_9798_3_6_2_B =
  [ Recv ''1'' <| sMV ''A'', sAV ''B'', sMV ''Ra'', sMV ''Text1'' |>
  , Recv ''text_2'' <| sMV ''Text2'', sMV ''Text3'' |>
  , Send ''2'' <| sMV ''A'', sAV ''B'', sMV ''Ra'', sN ''Rb'',
                  sMV ''Text3'',
                  PSign <| sC ''isoiec_9798_3_6_opt_2_sig_2'', sAV ''B'', sMV ''Ra'',
                           sN ''Rb'', sMV ''A'', sMV ''Text2''
                        |>
                        ( sPK ''B'' )
               |>
  , Recv ''5'' <| sMV ''A'', sAV ''B'', sMV ''Rpa'', sMV ''Text9'',
                  sMV ''T'',
                  PSign <| sC ''isoiec_9798_3_6_opt_2_sig_4'', sMV ''Rpa'', sN ''Rb'',
                           sMV ''A'', sMV ''pkA'', sAV ''B'', sMV ''pkB'', sMV ''Text5''
                        |>
                        ( PAsymPK ( sMV ''T'' ) ),
                  PSign <| sC ''isoiec_9798_3_6_opt_2_sig_5'', sN ''Rb'', sMV ''Ra'',
                           sAV ''B'', sMV ''A'', sMV ''Text8''
                        |>
                        ( sMV ''pkA'' )
               |>
  ]"

role isoiec_9798_3_6_2_T
where "isoiec_9798_3_6_2_T =
  [ Recv ''3'' <| sMV ''A'', sAV ''T'', sMV ''Rpa'', sMV ''Rb'', sMV ''B'',
                  sMV ''Text4''
               |>
  , Recv ''text_4'' <| sMV ''Text5'', sMV ''Text7'' |>
  , Send ''4'' <| sAV ''T'', sMV ''A'', sMV ''Text7'', sMV ''A'',
                  PAsymPK ( sMV ''A'' ), sMV ''B'', PAsymPK ( sMV ''B'' ),
                  PSign <| sC ''isoiec_9798_3_6_opt_2_sig_4'', sMV ''Rpa'', sMV ''Rb'',
                           sMV ''A'', PAsymPK ( sMV ''A'' ), sMV ''B'', PAsymPK ( sMV ''B'' ),
                           sMV ''Text5''
                        |>
                        ( sPK ''T'' )
               |>
  ]"

protocol isoiec_9798_3_6_2
where "isoiec_9798_3_6_2 =
{ isoiec_9798_3_6_2_A, isoiec_9798_3_6_2_B, isoiec_9798_3_6_2_T }"

locale restricted_isoiec_9798_3_6_2_state = isoiec_9798_3_6_2_state

type_invariant isoiec_9798_3_6_2_msc_typing for isoiec_9798_3_6_2
where "isoiec_9798_3_6_2_msc_typing = mk_typing
  [ ((isoiec_9798_3_6_2_B, ''A''), (KnownT isoiec_9798_3_6_2_B_1))
  , ((isoiec_9798_3_6_2_T, ''A''), (KnownT isoiec_9798_3_6_2_T_3))
  , ((isoiec_9798_3_6_2_T, ''B''), (KnownT isoiec_9798_3_6_2_T_3))
  , ((isoiec_9798_3_6_2_B, ''Ra''), (KnownT isoiec_9798_3_6_2_B_1))
  , ((isoiec_9798_3_6_2_A, ''Rb''), (KnownT isoiec_9798_3_6_2_A_2))
  , ((isoiec_9798_3_6_2_T, ''Rb''), (KnownT isoiec_9798_3_6_2_T_3))
  , ((isoiec_9798_3_6_2_B, ''Rpa''), (KnownT isoiec_9798_3_6_2_B_5))
  , ((isoiec_9798_3_6_2_T, ''Rpa''), (KnownT isoiec_9798_3_6_2_T_3))
  , ((isoiec_9798_3_6_2_B, ''T''), (KnownT isoiec_9798_3_6_2_B_5))
  , ((isoiec_9798_3_6_2_A, ''Text1''), (KnownT isoiec_9798_3_6_2_A_text_1))
  , ((isoiec_9798_3_6_2_B, ''Text1''), (KnownT isoiec_9798_3_6_2_B_1))
  , ((isoiec_9798_3_6_2_A, ''Text2''),
     (KnownT isoiec_9798_3_6_2_A_check_4_in))
  , ((isoiec_9798_3_6_2_B, ''Text2''), (KnownT isoiec_9798_3_6_2_B_text_2))
  , ((isoiec_9798_3_6_2_A, ''Text3''), (KnownT isoiec_9798_3_6_2_A_2))
  , ((isoiec_9798_3_6_2_B, ''Text3''), (KnownT isoiec_9798_3_6_2_B_text_2))
  , ((isoiec_9798_3_6_2_A, ''Text4''), (KnownT isoiec_9798_3_6_2_A_text_3))
  , ((isoiec_9798_3_6_2_T, ''Text4''), (KnownT isoiec_9798_3_6_2_T_3))
  , ((isoiec_9798_3_6_2_A, ''Text5''),
     (KnownT isoiec_9798_3_6_2_A_check_4_in))
  , ((isoiec_9798_3_6_2_B, ''Text5''), (KnownT isoiec_9798_3_6_2_B_5))
  , ((isoiec_9798_3_6_2_T, ''Text5''), (KnownT isoiec_9798_3_6_2_T_text_4))
  , ((isoiec_9798_3_6_2_A, ''Text7''), (KnownT isoiec_9798_3_6_2_A_4))
  , ((isoiec_9798_3_6_2_T, ''Text7''), (KnownT isoiec_9798_3_6_2_T_text_4))
  , ((isoiec_9798_3_6_2_A, ''Text8''), (KnownT isoiec_9798_3_6_2_A_text_5))
  , ((isoiec_9798_3_6_2_B, ''Text8''), (KnownT isoiec_9798_3_6_2_B_5))
  , ((isoiec_9798_3_6_2_A, ''Text9''), (KnownT isoiec_9798_3_6_2_A_text_5))
  , ((isoiec_9798_3_6_2_B, ''Text9''), (KnownT isoiec_9798_3_6_2_B_5))
  , ((isoiec_9798_3_6_2_A, ''TokenBA''), (KnownT isoiec_9798_3_6_2_A_2))
  , ((isoiec_9798_3_6_2_A, ''TokenTA''), (KnownT isoiec_9798_3_6_2_A_4))
  , ((isoiec_9798_3_6_2_A, ''pkA''),
     (KnownT isoiec_9798_3_6_2_A_check_4_in))
  , ((isoiec_9798_3_6_2_B, ''pkA''), (KnownT isoiec_9798_3_6_2_B_5))
  , ((isoiec_9798_3_6_2_A, ''pkB''), (KnownT isoiec_9798_3_6_2_A_4))
  , ((isoiec_9798_3_6_2_B, ''pkB''), (KnownT isoiec_9798_3_6_2_B_5))
  ]"

sublocale isoiec_9798_3_6_2_state < isoiec_9798_3_6_2_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_3_6_2_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_3_6_2_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_3_6_2_A_2_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_A_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_A_2_TokenBA t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_A_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_A_4_TokenTA t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_A_4_pkB t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_A_check_4_in_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''check_4'',
               {| {| LC ''isoiec_9798_3_6_opt_2_sig_4'', LN ''Rpa'' tid0,
                     s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                     s(AV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text5'' tid0)
                  |},
                  Enc {| LC ''isoiec_9798_3_6_opt_2_sig_4'', LN ''Rpa'' tid0,
                         s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                         s(AV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text5'' tid0)
                      |}
                      ( SK ( s(AV ''T'' tid0) ) )
               |},
               {| LC ''isoiec_9798_3_6_opt_2_sig_2'', s(AV ''B'' tid0), LN ''Ra'' tid0,
                  s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''Text2'' tid0)
               |},
               Enc {| LC ''isoiec_9798_3_6_opt_2_sig_2'', s(AV ''B'' tid0),
                      LN ''Ra'' tid0, s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''Text2'' tid0)
                   |}
                   ( inv(s(MV ''pkB'' tid0)) )
            |}
            ( LN ''check_nonce_4'' tid0 ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_3_6_2_A_check_4_in_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''check_4'',
               {| {| LC ''isoiec_9798_3_6_opt_2_sig_4'', LN ''Rpa'' tid0,
                     s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                     s(AV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text5'' tid0)
                  |},
                  Enc {| LC ''isoiec_9798_3_6_opt_2_sig_4'', LN ''Rpa'' tid0,
                         s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                         s(AV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text5'' tid0)
                      |}
                      ( SK ( s(AV ''T'' tid0) ) )
               |},
               {| LC ''isoiec_9798_3_6_opt_2_sig_2'', s(AV ''B'' tid0), LN ''Ra'' tid0,
                  s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''Text2'' tid0)
               |},
               Enc {| LC ''isoiec_9798_3_6_opt_2_sig_2'', s(AV ''B'' tid0),
                      LN ''Ra'' tid0, s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''Text2'' tid0)
                   |}
                   ( inv(s(MV ''pkB'' tid0)) )
            |}
            ( LN ''check_nonce_4'' tid0 ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_3_6_2_A_check_4_in_pkA t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''check_4'',
               {| {| LC ''isoiec_9798_3_6_opt_2_sig_4'', LN ''Rpa'' tid0,
                     s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                     s(AV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text5'' tid0)
                  |},
                  Enc {| LC ''isoiec_9798_3_6_opt_2_sig_4'', LN ''Rpa'' tid0,
                         s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                         s(AV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text5'' tid0)
                      |}
                      ( SK ( s(AV ''T'' tid0) ) )
               |},
               {| LC ''isoiec_9798_3_6_opt_2_sig_2'', s(AV ''B'' tid0), LN ''Ra'' tid0,
                  s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''Text2'' tid0)
               |},
               Enc {| LC ''isoiec_9798_3_6_opt_2_sig_2'', s(AV ''B'' tid0),
                      LN ''Ra'' tid0, s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''Text2'' tid0)
                   |}
                   ( inv(s(MV ''pkB'' tid0)) )
            |}
            ( LN ''check_nonce_4'' tid0 ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_3_6_2_A_text_5_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_A_text_5_Text9 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_1_Ra t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_5_Rpa t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_5_T t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_5_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_5_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_5_Text9 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_5_pkA t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_5_pkB t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_T_3_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_T_3_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_T_3_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_T_3_Rpa t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_T_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_T_text_4_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_T_text_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_3_6_2_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_3_6_2_state begin

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

lemma (in restricted_isoiec_9798_3_6_2_state) A_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_6_2_A &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          RLKR(s(AV ''T'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_6_2_A_5 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_6_2_B &
          ( tid1, isoiec_9798_3_6_2_B_2 ) : steps t &
          {| s(MV ''A'' tid1), s(AV ''B'' tid1), s(MV ''Ra'' tid1), LN ''Rb'' tid1,
             s(MV ''Text2'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), LN ''Ra'' tid0,
                  s(MV ''Rb'' tid0), s(MV ''Text2'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''check_4'',
                              {| {| LC ''isoiec_9798_3_6_opt_2_sig_4'', LN ''Rpa'' tid0,
                                    s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                                    s(AV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text5'' tid0)
                                 |},
                                 Enc {| LC ''isoiec_9798_3_6_opt_2_sig_4'', LN ''Rpa'' tid0,
                                        s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                                        s(AV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text5'' tid0)
                                     |}
                                     ( SK ( s(AV ''T'' tid0) ) )
                              |},
                              {| LC ''isoiec_9798_3_6_opt_2_sig_2'', s(AV ''B'' tid0), LN ''Ra'' tid0,
                                 s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''Text2'' tid0)
                              |},
                              Enc {| LC ''isoiec_9798_3_6_opt_2_sig_2'', s(AV ''B'' tid0),
                                     LN ''Ra'' tid0, s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''Text2'' tid0)
                                  |}
                                  ( inv(s(MV ''pkB'' tid0)) )
                           |}
                           ( LN ''check_nonce_4'' tid0 ) ")
        case fake note_unified facts = this facts
        thus ?thesis proof(sources! " LN ''check_nonce_4'' tid0 ")
        qed (insert facts, fastforce+)?
      next
        case (isoiec_9798_3_6_2_A_check_4_out_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_6_opt_2_sig_2'', s(AV ''B'' tid0),
                                LN ''Ra'' tid0, s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''Text2'' tid0)
                             |}
                             ( inv(s(MV ''pkB'' tid0)) ) ")
          case fake note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''isoiec_9798_3_6_opt_2_sig_4'', LN ''Rpa'' tid0,
                                  s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                                  s(AV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text5'' tid0)
                               |}
                               ( SK ( s(AV ''T'' tid0) ) ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest!: ltk_secrecy)
          next
            case (isoiec_9798_3_6_2_T_4_enc tid1) note_unified facts = this facts
            thus ?thesis by (fastforce dest!: ltk_secrecy)
          qed (insert facts, fastforce+)?
        next
          case (isoiec_9798_3_6_2_B_2_enc tid1) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_3_6_2_state) B_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_6_2_B &
          RLKR(s(MV ''A'' tid0)) ~: reveals t &
          RLKR(s(MV ''T'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_6_2_B_5 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_6_2_A &
          ( tid1, isoiec_9798_3_6_2_A_5 ) : steps t &
          {| s(AV ''A'' tid1), s(AV ''B'' tid1), LN ''Ra'' tid1, s(MV ''Rb'' tid1),
             s(MV ''Text8'' tid1)
          |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''Ra'' tid0),
                  LN ''Rb'' tid0, s(MV ''Text8'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_3_6_opt_2_sig_4'', s(MV ''Rpa'' tid0),
                              LN ''Rb'' tid0, s(MV ''A'' tid0), s(MV ''pkA'' tid0), s(AV ''B'' tid0),
                              s(MV ''pkB'' tid0), s(MV ''Text5'' tid0)
                           |}
                           ( SK ( s(MV ''T'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_6_2_T_4_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_6_opt_2_sig_5'', LN ''Rb'' tid0,
                                s(MV ''Ra'' tid0), s(AV ''B'' tid0), s(MV ''A'' tid0),
                                s(MV ''Text8'' tid0)
                             |}
                             ( SK ( s(MV ''A'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_6_2_A_5_enc tid2) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_3_6_2_state) A_injective_agreement_T:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_6_2_A &
          RLKR(s(AV ''T'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_6_2_A_5 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_6_2_T &
          ( tid1, isoiec_9798_3_6_2_T_4 ) : steps t &
          {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''T'' tid1),
             s(MV ''Rpa'' tid1), s(MV ''Rb'' tid1), PK ( s(MV ''A'' tid1) ),
             PK ( s(MV ''B'' tid1) ), s(MV ''Text5'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(AV ''T'' tid0),
                  LN ''Rpa'' tid0, s(MV ''Rb'' tid0), s(MV ''pkA'' tid0),
                  s(MV ''pkB'' tid0), s(MV ''Text5'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''check_4'',
                              {| {| LC ''isoiec_9798_3_6_opt_2_sig_4'', LN ''Rpa'' tid0,
                                    s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                                    s(AV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text5'' tid0)
                                 |},
                                 Enc {| LC ''isoiec_9798_3_6_opt_2_sig_4'', LN ''Rpa'' tid0,
                                        s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                                        s(AV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text5'' tid0)
                                     |}
                                     ( SK ( s(AV ''T'' tid0) ) )
                              |},
                              {| LC ''isoiec_9798_3_6_opt_2_sig_2'', s(AV ''B'' tid0), LN ''Ra'' tid0,
                                 s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''Text2'' tid0)
                              |},
                              Enc {| LC ''isoiec_9798_3_6_opt_2_sig_2'', s(AV ''B'' tid0),
                                     LN ''Ra'' tid0, s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''Text2'' tid0)
                                  |}
                                  ( inv(s(MV ''pkB'' tid0)) )
                           |}
                           ( LN ''check_nonce_4'' tid0 ) ")
        case fake note_unified facts = this facts
        thus ?thesis proof(sources! " LN ''check_nonce_4'' tid0 ")
        qed (insert facts, fastforce+)?
      next
        case (isoiec_9798_3_6_2_A_check_4_out_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_6_opt_2_sig_4'', LN ''Rpa'' tid0,
                                s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                                s(AV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text5'' tid0)
                             |}
                             ( SK ( s(AV ''T'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_6_2_T_4_enc tid1) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_3_6_2_state) B_injective_agreement_T:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_6_2_B &
          RLKR(s(MV ''T'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_6_2_B_5 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_6_2_T &
          ( tid1, isoiec_9798_3_6_2_T_4 ) : steps t &
          {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''T'' tid1),
             s(MV ''Rpa'' tid1), s(MV ''Rb'' tid1), PK ( s(MV ''A'' tid1) ),
             PK ( s(MV ''B'' tid1) ), s(MV ''Text5'' tid1)
          |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''T'' tid0),
                  s(MV ''Rpa'' tid0), LN ''Rb'' tid0, s(MV ''pkA'' tid0),
                  s(MV ''pkB'' tid0), s(MV ''Text5'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_3_6_opt_2_sig_4'', s(MV ''Rpa'' tid0),
                              LN ''Rb'' tid0, s(MV ''A'' tid0), s(MV ''pkA'' tid0), s(AV ''B'' tid0),
                              s(MV ''pkB'' tid0), s(MV ''Text5'' tid0)
                           |}
                           ( SK ( s(MV ''T'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_6_2_T_4_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

role isoiec_9798_3_7_1_A
where "isoiec_9798_3_7_1_A =
  [ Recv ''1'' <| sMV ''B'', sAV ''A'', sMV ''Rb'', sMV ''Text1'' |>
  , Recv ''text_2'' ( sMV ''Text2'' )
  , Send ''2'' <| sAV ''A'', sAV ''T'', sN ''Rpa'', sMV ''Rb'', sAV ''A'',
                  sMV ''B'', sMV ''Text2''
               |>
  , Recv ''3'' <| sAV ''T'', sAV ''A'', sMV ''Text5'', sAV ''A'',
                  sPK ''A'', sMV ''B'', sMV ''pkB'',
                  PSign <| sC ''isoiec_9798_3_7_opt_1_sig_3_1'', sN ''Rpa'', sMV ''B'',
                           sMV ''pkB'', sMV ''Text4''
                        |>
                        ( sPK ''T'' ),
                  sMV ''TokenTA_for_B''
               |>
  , Recv ''text_4'' <| sMV ''Text6'', sMV ''Text7'' |>
  , Send ''4'' <| sAV ''A'', sMV ''B'', sN ''Rpa'', sMV ''Text7'',
                  sAV ''T'', sMV ''TokenTA_for_B'',
                  PSign <| sC ''isoiec_9798_3_7_opt_1_sig_4'', sMV ''Rb'', sN ''Ra'',
                           sMV ''B'', sAV ''A'', sMV ''Text6''
                        |>
                        ( sPK ''A'' )
               |>
  , Recv ''5'' <| sAV ''A'', sMV ''B'', sN ''Ra'', sMV ''Rb'',
                  sMV ''Text9'',
                  PSign <| sC ''isoiec_9798_3_7_opt_1_sig_5'', sN ''Ra'', sMV ''Rb'',
                           sAV ''A'', sMV ''B'', sMV ''Text8''
                        |>
                        ( sMV ''pkB'' )
               |>
  ]"

role isoiec_9798_3_7_1_B
where "isoiec_9798_3_7_1_B =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''B'', sAV ''A'', sN ''Rb'', sMV ''Text1'' |>
  , Recv ''4'' <| sAV ''A'', sAV ''B'', sMV ''Rpa'', sMV ''Text9'',
                  sMV ''T'',
                  PSign <| sC ''isoiec_9798_3_7_opt_1_sig_3_2'', sN ''Rb'', sAV ''A'',
                           sMV ''pkA'', sMV ''Text3''
                        |>
                        ( PAsymPK ( sMV ''T'' ) ),
                  PSign <| sC ''isoiec_9798_3_7_opt_1_sig_4'', sN ''Rb'', sMV ''Ra'',
                           sAV ''B'', sAV ''A'', sMV ''Text6''
                        |>
                        ( sMV ''pkA'' )
               |>
  , Recv ''text_5'' <| sMV ''Text8'', sMV ''Text9'' |>
  , Send ''5'' <| sAV ''A'', sAV ''B'', sMV ''Ra'', sN ''Rb'',
                  sMV ''Text9'',
                  PSign <| sC ''isoiec_9798_3_7_opt_1_sig_5'', sMV ''Ra'', sN ''Rb'',
                           sAV ''A'', sAV ''B'', sMV ''Text8''
                        |>
                        ( sPK ''B'' )
               |>
  ]"

role isoiec_9798_3_7_1_T
where "isoiec_9798_3_7_1_T =
  [ Recv ''2'' <| sMV ''A'', sAV ''T'', sMV ''Rpa'', sMV ''Rb'', sMV ''A'',
                  sMV ''B'', sMV ''Text2''
               |>
  , Recv ''text_3'' <| sMV ''Text3'', sMV ''Text4'', sMV ''Text5'' |>
  , Send ''3'' <| sAV ''T'', sMV ''A'', sMV ''Text5'', sMV ''A'',
                  PAsymPK ( sMV ''A'' ), sMV ''B'', PAsymPK ( sMV ''B'' ),
                  PSign <| sC ''isoiec_9798_3_7_opt_1_sig_3_1'', sMV ''Rpa'', sMV ''B'',
                           PAsymPK ( sMV ''B'' ), sMV ''Text4''
                        |>
                        ( sPK ''T'' ),
                  PSign <| sC ''isoiec_9798_3_7_opt_1_sig_3_2'', sMV ''Rb'', sMV ''A'',
                           PAsymPK ( sMV ''A'' ), sMV ''Text3''
                        |>
                        ( sPK ''T'' )
               |>
  ]"

protocol isoiec_9798_3_7_1
where "isoiec_9798_3_7_1 =
{ isoiec_9798_3_7_1_A, isoiec_9798_3_7_1_B, isoiec_9798_3_7_1_T }"

locale restricted_isoiec_9798_3_7_1_state = isoiec_9798_3_7_1_state

type_invariant isoiec_9798_3_7_1_msc_typing for isoiec_9798_3_7_1
where "isoiec_9798_3_7_1_msc_typing = mk_typing
  [ ((isoiec_9798_3_7_1_T, ''A''), (KnownT isoiec_9798_3_7_1_T_2))
  , ((isoiec_9798_3_7_1_A, ''B''), (KnownT isoiec_9798_3_7_1_A_1))
  , ((isoiec_9798_3_7_1_T, ''B''), (KnownT isoiec_9798_3_7_1_T_2))
  , ((isoiec_9798_3_7_1_B, ''Ra''), (KnownT isoiec_9798_3_7_1_B_4))
  , ((isoiec_9798_3_7_1_A, ''Rb''), (KnownT isoiec_9798_3_7_1_A_1))
  , ((isoiec_9798_3_7_1_T, ''Rb''), (KnownT isoiec_9798_3_7_1_T_2))
  , ((isoiec_9798_3_7_1_B, ''Rpa''), (KnownT isoiec_9798_3_7_1_B_4))
  , ((isoiec_9798_3_7_1_T, ''Rpa''), (KnownT isoiec_9798_3_7_1_T_2))
  , ((isoiec_9798_3_7_1_B, ''T''), (KnownT isoiec_9798_3_7_1_B_4))
  , ((isoiec_9798_3_7_1_A, ''Text1''), (KnownT isoiec_9798_3_7_1_A_1))
  , ((isoiec_9798_3_7_1_B, ''Text1''), (KnownT isoiec_9798_3_7_1_B_text_1))
  , ((isoiec_9798_3_7_1_A, ''Text2''), (KnownT isoiec_9798_3_7_1_A_text_2))
  , ((isoiec_9798_3_7_1_T, ''Text2''), (KnownT isoiec_9798_3_7_1_T_2))
  , ((isoiec_9798_3_7_1_B, ''Text3''), (KnownT isoiec_9798_3_7_1_B_4))
  , ((isoiec_9798_3_7_1_T, ''Text3''), (KnownT isoiec_9798_3_7_1_T_text_3))
  , ((isoiec_9798_3_7_1_A, ''Text4''), (KnownT isoiec_9798_3_7_1_A_3))
  , ((isoiec_9798_3_7_1_T, ''Text4''), (KnownT isoiec_9798_3_7_1_T_text_3))
  , ((isoiec_9798_3_7_1_A, ''Text5''), (KnownT isoiec_9798_3_7_1_A_3))
  , ((isoiec_9798_3_7_1_T, ''Text5''), (KnownT isoiec_9798_3_7_1_T_text_3))
  , ((isoiec_9798_3_7_1_A, ''Text6''), (KnownT isoiec_9798_3_7_1_A_text_4))
  , ((isoiec_9798_3_7_1_B, ''Text6''), (KnownT isoiec_9798_3_7_1_B_4))
  , ((isoiec_9798_3_7_1_A, ''Text7''), (KnownT isoiec_9798_3_7_1_A_text_4))
  , ((isoiec_9798_3_7_1_A, ''Text8''), (KnownT isoiec_9798_3_7_1_A_5))
  , ((isoiec_9798_3_7_1_B, ''Text8''), (KnownT isoiec_9798_3_7_1_B_text_5))
  , ((isoiec_9798_3_7_1_A, ''Text9''), (KnownT isoiec_9798_3_7_1_A_5))
  , ((isoiec_9798_3_7_1_B, ''Text9''), (KnownT isoiec_9798_3_7_1_B_4))
  , ((isoiec_9798_3_7_1_A, ''TokenTA_for_B''),
     (KnownT isoiec_9798_3_7_1_A_3))
  , ((isoiec_9798_3_7_1_B, ''pkA''), (KnownT isoiec_9798_3_7_1_B_4))
  , ((isoiec_9798_3_7_1_A, ''pkB''), (KnownT isoiec_9798_3_7_1_A_3))
  ]"

sublocale isoiec_9798_3_7_1_state < isoiec_9798_3_7_1_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_3_7_1_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_3_7_1_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_3_7_1_A_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_1_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_3_TokenTA_for_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_3_pkB t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_text_4_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_text_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_5_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_5_Text9 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_B_4_Ra t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_B_4_Rpa t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_B_4_T t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_B_4_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_B_4_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_B_4_Text9 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_B_4_pkA t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_B_text_5_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_T_2_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_T_2_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_T_2_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_T_2_Rpa t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_T_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_T_text_3_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_T_text_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_T_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_3_7_1_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_3_7_1_state begin

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

lemma (in restricted_isoiec_9798_3_7_1_state) A_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_7_1_A &
          RLKR(s(AV ''T'' tid0)) ~: reveals t &
          RLKR(s(MV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_7_1_A_5 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_7_1_B &
          ( tid1, isoiec_9798_3_7_1_B_5 ) : steps t &
          {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(MV ''Ra'' tid1), LN ''Rb'' tid1,
             s(MV ''Text8'' tid1)
          |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), LN ''Ra'' tid0,
                  s(MV ''Rb'' tid0), s(MV ''Text8'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_3_7_opt_1_sig_3_1'', LN ''Rpa'' tid0,
                              s(MV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text4'' tid0)
                           |}
                           ( SK ( s(AV ''T'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_7_1_T_3_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_7_opt_1_sig_5'', LN ''Ra'' tid0,
                                s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''B'' tid0),
                                s(MV ''Text8'' tid0)
                             |}
                             ( SK ( s(MV ''B'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_7_1_B_5_enc tid2) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_3_7_1_state) B_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_7_1_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(MV ''T'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_7_1_B_4 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_7_1_A &
          ( tid1, isoiec_9798_3_7_1_A_4 ) : steps t &
          {| s(AV ''A'' tid1), s(MV ''B'' tid1), LN ''Ra'' tid1, s(MV ''Rb'' tid1),
             s(MV ''Text6'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''Ra'' tid0),
                  LN ''Rb'' tid0, s(MV ''Text6'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_3_7_opt_1_sig_3_2'', LN ''Rb'' tid0,
                              s(AV ''A'' tid0), s(MV ''pkA'' tid0), s(MV ''Text3'' tid0)
                           |}
                           ( SK ( s(MV ''T'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_7_1_T_3_enc_1 tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_7_opt_1_sig_4'', LN ''Rb'' tid0,
                                s(MV ''Ra'' tid0), s(AV ''B'' tid0), s(AV ''A'' tid0),
                                s(MV ''Text6'' tid0)
                             |}
                             ( SK ( s(AV ''A'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_7_1_A_4_enc tid2) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_3_7_1_state) A_injective_agreement_T:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_7_1_A &
          RLKR(s(AV ''T'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_7_1_A_3 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_7_1_T &
          ( tid1, isoiec_9798_3_7_1_T_3 ) : steps t &
          {| s(MV ''B'' tid1), s(AV ''T'' tid1), s(MV ''Rpa'' tid1),
             PK ( s(MV ''B'' tid1) ), s(MV ''Text4'' tid1)
          |} = {| s(MV ''B'' tid0), s(AV ''T'' tid0), LN ''Rpa'' tid0,
                  s(MV ''pkB'' tid0), s(MV ''Text4'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_3_7_opt_1_sig_3_1'', LN ''Rpa'' tid0,
                              s(MV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text4'' tid0)
                           |}
                           ( SK ( s(AV ''T'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_7_1_T_3_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_3_7_1_state) B_injective_agreement_T:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_7_1_B &
          RLKR(s(MV ''T'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_7_1_B_4 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_7_1_T &
          ( tid1, isoiec_9798_3_7_1_T_3 ) : steps t &
          {| s(MV ''A'' tid1), s(AV ''T'' tid1), s(MV ''Rb'' tid1),
             PK ( s(MV ''A'' tid1) ), s(MV ''Text3'' tid1)
          |} = {| s(AV ''A'' tid0), s(MV ''T'' tid0), LN ''Rb'' tid0,
                  s(MV ''pkA'' tid0), s(MV ''Text3'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_3_7_opt_1_sig_3_2'', LN ''Rb'' tid0,
                              s(AV ''A'' tid0), s(MV ''pkA'' tid0), s(MV ''Text3'' tid0)
                           |}
                           ( SK ( s(MV ''T'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_7_1_T_3_enc_1 tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

role isoiec_9798_3_7_2_A
where "isoiec_9798_3_7_2_A =
  [ Recv ''1'' <| sMV ''B'', sAV ''A'', sMV ''Rb'', sMV ''Text1'' |>
  , Recv ''text_2'' ( sMV ''Text2'' )
  , Send ''2'' <| sAV ''A'', sAV ''T'', sN ''Rpa'', sMV ''Rb'', sAV ''A'',
                  sMV ''B'', sMV ''Text2''
               |>
  , Recv ''3'' <| sAV ''T'', sAV ''A'', sMV ''Text5'', sAV ''A'',
                  sPK ''A'', sMV ''B'', sMV ''pkB'', sMV ''TokenTA''
               |>
  , Send ''check_3_out'' ( PEnc <| sC ''check_4'', sMV ''TokenTA'' |>
                                ( sN ''check_nonce_4'' )
                         )
  , Recv ''check_3_in'' ( PEnc <| sC ''check_4'',
                                  PSign <| sC ''isoiec_9798_3_7_opt_2_sig_3'', sN ''Rpa'', sMV ''Rb'',
                                           sAV ''A'', sMV ''pkA'', sMV ''B'', sMV ''pkB'', sMV ''Text3''
                                        |>
                                        ( sPK ''T'' )
                               |>
                               ( sN ''check_nonce_4'' )
                        )
  , Recv ''text_4'' <| sMV ''Text6'', sMV ''Text7'' |>
  , Send ''4'' <| sAV ''A'', sMV ''B'', sN ''Rpa'', sMV ''Text7'',
                  sAV ''T'', sMV ''TokenTA'',
                  PSign <| sC ''isoiec_9798_3_7_opt_2_sig_4'', sMV ''Rb'', sN ''Ra'',
                           sMV ''B'', sAV ''A'', sMV ''Text6''
                        |>
                        ( sPK ''A'' )
               |>
  , Recv ''5'' <| sAV ''A'', sMV ''B'', sN ''Ra'', sMV ''Rb'',
                  sMV ''Text9'',
                  PSign <| sC ''isoiec_9798_3_7_opt_2_sig_5'', sN ''Ra'', sMV ''Rb'',
                           sAV ''A'', sMV ''B'', sMV ''Text8''
                        |>
                        ( sMV ''pkB'' )
               |>
  ]"

role isoiec_9798_3_7_2_B
where "isoiec_9798_3_7_2_B =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''B'', sAV ''A'', sN ''Rb'', sMV ''Text1'' |>
  , Recv ''4'' <| sAV ''A'', sAV ''B'', sMV ''Rpa'', sMV ''Text9'',
                  sMV ''T'',
                  PSign <| sC ''isoiec_9798_3_7_opt_2_sig_3'', sMV ''Rpa'', sN ''Rb'',
                           sAV ''A'', sMV ''pkA'', sAV ''B'', sMV ''pkB'', sMV ''Text3''
                        |>
                        ( PAsymPK ( sMV ''T'' ) ),
                  PSign <| sC ''isoiec_9798_3_7_opt_2_sig_4'', sN ''Rb'', sMV ''Ra'',
                           sAV ''B'', sAV ''A'', sMV ''Text6''
                        |>
                        ( sMV ''pkA'' )
               |>
  , Recv ''text_5'' <| sMV ''Text8'', sMV ''Text9'' |>
  , Send ''5'' <| sAV ''A'', sAV ''B'', sMV ''Ra'', sN ''Rb'',
                  sMV ''Text9'',
                  PSign <| sC ''isoiec_9798_3_7_opt_2_sig_5'', sMV ''Ra'', sN ''Rb'',
                           sAV ''A'', sAV ''B'', sMV ''Text8''
                        |>
                        ( sPK ''B'' )
               |>
  ]"

role isoiec_9798_3_7_2_T
where "isoiec_9798_3_7_2_T =
  [ Recv ''2'' <| sMV ''A'', sAV ''T'', sMV ''Rpa'', sMV ''Rb'', sMV ''A'',
                  sMV ''B'', sMV ''Text2''
               |>
  , Recv ''text_3'' <| sMV ''Text3'', sMV ''Text5'' |>
  , Send ''3'' <| sAV ''T'', sMV ''A'', sMV ''Text5'', sMV ''A'',
                  PAsymPK ( sMV ''A'' ), sMV ''B'', PAsymPK ( sMV ''B'' ),
                  PSign <| sC ''isoiec_9798_3_7_opt_2_sig_3'', sMV ''Rpa'', sMV ''Rb'',
                           sMV ''A'', PAsymPK ( sMV ''A'' ), sMV ''B'', PAsymPK ( sMV ''B'' ),
                           sMV ''Text3''
                        |>
                        ( sPK ''T'' )
               |>
  ]"

protocol isoiec_9798_3_7_2
where "isoiec_9798_3_7_2 =
{ isoiec_9798_3_7_2_A, isoiec_9798_3_7_2_B, isoiec_9798_3_7_2_T }"

locale restricted_isoiec_9798_3_7_2_state = isoiec_9798_3_7_2_state

type_invariant isoiec_9798_3_7_2_msc_typing for isoiec_9798_3_7_2
where "isoiec_9798_3_7_2_msc_typing = mk_typing
  [ ((isoiec_9798_3_7_2_T, ''A''), (KnownT isoiec_9798_3_7_2_T_2))
  , ((isoiec_9798_3_7_2_A, ''B''), (KnownT isoiec_9798_3_7_2_A_1))
  , ((isoiec_9798_3_7_2_T, ''B''), (KnownT isoiec_9798_3_7_2_T_2))
  , ((isoiec_9798_3_7_2_B, ''Ra''), (KnownT isoiec_9798_3_7_2_B_4))
  , ((isoiec_9798_3_7_2_A, ''Rb''), (KnownT isoiec_9798_3_7_2_A_1))
  , ((isoiec_9798_3_7_2_T, ''Rb''), (KnownT isoiec_9798_3_7_2_T_2))
  , ((isoiec_9798_3_7_2_B, ''Rpa''), (KnownT isoiec_9798_3_7_2_B_4))
  , ((isoiec_9798_3_7_2_T, ''Rpa''), (KnownT isoiec_9798_3_7_2_T_2))
  , ((isoiec_9798_3_7_2_B, ''T''), (KnownT isoiec_9798_3_7_2_B_4))
  , ((isoiec_9798_3_7_2_A, ''Text1''), (KnownT isoiec_9798_3_7_2_A_1))
  , ((isoiec_9798_3_7_2_B, ''Text1''), (KnownT isoiec_9798_3_7_2_B_text_1))
  , ((isoiec_9798_3_7_2_A, ''Text2''), (KnownT isoiec_9798_3_7_2_A_text_2))
  , ((isoiec_9798_3_7_2_T, ''Text2''), (KnownT isoiec_9798_3_7_2_T_2))
  , ((isoiec_9798_3_7_2_A, ''Text3''),
     (KnownT isoiec_9798_3_7_2_A_check_3_in))
  , ((isoiec_9798_3_7_2_B, ''Text3''), (KnownT isoiec_9798_3_7_2_B_4))
  , ((isoiec_9798_3_7_2_T, ''Text3''), (KnownT isoiec_9798_3_7_2_T_text_3))
  , ((isoiec_9798_3_7_2_A, ''Text5''), (KnownT isoiec_9798_3_7_2_A_3))
  , ((isoiec_9798_3_7_2_T, ''Text5''), (KnownT isoiec_9798_3_7_2_T_text_3))
  , ((isoiec_9798_3_7_2_A, ''Text6''), (KnownT isoiec_9798_3_7_2_A_text_4))
  , ((isoiec_9798_3_7_2_B, ''Text6''), (KnownT isoiec_9798_3_7_2_B_4))
  , ((isoiec_9798_3_7_2_A, ''Text7''), (KnownT isoiec_9798_3_7_2_A_text_4))
  , ((isoiec_9798_3_7_2_A, ''Text8''), (KnownT isoiec_9798_3_7_2_A_5))
  , ((isoiec_9798_3_7_2_B, ''Text8''), (KnownT isoiec_9798_3_7_2_B_text_5))
  , ((isoiec_9798_3_7_2_A, ''Text9''), (KnownT isoiec_9798_3_7_2_A_5))
  , ((isoiec_9798_3_7_2_B, ''Text9''), (KnownT isoiec_9798_3_7_2_B_4))
  , ((isoiec_9798_3_7_2_A, ''TokenTA''), (KnownT isoiec_9798_3_7_2_A_3))
  , ((isoiec_9798_3_7_2_A, ''pkA''),
     (KnownT isoiec_9798_3_7_2_A_check_3_in))
  , ((isoiec_9798_3_7_2_B, ''pkA''), (KnownT isoiec_9798_3_7_2_B_4))
  , ((isoiec_9798_3_7_2_A, ''pkB''), (KnownT isoiec_9798_3_7_2_A_3))
  , ((isoiec_9798_3_7_2_B, ''pkB''), (KnownT isoiec_9798_3_7_2_B_4))
  ]"

sublocale isoiec_9798_3_7_2_state < isoiec_9798_3_7_2_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_3_7_2_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_3_7_2_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_3_7_2_A_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_1_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_3_TokenTA t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_3_pkB t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_check_3_in_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''check_4'',
               {| LC ''isoiec_9798_3_7_opt_2_sig_3'', LN ''Rpa'' tid0,
                  s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                  s(MV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text3'' tid0)
               |},
               Enc {| LC ''isoiec_9798_3_7_opt_2_sig_3'', LN ''Rpa'' tid0,
                      s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                      s(MV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text3'' tid0)
                   |}
                   ( SK ( s(AV ''T'' tid0) ) )
            |}
            ( LN ''check_nonce_4'' tid0 ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_3_7_2_A_check_3_in_pkA t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''check_4'',
               {| LC ''isoiec_9798_3_7_opt_2_sig_3'', LN ''Rpa'' tid0,
                  s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                  s(MV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text3'' tid0)
               |},
               Enc {| LC ''isoiec_9798_3_7_opt_2_sig_3'', LN ''Rpa'' tid0,
                      s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                      s(MV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text3'' tid0)
                   |}
                   ( SK ( s(AV ''T'' tid0) ) )
            |}
            ( LN ''check_nonce_4'' tid0 ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (isoiec_9798_3_7_2_A_text_4_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_text_4_Text7 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_5_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_5_Text9 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_4_Ra t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_4_Rpa t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_4_T t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_4_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_4_Text6 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_4_Text9 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_4_pkA t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_4_pkB t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_text_5_Text8 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_T_2_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_T_2_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_T_2_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_T_2_Rpa t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_T_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_T_text_3_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_T_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_3_7_2_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_3_7_2_state begin

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

lemma (in restricted_isoiec_9798_3_7_2_state) A_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_7_2_A &
          RLKR(s(AV ''T'' tid0)) ~: reveals t &
          RLKR(s(MV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_7_2_A_5 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_7_2_B &
          ( tid1, isoiec_9798_3_7_2_B_5 ) : steps t &
          {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(MV ''Ra'' tid1), LN ''Rb'' tid1,
             s(MV ''Text8'' tid1)
          |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), LN ''Ra'' tid0,
                  s(MV ''Rb'' tid0), s(MV ''Text8'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''check_4'',
                              {| LC ''isoiec_9798_3_7_opt_2_sig_3'', LN ''Rpa'' tid0,
                                 s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                                 s(MV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text3'' tid0)
                              |},
                              Enc {| LC ''isoiec_9798_3_7_opt_2_sig_3'', LN ''Rpa'' tid0,
                                     s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                                     s(MV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text3'' tid0)
                                  |}
                                  ( SK ( s(AV ''T'' tid0) ) )
                           |}
                           ( LN ''check_nonce_4'' tid0 ) ")
        case fake note_unified facts = this facts
        thus ?thesis proof(sources! " LN ''check_nonce_4'' tid0 ")
        qed (insert facts, fastforce+)?
      next
        case (isoiec_9798_3_7_2_A_check_3_out_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_7_opt_2_sig_3'', LN ''Rpa'' tid0,
                                s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                                s(MV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text3'' tid0)
                             |}
                             ( SK ( s(AV ''T'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_7_2_T_3_enc tid1) note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''isoiec_9798_3_7_opt_2_sig_5'', LN ''Ra'' tid0,
                                  s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''B'' tid0),
                                  s(MV ''Text8'' tid0)
                               |}
                               ( SK ( s(MV ''B'' tid0) ) ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest!: ltk_secrecy)
          next
            case (isoiec_9798_3_7_2_B_5_enc tid2) note_unified facts = this facts
            thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
          qed (insert facts, fastforce+)?
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_3_7_2_state) B_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_7_2_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(MV ''T'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_7_2_B_4 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_7_2_A &
          ( tid1, isoiec_9798_3_7_2_A_4 ) : steps t &
          {| s(AV ''A'' tid1), s(MV ''B'' tid1), LN ''Ra'' tid1, s(MV ''Rb'' tid1),
             s(MV ''Text6'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''Ra'' tid0),
                  LN ''Rb'' tid0, s(MV ''Text6'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_3_7_opt_2_sig_3'', s(MV ''Rpa'' tid0),
                              LN ''Rb'' tid0, s(AV ''A'' tid0), s(MV ''pkA'' tid0), s(AV ''B'' tid0),
                              s(MV ''pkB'' tid0), s(MV ''Text3'' tid0)
                           |}
                           ( SK ( s(MV ''T'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_7_2_T_3_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_7_opt_2_sig_4'', LN ''Rb'' tid0,
                                s(MV ''Ra'' tid0), s(AV ''B'' tid0), s(AV ''A'' tid0),
                                s(MV ''Text6'' tid0)
                             |}
                             ( SK ( s(AV ''A'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_7_2_A_4_enc tid2) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_3_7_2_state) A_injective_agreement_T:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_7_2_A &
          RLKR(s(AV ''T'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_7_2_A_4 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_7_2_T &
          ( tid1, isoiec_9798_3_7_2_T_3 ) : steps t &
          {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''T'' tid1),
             s(MV ''Rpa'' tid1), s(MV ''Rb'' tid1), PK ( s(MV ''A'' tid1) ),
             PK ( s(MV ''B'' tid1) ), s(MV ''Text3'' tid1)
          |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                  LN ''Rpa'' tid0, s(MV ''Rb'' tid0), s(MV ''pkA'' tid0),
                  s(MV ''pkB'' tid0), s(MV ''Text3'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''check_4'',
                              {| LC ''isoiec_9798_3_7_opt_2_sig_3'', LN ''Rpa'' tid0,
                                 s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                                 s(MV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text3'' tid0)
                              |},
                              Enc {| LC ''isoiec_9798_3_7_opt_2_sig_3'', LN ''Rpa'' tid0,
                                     s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                                     s(MV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text3'' tid0)
                                  |}
                                  ( SK ( s(AV ''T'' tid0) ) )
                           |}
                           ( LN ''check_nonce_4'' tid0 ) ")
        case fake note_unified facts = this facts
        thus ?thesis proof(sources! " LN ''check_nonce_4'' tid0 ")
        qed (insert facts, fastforce+)?
      next
        case (isoiec_9798_3_7_2_A_check_3_out_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_7_opt_2_sig_3'', LN ''Rpa'' tid0,
                                s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                                s(MV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text3'' tid0)
                             |}
                             ( SK ( s(AV ''T'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_7_2_T_3_enc tid1) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_3_7_2_state) B_injective_agreement_T:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_3_7_2_B &
          RLKR(s(MV ''T'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_3_7_2_B_4 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_3_7_2_T &
          ( tid1, isoiec_9798_3_7_2_T_3 ) : steps t &
          {| s(MV ''A'' tid1), s(MV ''B'' tid1), s(AV ''T'' tid1),
             s(MV ''Rpa'' tid1), s(MV ''Rb'' tid1), PK ( s(MV ''A'' tid1) ),
             PK ( s(MV ''B'' tid1) ), s(MV ''Text3'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''T'' tid0),
                  s(MV ''Rpa'' tid0), LN ''Rb'' tid0, s(MV ''pkA'' tid0),
                  s(MV ''pkB'' tid0), s(MV ''Text3'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''isoiec_9798_3_7_opt_2_sig_3'', s(MV ''Rpa'' tid0),
                              LN ''Rb'' tid0, s(AV ''A'' tid0), s(MV ''pkA'' tid0), s(AV ''B'' tid0),
                              s(MV ''pkB'' tid0), s(MV ''Text3'' tid0)
                           |}
                           ( SK ( s(MV ''T'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_7_2_T_3_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

role isoiec_9798_4_1_bdkey_A
where "isoiec_9798_4_1_bdkey_A =
  [ Send ''leak_A'' ( sN ''TNA'' )
  , Recv ''text_1'' <| sMV ''Text1'', sMV ''Text2'' |>
  , Send ''1'' <| sAV ''A'', sAV ''B'', sN ''TNA'', sMV ''Text2'',
                  sMV ''Text1'',
                  PHash <| <| sC ''CCF'', sKbd (AVar ''A'') (AVar ''B'') |>,
                           sC ''isoiec_9798_4_1_ccf_1'', sN ''TNA'', sAV ''B'', sMV ''Text1''
                        |>
               |>
  ]"

role isoiec_9798_4_1_bdkey_B
where "isoiec_9798_4_1_bdkey_B =
  [ Recv ''1'' <| sMV ''A'', sAV ''B'', sMV ''TNA'', sMV ''Text2'',
                  sMV ''Text1'',
                  PHash <| <| sC ''CCF'', sKbd (MVar ''A'') (AVar ''B'') |>,
                           sC ''isoiec_9798_4_1_ccf_1'', sMV ''TNA'', sAV ''B'', sMV ''Text1''
                        |>
               |>
  ]"

protocol isoiec_9798_4_1_bdkey
where "isoiec_9798_4_1_bdkey =
{ isoiec_9798_4_1_bdkey_A, isoiec_9798_4_1_bdkey_B }"

locale restricted_isoiec_9798_4_1_bdkey_state = isoiec_9798_4_1_bdkey_state

type_invariant isoiec_9798_4_1_bdkey_msc_typing for isoiec_9798_4_1_bdkey
where "isoiec_9798_4_1_bdkey_msc_typing = mk_typing
  [ ((isoiec_9798_4_1_bdkey_B, ''A''), (KnownT isoiec_9798_4_1_bdkey_B_1))
  , ((isoiec_9798_4_1_bdkey_B, ''TNA''),
     (KnownT isoiec_9798_4_1_bdkey_B_1))
  , ((isoiec_9798_4_1_bdkey_A, ''Text1''),
     (KnownT isoiec_9798_4_1_bdkey_A_text_1))
  , ((isoiec_9798_4_1_bdkey_B, ''Text1''),
     (KnownT isoiec_9798_4_1_bdkey_B_1))
  , ((isoiec_9798_4_1_bdkey_A, ''Text2''),
     (KnownT isoiec_9798_4_1_bdkey_A_text_1))
  , ((isoiec_9798_4_1_bdkey_B, ''Text2''),
     (KnownT isoiec_9798_4_1_bdkey_B_1))
  ]"

sublocale isoiec_9798_4_1_bdkey_state < isoiec_9798_4_1_bdkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_4_1_bdkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_4_1_bdkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_4_1_bdkey_A_text_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_1_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_1_bdkey_A_text_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_1_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_1_bdkey_B_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_1_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_1_bdkey_B_1_TNA t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_1_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_1_bdkey_B_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_1_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_1_bdkey_B_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_1_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_4_1_bdkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_4_1_bdkey_state begin

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

lemma (in restricted_isoiec_9798_4_1_bdkey_state) B_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_4_1_bdkey_B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_4_1_bdkey_B_1 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_4_1_bdkey_A &
        ( tid1, isoiec_9798_4_1_bdkey_A_1 ) : steps t &
        {| s(AV ''A'' tid1), s(AV ''B'' tid1), LN ''TNA'' tid1,
           s(MV ''Text1'' tid1)
        |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''TNA'' tid0),
                s(MV ''Text1'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Hash {| {| LC ''CCF'', Kbd ( s(AV ''B'' tid0) ) ( s(MV ''A'' tid0) ) |},
                           LC ''isoiec_9798_4_1_ccf_1'', s(MV ''TNA'' tid0), s(AV ''B'' tid0),
                           s(MV ''Text1'' tid0)
                        |} ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_4_1_bdkey_A_1_hash tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (insert facts, fastforce+)?
qed

role isoiec_9798_4_2_bdkey_A
where "isoiec_9798_4_2_bdkey_A =
  [ Recv ''1'' <| sMV ''B'', sAV ''A'', sMV ''Rb'', sMV ''Text1'' |>
  , Recv ''text_2'' <| sMV ''Text2'', sMV ''Text3'' |>
  , Send ''2'' <| sAV ''A'', sMV ''B'', sMV ''Text3'', sMV ''Rb'',
                  sMV ''Text2'',
                  PHash <| <| sC ''CCF'', sKbd (AVar ''A'') (MVar ''B'') |>,
                           sC ''isoiec_9798_4_2_ccf_2'', sMV ''Rb'', sMV ''B'', sMV ''Text2''
                        |>
               |>
  ]"

role isoiec_9798_4_2_bdkey_B
where "isoiec_9798_4_2_bdkey_B =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''B'', sAV ''A'', sN ''Rb'', sMV ''Text1'' |>
  , Recv ''2'' <| sAV ''A'', sAV ''B'', sMV ''Text3'', sN ''Rb'',
                  sMV ''Text2'',
                  PHash <| <| sC ''CCF'', sKbd (AVar ''A'') (AVar ''B'') |>,
                           sC ''isoiec_9798_4_2_ccf_2'', sN ''Rb'', sAV ''B'', sMV ''Text2''
                        |>
               |>
  ]"

protocol isoiec_9798_4_2_bdkey
where "isoiec_9798_4_2_bdkey =
{ isoiec_9798_4_2_bdkey_A, isoiec_9798_4_2_bdkey_B }"

locale restricted_isoiec_9798_4_2_bdkey_state = isoiec_9798_4_2_bdkey_state

type_invariant isoiec_9798_4_2_bdkey_msc_typing for isoiec_9798_4_2_bdkey
where "isoiec_9798_4_2_bdkey_msc_typing = mk_typing
  [ ((isoiec_9798_4_2_bdkey_A, ''B''), (KnownT isoiec_9798_4_2_bdkey_A_1))
  , ((isoiec_9798_4_2_bdkey_A, ''Rb''), (KnownT isoiec_9798_4_2_bdkey_A_1))
  , ((isoiec_9798_4_2_bdkey_A, ''Text1''),
     (KnownT isoiec_9798_4_2_bdkey_A_1))
  , ((isoiec_9798_4_2_bdkey_B, ''Text1''),
     (KnownT isoiec_9798_4_2_bdkey_B_text_1))
  , ((isoiec_9798_4_2_bdkey_A, ''Text2''),
     (KnownT isoiec_9798_4_2_bdkey_A_text_2))
  , ((isoiec_9798_4_2_bdkey_B, ''Text2''),
     (KnownT isoiec_9798_4_2_bdkey_B_2))
  , ((isoiec_9798_4_2_bdkey_A, ''Text3''),
     (KnownT isoiec_9798_4_2_bdkey_A_text_2))
  , ((isoiec_9798_4_2_bdkey_B, ''Text3''),
     (KnownT isoiec_9798_4_2_bdkey_B_2))
  ]"

sublocale isoiec_9798_4_2_bdkey_state < isoiec_9798_4_2_bdkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_4_2_bdkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_4_2_bdkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_4_2_bdkey_A_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_2_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_bdkey_A_1_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_2_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_bdkey_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_2_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_bdkey_A_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_2_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_bdkey_A_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_2_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_bdkey_B_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_2_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_bdkey_B_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_2_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_4_2_bdkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_4_2_bdkey_state begin

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

lemma (in restricted_isoiec_9798_4_2_bdkey_state) B_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_4_2_bdkey_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_4_2_bdkey_B_2 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_4_2_bdkey_A &
          ( tid1, isoiec_9798_4_2_bdkey_A_2 ) : steps t &
          {| s(AV ''A'' tid1), s(MV ''B'' tid1), s(MV ''Rb'' tid1),
             s(MV ''Text2'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), LN ''Rb'' tid0,
                  s(MV ''Text2'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Hash {| {| LC ''CCF'', Kbd ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) |},
                               LC ''isoiec_9798_4_2_ccf_2'', LN ''Rb'' tid0, s(AV ''B'' tid0),
                               s(MV ''Text2'' tid0)
                            |} ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_4_2_bdkey_A_2_hash tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

role isoiec_9798_4_3_bdkey_A
where "isoiec_9798_4_3_bdkey_A =
  [ Send ''leak_A'' ( sN ''TNa'' )
  , Recv ''text_1'' <| sMV ''Text1'', sMV ''Text2'' |>
  , Send ''1'' <| sAV ''A'', sAV ''B'', sN ''TNa'', sMV ''Text2'',
                  sMV ''Text1'',
                  PHash <| <| sC ''CCF'', sKbd (AVar ''A'') (AVar ''B'') |>,
                           sC ''isoiec_9798_4_3_ccf_1'', sN ''TNa'', sAV ''B'', sMV ''Text1''
                        |>
               |>
  , Recv ''2'' <| sAV ''B'', sAV ''A'', sMV ''TNb'', sMV ''Text4'',
                  sMV ''Text3'',
                  PHash <| <| sC ''CCF'', sKbd (AVar ''A'') (AVar ''B'') |>,
                           sC ''isoiec_9798_4_3_ccf_2'', sMV ''TNb'', sAV ''A'', sMV ''Text3''
                        |>
               |>
  ]"

role isoiec_9798_4_3_bdkey_B
where "isoiec_9798_4_3_bdkey_B =
  [ Send ''leak_B'' ( sN ''TNb'' )
  , Recv ''1'' <| sMV ''A'', sAV ''B'', sMV ''TNa'', sMV ''Text2'',
                  sMV ''Text1'',
                  PHash <| <| sC ''CCF'', sKbd (MVar ''A'') (AVar ''B'') |>,
                           sC ''isoiec_9798_4_3_ccf_1'', sMV ''TNa'', sAV ''B'', sMV ''Text1''
                        |>
               |>
  , Recv ''text_2'' <| sMV ''Text3'', sMV ''Text4'' |>
  , Send ''2'' <| sAV ''B'', sMV ''A'', sN ''TNb'', sMV ''Text4'',
                  sMV ''Text3'',
                  PHash <| <| sC ''CCF'', sKbd (MVar ''A'') (AVar ''B'') |>,
                           sC ''isoiec_9798_4_3_ccf_2'', sN ''TNb'', sMV ''A'', sMV ''Text3''
                        |>
               |>
  ]"

protocol isoiec_9798_4_3_bdkey
where "isoiec_9798_4_3_bdkey =
{ isoiec_9798_4_3_bdkey_A, isoiec_9798_4_3_bdkey_B }"

locale restricted_isoiec_9798_4_3_bdkey_state = isoiec_9798_4_3_bdkey_state

type_invariant isoiec_9798_4_3_bdkey_msc_typing for isoiec_9798_4_3_bdkey
where "isoiec_9798_4_3_bdkey_msc_typing = mk_typing
  [ ((isoiec_9798_4_3_bdkey_B, ''A''), (KnownT isoiec_9798_4_3_bdkey_B_1))
  , ((isoiec_9798_4_3_bdkey_B, ''TNa''),
     (KnownT isoiec_9798_4_3_bdkey_B_1))
  , ((isoiec_9798_4_3_bdkey_A, ''TNb''),
     (KnownT isoiec_9798_4_3_bdkey_A_2))
  , ((isoiec_9798_4_3_bdkey_A, ''Text1''),
     (KnownT isoiec_9798_4_3_bdkey_A_text_1))
  , ((isoiec_9798_4_3_bdkey_B, ''Text1''),
     (KnownT isoiec_9798_4_3_bdkey_B_1))
  , ((isoiec_9798_4_3_bdkey_A, ''Text2''),
     (KnownT isoiec_9798_4_3_bdkey_A_text_1))
  , ((isoiec_9798_4_3_bdkey_B, ''Text2''),
     (KnownT isoiec_9798_4_3_bdkey_B_1))
  , ((isoiec_9798_4_3_bdkey_A, ''Text3''),
     (KnownT isoiec_9798_4_3_bdkey_A_2))
  , ((isoiec_9798_4_3_bdkey_B, ''Text3''),
     (KnownT isoiec_9798_4_3_bdkey_B_text_2))
  , ((isoiec_9798_4_3_bdkey_A, ''Text4''),
     (KnownT isoiec_9798_4_3_bdkey_A_2))
  , ((isoiec_9798_4_3_bdkey_B, ''Text4''),
     (KnownT isoiec_9798_4_3_bdkey_B_text_2))
  ]"

sublocale isoiec_9798_4_3_bdkey_state < isoiec_9798_4_3_bdkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_4_3_bdkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_4_3_bdkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_4_3_bdkey_A_text_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_bdkey_A_text_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_bdkey_A_2_TNb t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_bdkey_A_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_bdkey_A_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_bdkey_B_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_bdkey_B_1_TNa t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_bdkey_B_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_bdkey_B_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_bdkey_B_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_bdkey_B_text_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_4_3_bdkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_4_3_bdkey_state begin

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

lemma (in restricted_isoiec_9798_4_3_bdkey_state) A_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_4_3_bdkey_A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_4_3_bdkey_A_2 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_4_3_bdkey_B &
        ( tid1, isoiec_9798_4_3_bdkey_B_2 ) : steps t &
        {| s(MV ''A'' tid1), s(AV ''B'' tid1), LN ''TNb'' tid1,
           s(MV ''Text3'' tid1)
        |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''TNb'' tid0),
                s(MV ''Text3'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Hash {| {| LC ''CCF'', Kbd ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) |},
                           LC ''isoiec_9798_4_3_ccf_2'', s(MV ''TNb'' tid0), s(AV ''A'' tid0),
                           s(MV ''Text3'' tid0)
                        |} ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_4_3_bdkey_B_2_hash tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_isoiec_9798_4_3_bdkey_state) B_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_4_3_bdkey_B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_4_3_bdkey_B_1 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_4_3_bdkey_A &
        ( tid1, isoiec_9798_4_3_bdkey_A_1 ) : steps t &
        {| s(AV ''A'' tid1), s(AV ''B'' tid1), LN ''TNa'' tid1,
           s(MV ''Text1'' tid1)
        |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''TNa'' tid0),
                s(MV ''Text1'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Hash {| {| LC ''CCF'', Kbd ( s(AV ''B'' tid0) ) ( s(MV ''A'' tid0) ) |},
                           LC ''isoiec_9798_4_3_ccf_1'', s(MV ''TNa'' tid0), s(AV ''B'' tid0),
                           s(MV ''Text1'' tid0)
                        |} ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_4_3_bdkey_A_1_hash tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (insert facts, fastforce+)?
qed

role isoiec_9798_4_4_bdkey_A
where "isoiec_9798_4_4_bdkey_A =
  [ Recv ''1'' <| sMV ''B'', sAV ''A'', sMV ''Rb'', sMV ''Text1'' |>
  , Recv ''text_2'' <| sMV ''Text2'', sMV ''Text3'' |>
  , Send ''2'' <| sAV ''A'', sMV ''B'', sN ''Ra'', sMV ''Text3'',
                  sMV ''Text2'',
                  PHash <| <| sC ''CCF'', sKbd (AVar ''A'') (MVar ''B'') |>,
                           sC ''isoiec_9798_4_4_ccf_2'', sN ''Ra'', sMV ''Rb'', sMV ''B'',
                           sMV ''Text2''
                        |>
               |>
  , Recv ''3'' <| sMV ''B'', sAV ''A'', sMV ''Text5'', sMV ''Text4'',
                  PHash <| <| sC ''CCF'', sKbd (AVar ''A'') (MVar ''B'') |>,
                           sC ''isoiec_9798_4_4_ccf_3'', sMV ''Rb'', sN ''Ra'', sMV ''Text4''
                        |>
               |>
  ]"

role isoiec_9798_4_4_bdkey_B
where "isoiec_9798_4_4_bdkey_B =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''B'', sAV ''A'', sN ''Rb'', sMV ''Text1'' |>
  , Recv ''2'' <| sAV ''A'', sAV ''B'', sMV ''Ra'', sMV ''Text3'',
                  sMV ''Text2'',
                  PHash <| <| sC ''CCF'', sKbd (AVar ''A'') (AVar ''B'') |>,
                           sC ''isoiec_9798_4_4_ccf_2'', sMV ''Ra'', sN ''Rb'', sAV ''B'',
                           sMV ''Text2''
                        |>
               |>
  , Recv ''text_3'' <| sMV ''Text4'', sMV ''Text5'' |>
  , Send ''3'' <| sAV ''B'', sAV ''A'', sMV ''Text5'', sMV ''Text4'',
                  PHash <| <| sC ''CCF'', sKbd (AVar ''A'') (AVar ''B'') |>,
                           sC ''isoiec_9798_4_4_ccf_3'', sN ''Rb'', sMV ''Ra'', sMV ''Text4''
                        |>
               |>
  ]"

protocol isoiec_9798_4_4_bdkey
where "isoiec_9798_4_4_bdkey =
{ isoiec_9798_4_4_bdkey_A, isoiec_9798_4_4_bdkey_B }"

locale restricted_isoiec_9798_4_4_bdkey_state = isoiec_9798_4_4_bdkey_state

type_invariant isoiec_9798_4_4_bdkey_msc_typing for isoiec_9798_4_4_bdkey
where "isoiec_9798_4_4_bdkey_msc_typing = mk_typing
  [ ((isoiec_9798_4_4_bdkey_A, ''B''), (KnownT isoiec_9798_4_4_bdkey_A_1))
  , ((isoiec_9798_4_4_bdkey_B, ''Ra''), (KnownT isoiec_9798_4_4_bdkey_B_2))
  , ((isoiec_9798_4_4_bdkey_A, ''Rb''), (KnownT isoiec_9798_4_4_bdkey_A_1))
  , ((isoiec_9798_4_4_bdkey_A, ''Text1''),
     (KnownT isoiec_9798_4_4_bdkey_A_1))
  , ((isoiec_9798_4_4_bdkey_B, ''Text1''),
     (KnownT isoiec_9798_4_4_bdkey_B_text_1))
  , ((isoiec_9798_4_4_bdkey_A, ''Text2''),
     (KnownT isoiec_9798_4_4_bdkey_A_text_2))
  , ((isoiec_9798_4_4_bdkey_B, ''Text2''),
     (KnownT isoiec_9798_4_4_bdkey_B_2))
  , ((isoiec_9798_4_4_bdkey_A, ''Text3''),
     (KnownT isoiec_9798_4_4_bdkey_A_text_2))
  , ((isoiec_9798_4_4_bdkey_B, ''Text3''),
     (KnownT isoiec_9798_4_4_bdkey_B_2))
  , ((isoiec_9798_4_4_bdkey_A, ''Text4''),
     (KnownT isoiec_9798_4_4_bdkey_A_3))
  , ((isoiec_9798_4_4_bdkey_B, ''Text4''),
     (KnownT isoiec_9798_4_4_bdkey_B_text_3))
  , ((isoiec_9798_4_4_bdkey_A, ''Text5''),
     (KnownT isoiec_9798_4_4_bdkey_A_3))
  , ((isoiec_9798_4_4_bdkey_B, ''Text5''),
     (KnownT isoiec_9798_4_4_bdkey_B_text_3))
  ]"

sublocale isoiec_9798_4_4_bdkey_state < isoiec_9798_4_4_bdkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_4_4_bdkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_4_4_bdkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_4_4_bdkey_A_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_bdkey_A_1_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_bdkey_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_bdkey_A_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_bdkey_A_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_bdkey_A_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_bdkey_A_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_bdkey_B_2_Ra t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_bdkey_B_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_bdkey_B_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_bdkey_B_text_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_bdkey_B_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_bdkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_4_4_bdkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_4_4_bdkey_state begin

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

lemma (in restricted_isoiec_9798_4_4_bdkey_state) A_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_4_4_bdkey_A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(MV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_4_4_bdkey_A_3 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_4_4_bdkey_B &
          ( tid1, isoiec_9798_4_4_bdkey_B_3 ) : steps t &
          {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(MV ''Ra'' tid1), LN ''Rb'' tid1,
             s(MV ''Text2'' tid1), s(MV ''Text4'' tid1)
          |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), LN ''Ra'' tid0,
                  s(MV ''Rb'' tid0), s(MV ''Text2'' tid0), s(MV ''Text4'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Hash {| {| LC ''CCF'', Kbd ( s(AV ''A'' tid0) ) ( s(MV ''B'' tid0) ) |},
                               LC ''isoiec_9798_4_4_ccf_3'', s(MV ''Rb'' tid0), LN ''Ra'' tid0,
                               s(MV ''Text4'' tid0)
                            |} ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_4_4_bdkey_B_3_hash tid1) note_unified facts = this facts
        hence "Kbd ( s(AV ''A'' tid1) )
                   ( s(AV ''B'' tid1) ) = Kbd ( s(AV ''A'' tid0) ) ( s(MV ''B'' tid0) )"
          by simp note facts = this facts
        thus ?thesis proof(cases rule: Kbd_cases)
          case noswap note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Hash {| {| LC ''CCF'', Kbd ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid1) ) |},
                                   LC ''isoiec_9798_4_4_ccf_2'', LN ''Ra'' tid0, LN ''Rb'' tid1,
                                   s(AV ''B'' tid1), s(MV ''Text2'' tid1)
                                |} ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest!: ltk_secrecy)
          next
            case (isoiec_9798_4_4_bdkey_A_2_hash tid2) note_unified facts = this facts
            thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
          qed (insert facts, fastforce+)?
        next
          case swapped note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Hash {| {| LC ''CCF'', Kbd ( s(AV ''A'' tid0) ) ( s(AV ''A'' tid1) ) |},
                                   LC ''isoiec_9798_4_4_ccf_2'', LN ''Ra'' tid0, LN ''Rb'' tid1,
                                   s(AV ''A'' tid0), s(MV ''Text2'' tid1)
                                |} ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest!: ltk_secrecy)
          next
            case (isoiec_9798_4_4_bdkey_A_2_hash tid2) note_unified facts = this facts
            thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
          qed (insert facts, fastforce+)?
        qed (fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_4_4_bdkey_state) B_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_4_4_bdkey_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_4_4_bdkey_B_2 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_4_4_bdkey_A &
          ( tid1, isoiec_9798_4_4_bdkey_A_2 ) : steps t &
          {| s(AV ''A'' tid1), s(MV ''B'' tid1), LN ''Ra'' tid1, s(MV ''Rb'' tid1),
             s(MV ''Text2'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''Ra'' tid0),
                  LN ''Rb'' tid0, s(MV ''Text2'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Hash {| {| LC ''CCF'', Kbd ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) |},
                               LC ''isoiec_9798_4_4_ccf_2'', s(MV ''Ra'' tid0), LN ''Rb'' tid0,
                               s(AV ''B'' tid0), s(MV ''Text2'' tid0)
                            |} ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_4_4_bdkey_A_2_hash tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

role isoiec_9798_4_1_udkey_A
where "isoiec_9798_4_1_udkey_A =
  [ Send ''leak_A'' ( sN ''TNA'' )
  , Recv ''text_1'' <| sMV ''Text1'', sMV ''Text2'' |>
  , Send ''1'' <| sAV ''A'', sAV ''B'', sN ''TNA'', sMV ''Text2'',
                  sMV ''Text1'',
                  PHash <| <| sC ''CCF'', sK ''A'' ''B'' |>, sC ''isoiec_9798_4_1_ccf_1'',
                           sN ''TNA'', sMV ''Text1''
                        |>
               |>
  ]"

role isoiec_9798_4_1_udkey_B
where "isoiec_9798_4_1_udkey_B =
  [ Recv ''1'' <| sMV ''A'', sAV ''B'', sMV ''TNA'', sMV ''Text2'',
                  sMV ''Text1'',
                  PHash <| <| sC ''CCF'', PSymK ( sMV ''A'' ) ( sAV ''B'' ) |>,
                           sC ''isoiec_9798_4_1_ccf_1'', sMV ''TNA'', sMV ''Text1''
                        |>
               |>
  ]"

protocol isoiec_9798_4_1_udkey
where "isoiec_9798_4_1_udkey =
{ isoiec_9798_4_1_udkey_A, isoiec_9798_4_1_udkey_B }"

locale restricted_isoiec_9798_4_1_udkey_state = isoiec_9798_4_1_udkey_state

type_invariant isoiec_9798_4_1_udkey_msc_typing for isoiec_9798_4_1_udkey
where "isoiec_9798_4_1_udkey_msc_typing = mk_typing
  [ ((isoiec_9798_4_1_udkey_B, ''A''), (KnownT isoiec_9798_4_1_udkey_B_1))
  , ((isoiec_9798_4_1_udkey_B, ''TNA''),
     (KnownT isoiec_9798_4_1_udkey_B_1))
  , ((isoiec_9798_4_1_udkey_A, ''Text1''),
     (KnownT isoiec_9798_4_1_udkey_A_text_1))
  , ((isoiec_9798_4_1_udkey_B, ''Text1''),
     (KnownT isoiec_9798_4_1_udkey_B_1))
  , ((isoiec_9798_4_1_udkey_A, ''Text2''),
     (KnownT isoiec_9798_4_1_udkey_A_text_1))
  , ((isoiec_9798_4_1_udkey_B, ''Text2''),
     (KnownT isoiec_9798_4_1_udkey_B_1))
  ]"

sublocale isoiec_9798_4_1_udkey_state < isoiec_9798_4_1_udkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_4_1_udkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_4_1_udkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_4_1_udkey_A_text_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_1_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_1_udkey_A_text_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_1_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_1_udkey_B_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_1_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_1_udkey_B_1_TNA t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_1_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_1_udkey_B_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_1_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_1_udkey_B_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_1_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_4_1_udkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_4_1_udkey_state begin

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

lemma (in restricted_isoiec_9798_4_1_udkey_state) B_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_4_1_udkey_B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_4_1_udkey_B_1 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_4_1_udkey_A &
        ( tid1, isoiec_9798_4_1_udkey_A_1 ) : steps t &
        {| s(AV ''A'' tid1), s(AV ''B'' tid1), LN ''TNA'' tid1,
           s(MV ''Text1'' tid1)
        |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''TNA'' tid0),
                s(MV ''Text1'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Hash {| {| LC ''CCF'', K ( s(MV ''A'' tid0) ) ( s(AV ''B'' tid0) ) |},
                           LC ''isoiec_9798_4_1_ccf_1'', s(MV ''TNA'' tid0), s(MV ''Text1'' tid0)
                        |} ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_4_1_udkey_A_1_hash tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (insert facts, fastforce+)?
qed

role isoiec_9798_4_2_udkey_A
where "isoiec_9798_4_2_udkey_A =
  [ Recv ''1'' <| sMV ''B'', sAV ''A'', sMV ''Rb'', sMV ''Text1'' |>
  , Recv ''text_2'' <| sMV ''Text2'', sMV ''Text3'' |>
  , Send ''2'' <| sAV ''A'', sMV ''B'', sMV ''Text3'', sMV ''Rb'',
                  sMV ''Text2'',
                  PHash <| <| sC ''CCF'', PSymK ( sAV ''A'' ) ( sMV ''B'' ) |>,
                           sC ''isoiec_9798_4_2_ccf_2'', sMV ''Rb'', sMV ''Text2''
                        |>
               |>
  ]"

role isoiec_9798_4_2_udkey_B
where "isoiec_9798_4_2_udkey_B =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''B'', sAV ''A'', sN ''Rb'', sMV ''Text1'' |>
  , Recv ''2'' <| sAV ''A'', sAV ''B'', sMV ''Text3'', sN ''Rb'',
                  sMV ''Text2'',
                  PHash <| <| sC ''CCF'', sK ''A'' ''B'' |>, sC ''isoiec_9798_4_2_ccf_2'',
                           sN ''Rb'', sMV ''Text2''
                        |>
               |>
  ]"

protocol isoiec_9798_4_2_udkey
where "isoiec_9798_4_2_udkey =
{ isoiec_9798_4_2_udkey_A, isoiec_9798_4_2_udkey_B }"

locale restricted_isoiec_9798_4_2_udkey_state = isoiec_9798_4_2_udkey_state

type_invariant isoiec_9798_4_2_udkey_msc_typing for isoiec_9798_4_2_udkey
where "isoiec_9798_4_2_udkey_msc_typing = mk_typing
  [ ((isoiec_9798_4_2_udkey_A, ''B''), (KnownT isoiec_9798_4_2_udkey_A_1))
  , ((isoiec_9798_4_2_udkey_A, ''Rb''), (KnownT isoiec_9798_4_2_udkey_A_1))
  , ((isoiec_9798_4_2_udkey_A, ''Text1''),
     (KnownT isoiec_9798_4_2_udkey_A_1))
  , ((isoiec_9798_4_2_udkey_B, ''Text1''),
     (KnownT isoiec_9798_4_2_udkey_B_text_1))
  , ((isoiec_9798_4_2_udkey_A, ''Text2''),
     (KnownT isoiec_9798_4_2_udkey_A_text_2))
  , ((isoiec_9798_4_2_udkey_B, ''Text2''),
     (KnownT isoiec_9798_4_2_udkey_B_2))
  , ((isoiec_9798_4_2_udkey_A, ''Text3''),
     (KnownT isoiec_9798_4_2_udkey_A_text_2))
  , ((isoiec_9798_4_2_udkey_B, ''Text3''),
     (KnownT isoiec_9798_4_2_udkey_B_2))
  ]"

sublocale isoiec_9798_4_2_udkey_state < isoiec_9798_4_2_udkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_4_2_udkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_4_2_udkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_4_2_udkey_A_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_udkey_A_1_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_udkey_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_udkey_A_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_udkey_A_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_udkey_B_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_udkey_B_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_2_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_4_2_udkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_4_2_udkey_state begin

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

lemma (in restricted_isoiec_9798_4_2_udkey_state) B_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_4_2_udkey_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_4_2_udkey_B_2 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_4_2_udkey_A &
          ( tid1, isoiec_9798_4_2_udkey_A_2 ) : steps t &
          {| s(AV ''A'' tid1), s(MV ''B'' tid1), s(MV ''Rb'' tid1),
             s(MV ''Text2'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), LN ''Rb'' tid0,
                  s(MV ''Text2'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Hash {| {| LC ''CCF'', K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) |},
                               LC ''isoiec_9798_4_2_ccf_2'', LN ''Rb'' tid0, s(MV ''Text2'' tid0)
                            |} ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_4_2_udkey_A_2_hash tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

role isoiec_9798_4_3_udkey_A
where "isoiec_9798_4_3_udkey_A =
  [ Send ''leak_A'' ( sN ''TNa'' )
  , Recv ''text_1'' <| sMV ''Text1'', sMV ''Text2'' |>
  , Send ''1'' <| sAV ''A'', sAV ''B'', sN ''TNa'', sMV ''Text2'',
                  sMV ''Text1'',
                  PHash <| <| sC ''CCF'', sK ''A'' ''B'' |>, sC ''isoiec_9798_4_3_ccf_1'',
                           sN ''TNa'', sMV ''Text1''
                        |>
               |>
  , Recv ''2'' <| sAV ''B'', sAV ''A'', sMV ''TNb'', sMV ''Text4'',
                  sMV ''Text3'',
                  PHash <| <| sC ''CCF'', sK ''A'' ''B'' |>, sC ''isoiec_9798_4_3_ccf_2'',
                           sMV ''TNb'', sMV ''Text3''
                        |>
               |>
  ]"

role isoiec_9798_4_3_udkey_B
where "isoiec_9798_4_3_udkey_B =
  [ Send ''leak_B'' ( sN ''TNb'' )
  , Recv ''1'' <| sMV ''A'', sAV ''B'', sMV ''TNa'', sMV ''Text2'',
                  sMV ''Text1'',
                  PHash <| <| sC ''CCF'', PSymK ( sMV ''A'' ) ( sAV ''B'' ) |>,
                           sC ''isoiec_9798_4_3_ccf_1'', sMV ''TNa'', sMV ''Text1''
                        |>
               |>
  , Recv ''text_2'' <| sMV ''Text3'', sMV ''Text4'' |>
  , Send ''2'' <| sAV ''B'', sMV ''A'', sN ''TNb'', sMV ''Text4'',
                  sMV ''Text3'',
                  PHash <| <| sC ''CCF'', PSymK ( sMV ''A'' ) ( sAV ''B'' ) |>,
                           sC ''isoiec_9798_4_3_ccf_2'', sN ''TNb'', sMV ''Text3''
                        |>
               |>
  ]"

protocol isoiec_9798_4_3_udkey
where "isoiec_9798_4_3_udkey =
{ isoiec_9798_4_3_udkey_A, isoiec_9798_4_3_udkey_B }"

locale restricted_isoiec_9798_4_3_udkey_state = isoiec_9798_4_3_udkey_state

type_invariant isoiec_9798_4_3_udkey_msc_typing for isoiec_9798_4_3_udkey
where "isoiec_9798_4_3_udkey_msc_typing = mk_typing
  [ ((isoiec_9798_4_3_udkey_B, ''A''), (KnownT isoiec_9798_4_3_udkey_B_1))
  , ((isoiec_9798_4_3_udkey_B, ''TNa''),
     (KnownT isoiec_9798_4_3_udkey_B_1))
  , ((isoiec_9798_4_3_udkey_A, ''TNb''),
     (KnownT isoiec_9798_4_3_udkey_A_2))
  , ((isoiec_9798_4_3_udkey_A, ''Text1''),
     (KnownT isoiec_9798_4_3_udkey_A_text_1))
  , ((isoiec_9798_4_3_udkey_B, ''Text1''),
     (KnownT isoiec_9798_4_3_udkey_B_1))
  , ((isoiec_9798_4_3_udkey_A, ''Text2''),
     (KnownT isoiec_9798_4_3_udkey_A_text_1))
  , ((isoiec_9798_4_3_udkey_B, ''Text2''),
     (KnownT isoiec_9798_4_3_udkey_B_1))
  , ((isoiec_9798_4_3_udkey_A, ''Text3''),
     (KnownT isoiec_9798_4_3_udkey_A_2))
  , ((isoiec_9798_4_3_udkey_B, ''Text3''),
     (KnownT isoiec_9798_4_3_udkey_B_text_2))
  , ((isoiec_9798_4_3_udkey_A, ''Text4''),
     (KnownT isoiec_9798_4_3_udkey_A_2))
  , ((isoiec_9798_4_3_udkey_B, ''Text4''),
     (KnownT isoiec_9798_4_3_udkey_B_text_2))
  ]"

sublocale isoiec_9798_4_3_udkey_state < isoiec_9798_4_3_udkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_4_3_udkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_4_3_udkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_4_3_udkey_A_text_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_A_text_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_A_2_TNb t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_A_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_A_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_B_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_B_1_TNa t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_B_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_B_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_B_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_B_text_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_3_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_4_3_udkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_4_3_udkey_state begin

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

lemma (in restricted_isoiec_9798_4_3_udkey_state) A_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_4_3_udkey_A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_4_3_udkey_A_2 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_4_3_udkey_B &
        ( tid1, isoiec_9798_4_3_udkey_B_2 ) : steps t &
        {| s(MV ''A'' tid1), s(AV ''B'' tid1), LN ''TNb'' tid1,
           s(MV ''Text3'' tid1)
        |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''TNb'' tid0),
                s(MV ''Text3'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Hash {| {| LC ''CCF'', K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) |},
                           LC ''isoiec_9798_4_3_ccf_2'', s(MV ''TNb'' tid0), s(MV ''Text3'' tid0)
                        |} ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_4_3_udkey_B_2_hash tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_isoiec_9798_4_3_udkey_state) B_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_4_3_udkey_B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_4_3_udkey_B_1 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_4_3_udkey_A &
        ( tid1, isoiec_9798_4_3_udkey_A_1 ) : steps t &
        {| s(AV ''A'' tid1), s(AV ''B'' tid1), LN ''TNa'' tid1,
           s(MV ''Text1'' tid1)
        |} = {| s(MV ''A'' tid0), s(AV ''B'' tid0), s(MV ''TNa'' tid0),
                s(MV ''Text1'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Hash {| {| LC ''CCF'', K ( s(MV ''A'' tid0) ) ( s(AV ''B'' tid0) ) |},
                           LC ''isoiec_9798_4_3_ccf_1'', s(MV ''TNa'' tid0), s(MV ''Text1'' tid0)
                        |} ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (isoiec_9798_4_3_udkey_A_1_hash tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (insert facts, fastforce+)?
qed

role isoiec_9798_4_4_udkey_A
where "isoiec_9798_4_4_udkey_A =
  [ Recv ''1'' <| sMV ''B'', sAV ''A'', sMV ''Rb'', sMV ''Text1'' |>
  , Recv ''text_2'' <| sMV ''Text2'', sMV ''Text3'' |>
  , Send ''2'' <| sAV ''A'', sMV ''B'', sN ''Ra'', sMV ''Text3'',
                  sMV ''Text2'',
                  PHash <| <| sC ''CCF'', PSymK ( sAV ''A'' ) ( sMV ''B'' ) |>,
                           sC ''isoiec_9798_4_4_ccf_2'', sN ''Ra'', sMV ''Rb'', sMV ''Text2''
                        |>
               |>
  , Recv ''3'' <| sMV ''B'', sAV ''A'', sMV ''Text5'', sMV ''Text4'',
                  PHash <| <| sC ''CCF'', PSymK ( sAV ''A'' ) ( sMV ''B'' ) |>,
                           sC ''isoiec_9798_4_4_ccf_3'', sMV ''Rb'', sN ''Ra'', sMV ''Text4''
                        |>
               |>
  ]"

role isoiec_9798_4_4_udkey_B
where "isoiec_9798_4_4_udkey_B =
  [ Recv ''text_1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''B'', sAV ''A'', sN ''Rb'', sMV ''Text1'' |>
  , Recv ''2'' <| sAV ''A'', sAV ''B'', sMV ''Ra'', sMV ''Text3'',
                  sMV ''Text2'',
                  PHash <| <| sC ''CCF'', sK ''A'' ''B'' |>, sC ''isoiec_9798_4_4_ccf_2'',
                           sMV ''Ra'', sN ''Rb'', sMV ''Text2''
                        |>
               |>
  , Recv ''text_3'' <| sMV ''Text4'', sMV ''Text5'' |>
  , Send ''3'' <| sAV ''B'', sAV ''A'', sMV ''Text5'', sMV ''Text4'',
                  PHash <| <| sC ''CCF'', sK ''A'' ''B'' |>, sC ''isoiec_9798_4_4_ccf_3'',
                           sN ''Rb'', sMV ''Ra'', sMV ''Text4''
                        |>
               |>
  ]"

protocol isoiec_9798_4_4_udkey
where "isoiec_9798_4_4_udkey =
{ isoiec_9798_4_4_udkey_A, isoiec_9798_4_4_udkey_B }"

locale restricted_isoiec_9798_4_4_udkey_state = isoiec_9798_4_4_udkey_state

type_invariant isoiec_9798_4_4_udkey_msc_typing for isoiec_9798_4_4_udkey
where "isoiec_9798_4_4_udkey_msc_typing = mk_typing
  [ ((isoiec_9798_4_4_udkey_A, ''B''), (KnownT isoiec_9798_4_4_udkey_A_1))
  , ((isoiec_9798_4_4_udkey_B, ''Ra''), (KnownT isoiec_9798_4_4_udkey_B_2))
  , ((isoiec_9798_4_4_udkey_A, ''Rb''), (KnownT isoiec_9798_4_4_udkey_A_1))
  , ((isoiec_9798_4_4_udkey_A, ''Text1''),
     (KnownT isoiec_9798_4_4_udkey_A_1))
  , ((isoiec_9798_4_4_udkey_B, ''Text1''),
     (KnownT isoiec_9798_4_4_udkey_B_text_1))
  , ((isoiec_9798_4_4_udkey_A, ''Text2''),
     (KnownT isoiec_9798_4_4_udkey_A_text_2))
  , ((isoiec_9798_4_4_udkey_B, ''Text2''),
     (KnownT isoiec_9798_4_4_udkey_B_2))
  , ((isoiec_9798_4_4_udkey_A, ''Text3''),
     (KnownT isoiec_9798_4_4_udkey_A_text_2))
  , ((isoiec_9798_4_4_udkey_B, ''Text3''),
     (KnownT isoiec_9798_4_4_udkey_B_2))
  , ((isoiec_9798_4_4_udkey_A, ''Text4''),
     (KnownT isoiec_9798_4_4_udkey_A_3))
  , ((isoiec_9798_4_4_udkey_B, ''Text4''),
     (KnownT isoiec_9798_4_4_udkey_B_text_3))
  , ((isoiec_9798_4_4_udkey_A, ''Text5''),
     (KnownT isoiec_9798_4_4_udkey_A_3))
  , ((isoiec_9798_4_4_udkey_B, ''Text5''),
     (KnownT isoiec_9798_4_4_udkey_B_text_3))
  ]"

sublocale isoiec_9798_4_4_udkey_state < isoiec_9798_4_4_udkey_msc_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_4_4_udkey_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_4_4_udkey_msc_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_4_4_udkey_A_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_A_1_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_A_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_A_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_A_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_A_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_B_2_Ra t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_B_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_B_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_B_text_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_B_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_4_udkey_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_4_4_udkey_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_4_4_udkey_state begin

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

lemma (in restricted_isoiec_9798_4_4_udkey_state) A_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_4_4_udkey_A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(MV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_4_4_udkey_A_3 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_4_4_udkey_B &
          ( tid1, isoiec_9798_4_4_udkey_B_3 ) : steps t &
          {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(MV ''Ra'' tid1), LN ''Rb'' tid1,
             s(MV ''Text2'' tid1), s(MV ''Text4'' tid1)
          |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), LN ''Ra'' tid0,
                  s(MV ''Rb'' tid0), s(MV ''Text2'' tid0), s(MV ''Text4'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Hash {| {| LC ''CCF'', K ( s(AV ''A'' tid0) ) ( s(MV ''B'' tid0) ) |},
                               LC ''isoiec_9798_4_4_ccf_3'', s(MV ''Rb'' tid0), LN ''Ra'' tid0,
                               s(MV ''Text4'' tid0)
                            |} ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_4_4_udkey_B_3_hash tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Hash {| {| LC ''CCF'', K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid1) ) |},
                                 LC ''isoiec_9798_4_4_ccf_2'', LN ''Ra'' tid0, LN ''Rb'' tid1,
                                 s(MV ''Text2'' tid1)
                              |} ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest!: ltk_secrecy)
        next
          case (isoiec_9798_4_4_udkey_A_2_hash tid2) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

lemma (in restricted_isoiec_9798_4_4_udkey_state) B_injective_agreement:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some isoiec_9798_4_4_udkey_B &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t &
          ( tid0, isoiec_9798_4_4_udkey_B_2 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some isoiec_9798_4_4_udkey_A &
          ( tid1, isoiec_9798_4_4_udkey_A_2 ) : steps t &
          {| s(AV ''A'' tid1), s(MV ''B'' tid1), LN ''Ra'' tid1, s(MV ''Rb'' tid1),
             s(MV ''Text2'' tid1)
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''Ra'' tid0),
                  LN ''Rb'' tid0, s(MV ''Text2'' tid0)
               |})
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Hash {| {| LC ''CCF'', K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) |},
                               LC ''isoiec_9798_4_4_ccf_2'', s(MV ''Ra'' tid0), LN ''Rb'' tid0,
                               s(MV ''Text2'' tid0)
                            |} ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case (isoiec_9798_4_4_udkey_A_2_hash tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

end