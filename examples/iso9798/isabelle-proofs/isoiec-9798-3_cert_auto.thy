theory "isoiec-9798-3_cert_auto"
imports
  "ESPLogic"
begin

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
    case (isoiec_9798_3_1_A_text_1_Text1 t r s tid0)
    then interpret state: isoiec_9798_3_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_1_A_text_1_Text1
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_1_A_text_1_Text2 t r s tid0)
    then interpret state: isoiec_9798_3_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_1_A_text_1_Text2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_1_B_1_A t r s tid0)
    then interpret state: isoiec_9798_3_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_1_B_1_A
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_1_B_1_TNA t r s tid0)
    then interpret state: isoiec_9798_3_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_1_B_1_TNA
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_1_B_1_Text1 t r s tid0)
    then interpret state: isoiec_9798_3_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_1_B_1_Text1
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_1_B_1_Text2 t r s tid0)
    then interpret state: isoiec_9798_3_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_1_B_1_Text2
    thus ?case
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
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (isoiec_9798_3_1_A_1_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
    case (isoiec_9798_3_2_A_1_B t r s tid0)
    then interpret state: isoiec_9798_3_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_2_A_1_B
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_2_A_1_Rb t r s tid0)
    then interpret state: isoiec_9798_3_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_2_A_1_Rb
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_2_A_1_Text1 t r s tid0)
    then interpret state: isoiec_9798_3_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_2_A_1_Text1
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_2_A_text_2_Text2 t r s tid0)
    then interpret state: isoiec_9798_3_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_2_A_text_2_Text2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_2_A_text_2_Text3 t r s tid0)
    then interpret state: isoiec_9798_3_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_2_A_text_2_Text3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_2_B_2_Ra t r s tid0)
    then interpret state: isoiec_9798_3_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_2_B_2_Ra
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_2_B_2_Text2 t r s tid0)
    then interpret state: isoiec_9798_3_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_2_B_2_Text2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_2_B_2_Text3 t r s tid0)
    then interpret state: isoiec_9798_3_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_2_B_2_Text3
    thus ?case
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
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_2_A_2_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
    case (isoiec_9798_3_3_A_text_1_Text1 t r s tid0)
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_3_A_text_1_Text1
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_A_text_1_Text2 t r s tid0)
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_3_A_text_1_Text2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_A_2_TNB t r s tid0)
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_3_A_2_TNB
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_A_2_Text3 t r s tid0)
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_3_A_2_Text3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_A_2_Text4 t r s tid0)
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_3_A_2_Text4
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_B_1_A t r s tid0)
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_3_B_1_A
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_B_1_TNA t r s tid0)
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_3_B_1_TNA
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_B_1_Text1 t r s tid0)
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_3_B_1_Text1
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_B_1_Text2 t r s tid0)
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_3_B_1_Text2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_B_text_2_Text3 t r s tid0)
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_3_B_text_2_Text3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_3_B_text_2_Text4 t r s tid0)
    then interpret state: isoiec_9798_3_3_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_3_B_text_2_Text4
    thus ?case
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
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (isoiec_9798_3_3_B_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (isoiec_9798_3_3_A_1_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
    case (isoiec_9798_3_4_A_1_B t r s tid0)
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_4_A_1_B
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_A_1_RB t r s tid0)
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_4_A_1_RB
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_A_1_Text1 t r s tid0)
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_4_A_1_Text1
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_A_text_2_Text2 t r s tid0)
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_4_A_text_2_Text2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_A_text_2_Text3 t r s tid0)
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_4_A_text_2_Text3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_A_3_Text4 t r s tid0)
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_4_A_3_Text4
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_A_3_Text5 t r s tid0)
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_4_A_3_Text5
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_B_2_RA t r s tid0)
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_4_B_2_RA
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_B_2_Text2 t r s tid0)
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_4_B_2_Text2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_B_2_Text3 t r s tid0)
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_4_B_2_Text3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_B_text_3_Text4 t r s tid0)
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_4_B_text_3_Text4
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_4_B_text_3_Text5 t r s tid0)
    then interpret state: isoiec_9798_3_4_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_4_B_text_3_Text5
    thus ?case
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
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_4_B_3_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_4_sig_1'', LN ''RA'' tid0, LN ''RB'' tid1,
                                s(AV ''B'' tid1), s(MV ''Text2'' tid1)
                             |}
                             ( SK ( s(AV ''A'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (auto dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_4_A_2_enc tid2) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_4_A_2_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
    case (isoiec_9798_3_5_A_2_RB t r s tid0)
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_5_A_2_RB
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_A_2_Text2 t r s tid0)
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_5_A_2_Text2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_A_3_Text5 t r s tid0)
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_5_A_3_Text5
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_A_3_Text6 t r s tid0)
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_5_A_3_Text6
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_A_text_4_Text3 t r s tid0)
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_5_A_text_4_Text3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_A_text_4_Text4 t r s tid0)
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_5_A_text_4_Text4
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_B_1_A t r s tid0)
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_5_B_1_A
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_B_1_RA t r s tid0)
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_5_B_1_RA
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_B_1_Text1 t r s tid0)
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_5_B_1_Text1
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_B_text_3_Text5 t r s tid0)
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_5_B_text_3_Text5
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_B_text_3_Text6 t r s tid0)
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_5_B_text_3_Text6
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_B_4_Text3 t r s tid0)
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_5_B_4_Text3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_5_B_4_Text4 t r s tid0)
    then interpret state: isoiec_9798_3_5_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_5_B_4_Text4
    thus ?case
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
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_5_B_3_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_5_A_4_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_5_sig_1'', LN ''RB'' tid0, LN ''RA'' tid1,
                                s(AV ''A'' tid1), s(MV ''Text5'' tid1)
                             |}
                             ( SK ( s(AV ''B'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (auto dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_5_B_3_enc tid2) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
    case (isoiec_9798_3_6_1_A_2_Rb t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_A_2_Rb
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_A_2_Text3 t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_A_2_Text3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_A_2_TokenBA t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_A_2_TokenBA
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_A_4_Text6 t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_A_4_Text6
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_A_4_Text7 t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_A_4_Text7
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_A_4_TokenTA_for_B t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_A_4_TokenTA_for_B
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_A_4_pkB t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_A_4_pkB
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_A_check_4_in_Text2 t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_A_check_4_in_Text2
    thus ?case
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
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (isoiec_9798_3_6_1_A_text_5_Text8 t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_A_text_5_Text8
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_A_text_5_Text9 t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_A_text_5_Text9
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_1_A t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_B_1_A
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_1_Ra t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_B_1_Ra
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_1_Text1 t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_B_1_Text1
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_text_2_Text2 t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_B_text_2_Text2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_text_2_Text3 t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_B_text_2_Text3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_5_T t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_B_5_T
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_5_Text5 t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_B_5_Text5
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_5_Text8 t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_B_5_Text8
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_5_Text9 t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_B_5_Text9
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_B_5_pkA t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_B_5_pkA
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_T_3_A t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_T_3_A
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_T_3_B t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_T_3_B
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_T_3_Rb t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_T_3_Rb
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_T_3_Rpa t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_T_3_Rpa
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_T_3_Text4 t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_T_3_Text4
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_T_text_4_Text5 t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_T_text_4_Text5
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_T_text_4_Text6 t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_T_text_4_Text6
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_1_T_text_4_Text7 t r s tid0)
    then interpret state: isoiec_9798_3_6_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_1_T_text_4_Text7
    thus ?case
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
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
            thus ?thesis by (auto dest!: ltk_secrecy)
          next
            case (isoiec_9798_3_6_1_T_4_enc tid1) note_unified facts = this facts
            thus ?thesis by (auto dest!: ltk_secrecy)
          qed (safe?, simp_all?, insert facts, (fastforce+)?)
        next
          case (isoiec_9798_3_6_1_B_2_enc tid1) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_6_1_T_4_enc_1 tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_6_opt_1_sig_5'', LN ''Rb'' tid0,
                                s(MV ''Ra'' tid0), s(AV ''B'' tid0), s(MV ''A'' tid0),
                                s(MV ''Text8'' tid0)
                             |}
                             ( SK ( s(MV ''A'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (auto dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_6_1_A_5_enc tid2) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_6_1_T_4_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_6_1_T_4_enc_1 tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
    case (isoiec_9798_3_6_2_A_2_Rb t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_A_2_Rb
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_A_2_Text3 t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_A_2_Text3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_A_2_TokenBA t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_A_2_TokenBA
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_A_4_Text7 t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_A_4_Text7
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_A_4_TokenTA t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_A_4_TokenTA
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_A_4_pkB t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_A_4_pkB
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_A_check_4_in_Text2 t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_A_check_4_in_Text2
    thus ?case
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
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (isoiec_9798_3_6_2_A_check_4_in_Text5 t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_A_check_4_in_Text5
    thus ?case
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
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (isoiec_9798_3_6_2_A_check_4_in_pkA t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_A_check_4_in_pkA
    thus ?case
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
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (isoiec_9798_3_6_2_A_text_5_Text8 t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_A_text_5_Text8
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_A_text_5_Text9 t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_A_text_5_Text9
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_1_A t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_B_1_A
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_1_Ra t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_B_1_Ra
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_1_Text1 t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_B_1_Text1
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_text_2_Text2 t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_B_text_2_Text2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_text_2_Text3 t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_B_text_2_Text3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_5_Rpa t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_B_5_Rpa
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_5_T t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_B_5_T
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_5_Text5 t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_B_5_Text5
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_5_Text8 t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_B_5_Text8
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_5_Text9 t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_B_5_Text9
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_5_pkA t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_B_5_pkA
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_B_5_pkB t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_B_5_pkB
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_T_3_A t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_T_3_A
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_T_3_B t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_T_3_B
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_T_3_Rb t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_T_3_Rb
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_T_3_Rpa t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_T_3_Rpa
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_T_3_Text4 t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_T_3_Text4
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_T_text_4_Text5 t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_T_text_4_Text5
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_6_2_T_text_4_Text7 t r s tid0)
    then interpret state: isoiec_9798_3_6_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_6_2_T_text_4_Text7
    thus ?case
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
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
            thus ?thesis by (auto dest!: ltk_secrecy)
          next
            case (isoiec_9798_3_6_2_T_4_enc tid1) note_unified facts = this facts
            thus ?thesis by (auto dest!: ltk_secrecy)
          qed (safe?, simp_all?, insert facts, (fastforce+)?)
        next
          case (isoiec_9798_3_6_2_B_2_enc tid1) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_6_2_T_4_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_6_opt_2_sig_5'', LN ''Rb'' tid0,
                                s(MV ''Ra'' tid0), s(AV ''B'' tid0), s(MV ''A'' tid0),
                                s(MV ''Text8'' tid0)
                             |}
                             ( SK ( s(MV ''A'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (auto dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_6_2_A_5_enc tid2) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      next
        case (isoiec_9798_3_6_2_A_check_4_out_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_6_opt_2_sig_4'', LN ''Rpa'' tid0,
                                s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                                s(AV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text5'' tid0)
                             |}
                             ( SK ( s(AV ''T'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (auto dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_6_2_T_4_enc tid1) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_6_2_T_4_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
    case (isoiec_9798_3_7_1_A_1_B t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_A_1_B
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_1_Rb t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_A_1_Rb
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_1_Text1 t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_A_1_Text1
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_3_Text4 t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_A_3_Text4
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_3_Text5 t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_A_3_Text5
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_3_TokenTA_for_B t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_A_3_TokenTA_for_B
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_3_pkB t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_A_3_pkB
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_text_4_Text6 t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_A_text_4_Text6
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_text_4_Text7 t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_A_text_4_Text7
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_5_Text8 t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_A_5_Text8
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_A_5_Text9 t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_A_5_Text9
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_B_4_Ra t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_B_4_Ra
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_B_4_Rpa t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_B_4_Rpa
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_B_4_T t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_B_4_T
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_B_4_Text3 t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_B_4_Text3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_B_4_Text6 t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_B_4_Text6
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_B_4_Text9 t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_B_4_Text9
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_B_4_pkA t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_B_4_pkA
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_B_text_5_Text8 t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_B_text_5_Text8
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_T_2_A t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_T_2_A
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_T_2_B t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_T_2_B
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_T_2_Rb t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_T_2_Rb
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_T_2_Rpa t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_T_2_Rpa
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_T_2_Text2 t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_T_2_Text2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_T_text_3_Text3 t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_T_text_3_Text3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_T_text_3_Text4 t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_T_text_3_Text4
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_1_T_text_3_Text5 t r s tid0)
    then interpret state: isoiec_9798_3_7_1_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_1_T_text_3_Text5
    thus ?case
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
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_7_1_T_3_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_7_opt_1_sig_5'', LN ''Ra'' tid0,
                                s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''B'' tid0),
                                s(MV ''Text8'' tid0)
                             |}
                             ( SK ( s(MV ''B'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (auto dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_7_1_B_5_enc tid2) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_7_1_T_3_enc_1 tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_7_opt_1_sig_4'', LN ''Rb'' tid0,
                                s(MV ''Ra'' tid0), s(AV ''B'' tid0), s(AV ''A'' tid0),
                                s(MV ''Text6'' tid0)
                             |}
                             ( SK ( s(AV ''A'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (auto dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_7_1_A_4_enc tid2) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_7_1_T_3_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_7_1_T_3_enc_1 tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
    case (isoiec_9798_3_7_2_A_1_B t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_A_1_B
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_1_Rb t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_A_1_Rb
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_1_Text1 t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_A_1_Text1
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_3_Text5 t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_A_3_Text5
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_3_TokenTA t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_A_3_TokenTA
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_3_pkB t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_A_3_pkB
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_check_3_in_Text3 t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_A_check_3_in_Text3
    thus ?case
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
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (isoiec_9798_3_7_2_A_check_3_in_pkA t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_A_check_3_in_pkA
    thus ?case
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
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (isoiec_9798_3_7_2_A_text_4_Text6 t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_A_text_4_Text6
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_text_4_Text7 t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_A_text_4_Text7
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_5_Text8 t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_A_5_Text8
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_A_5_Text9 t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_A_5_Text9
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_4_Ra t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_B_4_Ra
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_4_Rpa t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_B_4_Rpa
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_4_T t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_B_4_T
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_4_Text3 t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_B_4_Text3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_4_Text6 t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_B_4_Text6
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_4_Text9 t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_B_4_Text9
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_4_pkA t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_B_4_pkA
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_4_pkB t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_B_4_pkB
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_B_text_5_Text8 t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_B_text_5_Text8
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_T_2_A t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_T_2_A
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_T_2_B t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_T_2_B
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_T_2_Rb t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_T_2_Rb
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_T_2_Rpa t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_T_2_Rpa
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_T_2_Text2 t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_T_2_Text2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_T_text_3_Text3 t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_T_text_3_Text3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_3_7_2_T_text_3_Text5 t r s tid0)
    then interpret state: isoiec_9798_3_7_2_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = isoiec_9798_3_7_2_T_text_3_Text5
    thus ?case
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
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      next
        case (isoiec_9798_3_7_2_A_check_3_out_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_7_opt_2_sig_3'', LN ''Rpa'' tid0,
                                s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                                s(MV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text3'' tid0)
                             |}
                             ( SK ( s(AV ''T'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (auto dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_7_2_T_3_enc tid1) note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''isoiec_9798_3_7_opt_2_sig_5'', LN ''Ra'' tid0,
                                  s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''B'' tid0),
                                  s(MV ''Text8'' tid0)
                               |}
                               ( SK ( s(MV ''B'' tid0) ) ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (auto dest!: ltk_secrecy)
          next
            case (isoiec_9798_3_7_2_B_5_enc tid2) note_unified facts = this facts
            thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
          qed (safe?, simp_all?, insert facts, (fastforce+)?)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_7_2_T_3_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_7_opt_2_sig_4'', LN ''Rb'' tid0,
                                s(MV ''Ra'' tid0), s(AV ''B'' tid0), s(AV ''A'' tid0),
                                s(MV ''Text6'' tid0)
                             |}
                             ( SK ( s(AV ''A'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (auto dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_7_2_A_4_enc tid2) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      next
        case (isoiec_9798_3_7_2_A_check_3_out_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''isoiec_9798_3_7_opt_2_sig_3'', LN ''Rpa'' tid0,
                                s(MV ''Rb'' tid0), s(AV ''A'' tid0), s(MV ''pkA'' tid0),
                                s(MV ''B'' tid0), s(MV ''pkB'' tid0), s(MV ''Text3'' tid0)
                             |}
                             ( SK ( s(AV ''T'' tid0) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (auto dest!: ltk_secrecy)
        next
          case (isoiec_9798_3_7_2_T_3_enc tid1) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (isoiec_9798_3_7_2_T_3_enc tid1) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
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