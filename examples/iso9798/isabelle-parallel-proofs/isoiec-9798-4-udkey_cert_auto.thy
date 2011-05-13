theory "isoiec-9798-4-udkey_cert_auto"
imports
  "../ESPLogic"
begin

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

protocol isoiec_9798_4_udkey
where "isoiec_9798_4_udkey =
{ isoiec_9798_4_1_udkey_A, isoiec_9798_4_1_udkey_B,
  isoiec_9798_4_2_udkey_A, isoiec_9798_4_2_udkey_B,
  isoiec_9798_4_3_udkey_A, isoiec_9798_4_3_udkey_B,
  isoiec_9798_4_4_udkey_A, isoiec_9798_4_4_udkey_B
}"

locale restricted_isoiec_9798_4_udkey_state = isoiec_9798_4_udkey_state

type_invariant isoiec_9798_4_udkey_composed_typing for isoiec_9798_4_udkey
where "isoiec_9798_4_udkey_composed_typing = mk_typing
  [ ((isoiec_9798_4_1_udkey_B, ''A''), (KnownT isoiec_9798_4_1_udkey_B_1))
  , ((isoiec_9798_4_3_udkey_B, ''A''), (KnownT isoiec_9798_4_3_udkey_B_1))
  , ((isoiec_9798_4_2_udkey_A, ''B''), (KnownT isoiec_9798_4_2_udkey_A_1))
  , ((isoiec_9798_4_4_udkey_A, ''B''), (KnownT isoiec_9798_4_4_udkey_A_1))
  , ((isoiec_9798_4_4_udkey_B, ''Ra''), (KnownT isoiec_9798_4_4_udkey_B_2))
  , ((isoiec_9798_4_2_udkey_A, ''Rb''), (KnownT isoiec_9798_4_2_udkey_A_1))
  , ((isoiec_9798_4_4_udkey_A, ''Rb''), (KnownT isoiec_9798_4_4_udkey_A_1))
  , ((isoiec_9798_4_1_udkey_B, ''TNA''),
     (KnownT isoiec_9798_4_1_udkey_B_1))
  , ((isoiec_9798_4_3_udkey_B, ''TNa''),
     (KnownT isoiec_9798_4_3_udkey_B_1))
  , ((isoiec_9798_4_3_udkey_A, ''TNb''),
     (KnownT isoiec_9798_4_3_udkey_A_2))
  , ((isoiec_9798_4_1_udkey_A, ''Text1''),
     (KnownT isoiec_9798_4_1_udkey_A_text_1))
  , ((isoiec_9798_4_1_udkey_B, ''Text1''),
     (KnownT isoiec_9798_4_1_udkey_B_1))
  , ((isoiec_9798_4_2_udkey_A, ''Text1''),
     (KnownT isoiec_9798_4_2_udkey_A_1))
  , ((isoiec_9798_4_2_udkey_B, ''Text1''),
     (KnownT isoiec_9798_4_2_udkey_B_text_1))
  , ((isoiec_9798_4_3_udkey_A, ''Text1''),
     (KnownT isoiec_9798_4_3_udkey_A_text_1))
  , ((isoiec_9798_4_3_udkey_B, ''Text1''),
     (KnownT isoiec_9798_4_3_udkey_B_1))
  , ((isoiec_9798_4_4_udkey_A, ''Text1''),
     (KnownT isoiec_9798_4_4_udkey_A_1))
  , ((isoiec_9798_4_4_udkey_B, ''Text1''),
     (KnownT isoiec_9798_4_4_udkey_B_text_1))
  , ((isoiec_9798_4_1_udkey_A, ''Text2''),
     (KnownT isoiec_9798_4_1_udkey_A_text_1))
  , ((isoiec_9798_4_1_udkey_B, ''Text2''),
     (KnownT isoiec_9798_4_1_udkey_B_1))
  , ((isoiec_9798_4_2_udkey_A, ''Text2''),
     (KnownT isoiec_9798_4_2_udkey_A_text_2))
  , ((isoiec_9798_4_2_udkey_B, ''Text2''),
     (KnownT isoiec_9798_4_2_udkey_B_2))
  , ((isoiec_9798_4_3_udkey_A, ''Text2''),
     (KnownT isoiec_9798_4_3_udkey_A_text_1))
  , ((isoiec_9798_4_3_udkey_B, ''Text2''),
     (KnownT isoiec_9798_4_3_udkey_B_1))
  , ((isoiec_9798_4_4_udkey_A, ''Text2''),
     (KnownT isoiec_9798_4_4_udkey_A_text_2))
  , ((isoiec_9798_4_4_udkey_B, ''Text2''),
     (KnownT isoiec_9798_4_4_udkey_B_2))
  , ((isoiec_9798_4_2_udkey_A, ''Text3''),
     (KnownT isoiec_9798_4_2_udkey_A_text_2))
  , ((isoiec_9798_4_2_udkey_B, ''Text3''),
     (KnownT isoiec_9798_4_2_udkey_B_2))
  , ((isoiec_9798_4_3_udkey_A, ''Text3''),
     (KnownT isoiec_9798_4_3_udkey_A_2))
  , ((isoiec_9798_4_3_udkey_B, ''Text3''),
     (KnownT isoiec_9798_4_3_udkey_B_text_2))
  , ((isoiec_9798_4_4_udkey_A, ''Text3''),
     (KnownT isoiec_9798_4_4_udkey_A_text_2))
  , ((isoiec_9798_4_4_udkey_B, ''Text3''),
     (KnownT isoiec_9798_4_4_udkey_B_2))
  , ((isoiec_9798_4_3_udkey_A, ''Text4''),
     (KnownT isoiec_9798_4_3_udkey_A_2))
  , ((isoiec_9798_4_3_udkey_B, ''Text4''),
     (KnownT isoiec_9798_4_3_udkey_B_text_2))
  , ((isoiec_9798_4_4_udkey_A, ''Text4''),
     (KnownT isoiec_9798_4_4_udkey_A_3))
  , ((isoiec_9798_4_4_udkey_B, ''Text4''),
     (KnownT isoiec_9798_4_4_udkey_B_text_3))
  , ((isoiec_9798_4_4_udkey_A, ''Text5''),
     (KnownT isoiec_9798_4_4_udkey_A_3))
  , ((isoiec_9798_4_4_udkey_B, ''Text5''),
     (KnownT isoiec_9798_4_4_udkey_B_text_3))
  ]"

sublocale isoiec_9798_4_udkey_state < isoiec_9798_4_udkey_composed_typing_state
proof -
  have "(t,r,s) : approx isoiec_9798_4_udkey_composed_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF isoiec_9798_4_udkey_composed_typing.monoTyp, completeness_cases_rule])
    case (isoiec_9798_4_1_udkey_A_text_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_1_udkey_A_text_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_1_udkey_B_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_1_udkey_B_1_TNA t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_1_udkey_B_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_1_udkey_B_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_udkey_A_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_udkey_A_1_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_udkey_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_udkey_A_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_udkey_A_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_udkey_B_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_2_udkey_B_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_A_text_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_A_text_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_A_2_TNb t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_A_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_A_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_B_1_A t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_B_1_TNa t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_B_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_B_1_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_B_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_3_udkey_B_text_2_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_A_1_B t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_A_1_Rb t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_A_1_Text1 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_A_text_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_A_text_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_A_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_A_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_B_2_Ra t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_B_2_Text2 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_B_2_Text3 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_B_text_3_Text4 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (isoiec_9798_4_4_udkey_B_text_3_Text5 t r s tid0) note facts = this
    then interpret state: isoiec_9798_4_udkey_composed_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  qed
  thus "isoiec_9798_4_udkey_composed_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_4_udkey_state begin

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

lemma (in restricted_isoiec_9798_4_udkey_state) isoiec_9798_4_1_udkey_B_non_injective_agreement:
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
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_4_1_udkey_A_1_hash tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_isoiec_9798_4_udkey_state) isoiec_9798_4_2_udkey_B_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_4_2_udkey_B"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_4_2_udkey_B_2 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_4_2_udkey_A &
        ( tid1, isoiec_9798_4_2_udkey_A_2 ) : steps t &
        {| s(AV ''A'' tid1), s(MV ''B'' tid1), s(MV ''Rb'' tid1),
           s(MV ''Text2'' tid1)
        |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), LN ''Rb'' tid0,
                s(MV ''Text2'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Hash {| {| LC ''CCF'', K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) |},
                           LC ''isoiec_9798_4_2_ccf_2'', LN ''Rb'' tid0, s(MV ''Text2'' tid0)
                        |} ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_4_2_udkey_A_2_hash tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_isoiec_9798_4_udkey_state) isoiec_9798_4_3_udkey_A_non_injective_agreement:
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
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_4_3_udkey_B_2_hash tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_isoiec_9798_4_udkey_state) isoiec_9798_4_3_udkey_B_non_injective_agreement:
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
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_4_3_udkey_A_1_hash tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_isoiec_9798_4_udkey_state) isoiec_9798_4_4_udkey_A_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_4_4_udkey_A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_4_4_udkey_A_3 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_4_4_udkey_B &
        ( tid1, isoiec_9798_4_4_udkey_B_3 ) : steps t &
        {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(MV ''Ra'' tid1), LN ''Rb'' tid1,
           s(MV ''Text2'' tid1), s(MV ''Text4'' tid1)
        |} = {| s(AV ''A'' tid0), s(MV ''B'' tid0), LN ''Ra'' tid0,
                s(MV ''Rb'' tid0), s(MV ''Text2'' tid0), s(MV ''Text4'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Hash {| {| LC ''CCF'', K ( s(AV ''A'' tid0) ) ( s(MV ''B'' tid0) ) |},
                           LC ''isoiec_9798_4_4_ccf_3'', s(MV ''Rb'' tid0), LN ''Ra'' tid0,
                           s(MV ''Text4'' tid0)
                        |} ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_4_4_udkey_B_3_hash tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Hash {| {| LC ''CCF'', K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid1) ) |},
                             LC ''isoiec_9798_4_4_ccf_2'', LN ''Ra'' tid0, LN ''Rb'' tid1,
                             s(MV ''Text2'' tid1)
                          |} ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest!: ltk_secrecy)
    next
      case (isoiec_9798_4_4_udkey_A_2_hash tid2) note_unified facts = this facts
      thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
    qed (insert facts, fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_isoiec_9798_4_udkey_state) isoiec_9798_4_4_udkey_B_non_injective_agreement:
  assumes facts:
    "roleMap r tid0 = Some isoiec_9798_4_4_udkey_B"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "( tid0, isoiec_9798_4_4_udkey_B_2 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some isoiec_9798_4_4_udkey_A &
        ( tid1, isoiec_9798_4_4_udkey_A_2 ) : steps t &
        {| s(AV ''A'' tid1), s(MV ''B'' tid1), LN ''Ra'' tid1, s(MV ''Rb'' tid1),
           s(MV ''Text2'' tid1)
        |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(MV ''Ra'' tid0),
                LN ''Rb'' tid0, s(MV ''Text2'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Hash {| {| LC ''CCF'', K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) |},
                           LC ''isoiec_9798_4_4_ccf_2'', s(MV ''Ra'' tid0), LN ''Rb'' tid0,
                           s(MV ''Text2'' tid0)
                        |} ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (isoiec_9798_4_4_udkey_A_2_hash tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
  qed (insert facts, fastsimp+)?
qed

end