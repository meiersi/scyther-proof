theory "isoiec-9798_cert_auto"
imports
  "ESPLogic"
begin

role A
where "A =
  [ Recv ''1'' <| sMV ''B'', sAV ''A'', sMV ''Rb'', sMV ''Text1'' |>
  , Recv ''text2'' ( sMV ''Text2'' )
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
  , Recv ''text4'' <| sMV ''Text6'', sMV ''Text7'' |>
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

role Abd
where "Abd =
  [ Recv ''1'' <| sMV ''Bbd'', sAV ''Abd'', sMV ''Rb'', sMV ''Text1'' |>
  , Recv ''text2'' ( sMV ''Text2'' )
  , Send ''2'' <| sAV ''Abd'', sAV ''Pbd'', sN ''Ra'', sMV ''Rb'',
                  sMV ''Bbd'', sMV ''Text2''
               |>
  , Recv ''3'' <| sAV ''Pbd'', sAV ''Abd'', sMV ''Text5'',
                  PEnc <| sC ''isoiec_9798_2_6_enc_3_1'', sN ''Ra'', sMV ''Kab'',
                          sAV ''Abd'', sMV ''Bbd'', sMV ''Text4''
                       |>
                       ( sKbd (AVar ''Abd'') (AVar ''Pbd'') ),
                  sMV ''TokenPA_for_B''
               |>
  , Recv ''text4'' <| sMV ''Text6'', sMV ''Text7'' |>
  , Send ''4'' <| sAV ''Abd'', sMV ''Bbd'', sMV ''Text7'', sAV ''Pbd'',
                  sMV ''TokenPA_for_B'',
                  PEnc <| sC ''isoiec_9798_2_6_enc_4'', sN ''Rpa'', sMV ''Rb'',
                          sMV ''Text6''
                       |>
                       ( sMV ''Kab'' )
               |>
  , Recv ''5'' <| sMV ''Bbd'', sAV ''Abd'', sMV ''Text9'',
                  PEnc <| sC ''isoiec_9798_2_6_enc_5'', sMV ''Rb'', sN ''Rpa'',
                          sMV ''Text8''
                       |>
                       ( sMV ''Kab'' )
               |>
  ]"

role B
where "B =
  [ Recv ''text1'' ( sMV ''Text1'' )
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
  , Recv ''text5'' <| sMV ''Text8'', sMV ''Text9'' |>
  , Send ''5'' <| sAV ''B'', sAV ''A'', sMV ''Text9'',
                  PEnc <| sC ''isoiec_9798_2_6_enc_5'', sN ''Rb'', sMV ''Rpa'',
                          sMV ''Text8''
                       |>
                       ( sMV ''Kab'' )
               |>
  ]"

role Bbd
where "Bbd =
  [ Recv ''text1'' ( sMV ''Text1'' )
  , Send ''1'' <| sAV ''Bbd'', sAV ''Abd'', sN ''Rb'', sMV ''Text1'' |>
  , Recv ''4'' <| sAV ''Abd'', sAV ''Bbd'', sMV ''Text7'', sMV ''Pbd'',
                  PEnc <| sC ''isoiec_9798_2_6_enc_3_2'', sN ''Rb'', sMV ''Kab'',
                          sAV ''Abd'', sAV ''Bbd'', sMV ''Text3''
                       |>
                       ( sKbd (AVar ''Bbd'') (MVar ''Pbd'') ),
                  PEnc <| sC ''isoiec_9798_2_6_enc_4'', sMV ''Rpa'', sN ''Rb'',
                          sMV ''Text6''
                       |>
                       ( sMV ''Kab'' )
               |>
  , Recv ''text5'' <| sMV ''Text8'', sMV ''Text9'' |>
  , Send ''5'' <| sAV ''Bbd'', sAV ''Abd'', sMV ''Text9'',
                  PEnc <| sC ''isoiec_9798_2_6_enc_5'', sN ''Rb'', sMV ''Rpa'',
                          sMV ''Text8''
                       |>
                       ( sMV ''Kab'' )
               |>
  ]"

role P
where "P =
  [ Recv ''2'' <| sMV ''A'', sAV ''P'', sMV ''Ra'', sMV ''Rb'', sMV ''B'',
                  sMV ''Text2''
               |>
  , Recv ''text3'' <| sMV ''Text3'', sMV ''Text4'', sMV ''Text5'' |>
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

role Pbd
where "Pbd =
  [ Recv ''2'' <| sMV ''Abd'', sAV ''Pbd'', sMV ''Ra'', sMV ''Rb'',
                  sMV ''Bbd'', sMV ''Text2''
               |>
  , Recv ''text3'' <| sMV ''Text3'', sMV ''Text4'', sMV ''Text5'' |>
  , Send ''3'' <| sAV ''Pbd'', sMV ''Abd'', sMV ''Text5'',
                  PEnc <| sC ''isoiec_9798_2_6_enc_3_1'', sMV ''Ra'', sN ''Kab'',
                          sMV ''Abd'', sMV ''Bbd'', sMV ''Text4''
                       |>
                       ( sKbd (MVar ''Abd'') (AVar ''Pbd'') ),
                  PEnc <| sC ''isoiec_9798_2_6_enc_3_2'', sMV ''Rb'', sN ''Kab'',
                          sMV ''Abd'', sMV ''Bbd'', sMV ''Text3''
                       |>
                       ( sKbd (MVar ''Bbd'') (AVar ''Pbd'') )
               |>
  ]"

protocol isoiec_9798_2_6
where "isoiec_9798_2_6 = { A, Abd, B, Bbd, P, Pbd }"

locale restricted_isoiec_9798_2_6_state = isoiec_9798_2_6_state

type_invariant typing_2_6 for isoiec_9798_2_6
where "typing_2_6 = mk_typing
  [ ((P, ''A''), (KnownT P_2))
  , ((Pbd, ''Abd''), (KnownT Pbd_2))
  , ((A, ''B''), (KnownT A_1))
  , ((P, ''B''), (KnownT P_2))
  , ((Abd, ''Bbd''), (KnownT Abd_1))
  , ((Pbd, ''Bbd''), (KnownT Pbd_2))
  , ((A, ''Kab''), (SumT (KnownT A_3) (NonceT P ''Kab'')))
  , ((Abd, ''Kab''), (SumT (KnownT Abd_3) (NonceT Pbd ''Kab'')))
  , ((B, ''Kab''), (SumT (KnownT B_4) (NonceT P ''Kab'')))
  , ((Bbd, ''Kab''), (SumT (KnownT Bbd_4) (NonceT Pbd ''Kab'')))
  , ((B, ''P''), (KnownT B_4))
  , ((Bbd, ''Pbd''), (KnownT Bbd_4))
  , ((P, ''Ra''), (KnownT P_2))
  , ((Pbd, ''Ra''), (KnownT Pbd_2))
  , ((A, ''Rb''), (KnownT A_1))
  , ((Abd, ''Rb''), (KnownT Abd_1))
  , ((P, ''Rb''), (KnownT P_2))
  , ((Pbd, ''Rb''), (KnownT Pbd_2))
  , ((B, ''Rpa''),
     (SumT (KnownT B_4) (SumT (NonceT A ''Rpa'') (NonceT Abd ''Rpa''))))
  , ((Bbd, ''Rpa''),
     (SumT (KnownT Bbd_4) (SumT (NonceT A ''Rpa'') (NonceT Abd ''Rpa''))))
  , ((A, ''Text1''), (KnownT A_1))
  , ((Abd, ''Text1''), (KnownT Abd_1))
  , ((B, ''Text1''), (KnownT B_text1))
  , ((Bbd, ''Text1''), (KnownT Bbd_text1))
  , ((A, ''Text2''), (KnownT A_text2))
  , ((Abd, ''Text2''), (KnownT Abd_text2))
  , ((P, ''Text2''), (KnownT P_2))
  , ((Pbd, ''Text2''), (KnownT Pbd_2))
  , ((B, ''Text3''), (KnownT B_4))
  , ((Bbd, ''Text3''), (KnownT Bbd_4))
  , ((P, ''Text3''), (KnownT P_text3))
  , ((Pbd, ''Text3''), (KnownT Pbd_text3))
  , ((A, ''Text4''), (KnownT A_3))
  , ((Abd, ''Text4''), (KnownT Abd_3))
  , ((P, ''Text4''), (KnownT P_text3))
  , ((Pbd, ''Text4''), (KnownT Pbd_text3))
  , ((A, ''Text5''), (KnownT A_3))
  , ((Abd, ''Text5''), (KnownT Abd_3))
  , ((P, ''Text5''), (KnownT P_text3))
  , ((Pbd, ''Text5''), (KnownT Pbd_text3))
  , ((A, ''Text6''), (KnownT A_text4))
  , ((Abd, ''Text6''), (KnownT Abd_text4))
  , ((B, ''Text6''), (KnownT B_4))
  , ((Bbd, ''Text6''), (KnownT Bbd_4))
  , ((A, ''Text7''), (KnownT A_text4))
  , ((Abd, ''Text7''), (KnownT Abd_text4))
  , ((B, ''Text7''), (KnownT B_4))
  , ((Bbd, ''Text7''), (KnownT Bbd_4))
  , ((A, ''Text8''), (KnownT A_5))
  , ((Abd, ''Text8''), (KnownT Abd_5))
  , ((B, ''Text8''), (KnownT B_text5))
  , ((Bbd, ''Text8''), (KnownT Bbd_text5))
  , ((A, ''Text9''), (KnownT A_5))
  , ((Abd, ''Text9''), (KnownT Abd_5))
  , ((B, ''Text9''), (KnownT B_text5))
  , ((Bbd, ''Text9''), (KnownT Bbd_text5))
  , ((A, ''TokenPA_for_B''), (KnownT A_3))
  , ((Abd, ''TokenPA_for_B''), (KnownT Abd_3))
  ]"

sublocale isoiec_9798_2_6_state < typing_2_6_state
proof -
  have "(t,r,s) : approx typing_2_6"
  proof(cases rule: reachable_in_approxI_ext
        [OF typing_2_6.monoTyp, completeness_cases_rule])
    case (A_1_B t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_1_B
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (A_1_Rb t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_1_Rb
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (A_1_Text1 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_1_Text1
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (A_3_Kab t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_3_Kab
    thus ?case
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid0,
               s(MV ''Kab'' tid0), s(MV ''B'' tid0), s(MV ''Text4'' tid0)
            |}
            ( K ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (A_3_Text4 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_3_Text4
    thus ?case
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid0,
               s(MV ''Kab'' tid0), s(MV ''B'' tid0), s(MV ''Text4'' tid0)
            |}
            ( K ( s(AV ''A'' tid0) ) ( s(AV ''P'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (A_3_Text5 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_3_Text5
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (A_3_TokenPA_for_B t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_3_TokenPA_for_B
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (A_text4_Text6 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_text4_Text6
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (A_text4_Text7 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_text4_Text7
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (A_5_Text8 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_5_Text8
    thus ?case
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_5'', s(MV ''Rb'' tid0), LN ''Rpa'' tid0,
               s(MV ''Text8'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (A_5_Text9 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_5_Text9
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Abd_1_Bbd t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Abd_1_Bbd
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Abd_1_Rb t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Abd_1_Rb
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Abd_1_Text1 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Abd_1_Text1
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Abd_3_Kab t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Abd_3_Kab
    thus ?case
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid0,
               s(MV ''Kab'' tid0), s(AV ''Abd'' tid0), s(MV ''Bbd'' tid0),
               s(MV ''Text4'' tid0)
            |}
            ( Kbd ( s(AV ''Abd'' tid0) ) ( s(AV ''Pbd'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (Abd_3_Text4 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Abd_3_Text4
    thus ?case
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_3_1'', LN ''Ra'' tid0,
               s(MV ''Kab'' tid0), s(AV ''Abd'' tid0), s(MV ''Bbd'' tid0),
               s(MV ''Text4'' tid0)
            |}
            ( Kbd ( s(AV ''Abd'' tid0) ) ( s(AV ''Pbd'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (Abd_3_Text5 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Abd_3_Text5
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Abd_3_TokenPA_for_B t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Abd_3_TokenPA_for_B
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Abd_text4_Text6 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Abd_text4_Text6
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Abd_text4_Text7 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Abd_text4_Text7
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Abd_5_Text8 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Abd_5_Text8
    thus ?case
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_5'', s(MV ''Rb'' tid0), LN ''Rpa'' tid0,
               s(MV ''Text8'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (Abd_5_Text9 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Abd_5_Text9
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (B_4_Kab t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = B_4_Kab
    thus ?case
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid0,
               s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''Text3'' tid0)
            |}
            ( K ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (B_4_P t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = B_4_P
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (B_4_Rpa t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = B_4_Rpa
    thus ?case
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_4'', s(MV ''Rpa'' tid0), LN ''Rb'' tid0,
               s(MV ''Text6'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (B_4_Text3 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = B_4_Text3
    thus ?case
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid0,
               s(MV ''Kab'' tid0), s(AV ''A'' tid0), s(MV ''Text3'' tid0)
            |}
            ( K ( s(AV ''B'' tid0) ) ( s(MV ''P'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (B_4_Text6 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = B_4_Text6
    thus ?case
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_4'', s(MV ''Rpa'' tid0), LN ''Rb'' tid0,
               s(MV ''Text6'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (B_4_Text7 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = B_4_Text7
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (B_text5_Text8 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = B_text5_Text8
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (B_text5_Text9 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = B_text5_Text9
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Bbd_4_Kab t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Bbd_4_Kab
    thus ?case
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid0,
               s(MV ''Kab'' tid0), s(AV ''Abd'' tid0), s(AV ''Bbd'' tid0),
               s(MV ''Text3'' tid0)
            |}
            ( Kbd ( s(AV ''Bbd'' tid0) ) ( s(MV ''Pbd'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (Bbd_4_Pbd t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Bbd_4_Pbd
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Bbd_4_Rpa t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Bbd_4_Rpa
    thus ?case
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_4'', s(MV ''Rpa'' tid0), LN ''Rb'' tid0,
               s(MV ''Text6'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (Bbd_4_Text3 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Bbd_4_Text3
    thus ?case
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_3_2'', LN ''Rb'' tid0,
               s(MV ''Kab'' tid0), s(AV ''Abd'' tid0), s(AV ''Bbd'' tid0),
               s(MV ''Text3'' tid0)
            |}
            ( Kbd ( s(AV ''Bbd'' tid0) ) ( s(MV ''Pbd'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (Bbd_4_Text6 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Bbd_4_Text6
    thus ?case
    proof(sources! "
        Enc {| LC ''isoiec_9798_2_6_enc_4'', s(MV ''Rpa'' tid0), LN ''Rb'' tid0,
               s(MV ''Text6'' tid0)
            |}
            ( s(MV ''Kab'' tid0) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (Bbd_4_Text7 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Bbd_4_Text7
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Bbd_text5_Text8 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Bbd_text5_Text8
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Bbd_text5_Text9 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Bbd_text5_Text9
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (P_2_A t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = P_2_A
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (P_2_B t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = P_2_B
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (P_2_Ra t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = P_2_Ra
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (P_2_Rb t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = P_2_Rb
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (P_2_Text2 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = P_2_Text2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (P_text3_Text3 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = P_text3_Text3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (P_text3_Text4 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = P_text3_Text4
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (P_text3_Text5 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = P_text3_Text5
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Pbd_2_Abd t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Pbd_2_Abd
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Pbd_2_Bbd t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Pbd_2_Bbd
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Pbd_2_Ra t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Pbd_2_Ra
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Pbd_2_Rb t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Pbd_2_Rb
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Pbd_2_Text2 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Pbd_2_Text2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Pbd_text3_Text3 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Pbd_text3_Text3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Pbd_text3_Text4 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Pbd_text3_Text4
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Pbd_text3_Text5 t r s tid0)
    then interpret state: typing_2_6_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Pbd_text3_Text5
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "typing_2_6_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context isoiec_9798_2_6_state begin

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

end