theory "ASW_optimistic_contract_cert_auto"
imports
  "ESPLogic"
begin

(* section:  Optimistic fair exchange following Asokan, Shoup, Waidner  *)

(* text: 

We model the contract signing example from 

  N. Asokan, V. Shoup, and M. Waidner. Asynchronous protocols for optimistic
  fair exchange. In Proceedings of the IEEE Symposium on Research in Security
  and Privacy, pages 86--99. IEEE Computer Society Press, 1998. 

Since role scripts are linear, we model the non-deterministic choice to
abort as separate roles that share the same prefix with the non-aborting role.
The trusted party is therefore split into Ta and Tr which run only the
abort protocol or only the resolve protocol.

 *)

role A
where "A =
  [ Recv ''0regular'' ( PEnc <| sC ''bind'', sAV ''T'', sMV ''n'' |>
                             ( sSK ''T'' )
                      )
  , Send ''1regular'' ( PEnc <| sAV ''A'', sAV ''B'', sAV ''T'', sMV ''n'',
                                sC ''text'', PHash ( sN ''sA'' )
                             |>
                             ( sSK ''A'' )
                      )
  , Recv ''2regular'' ( PEnc <| PEnc <| sAV ''A'', sAV ''B'', sAV ''T'',
                                        sMV ''n'', sC ''text'', PHash ( sN ''sA'' )
                                     |>
                                     ( sSK ''A'' ),
                                sMV ''cB''
                             |>
                             ( sSK ''B'' )
                      )
  , Send ''3regular'' ( sN ''sA'' )
  , Recv ''5regular'' ( sMV ''sB'' )
  , MatchEq ''6regular'' ( MVar ''cB'' ) ( PHash ( sMV ''sB'' ) )
  ]"

role Aa
where "Aa =
  [ Recv ''0abort'' ( PEnc <| sC ''bind'', sAV ''T'', sMV ''n'' |>
                           ( sSK ''T'' )
                    )
  , Send ''1abort'' ( PEnc <| sAV ''A'', sAV ''B'', sAV ''T'', sMV ''n'',
                              sC ''text'', PHash ( sN ''sA'' )
                           |>
                           ( sSK ''A'' )
                    )
  , Send ''2abort'' ( PEnc <| sC ''aborted'',
                              PEnc <| sAV ''A'', sAV ''B'', sAV ''T'', sMV ''n'', sC ''text'',
                                      PHash ( sN ''sA'' )
                                   |>
                                   ( sSK ''A'' )
                           |>
                           ( sSK ''A'' )
                    )
  , Recv ''3abort'' ( PEnc <| sC ''aborted'',
                              PEnc <| sC ''aborted'',
                                      PEnc <| sAV ''A'', sAV ''B'', sAV ''T'', sMV ''n'', sC ''text'',
                                              PHash ( sN ''sA'' )
                                           |>
                                           ( sSK ''A'' )
                                   |>
                                   ( sSK ''A'' )
                           |>
                           ( sSK ''T'' )
                    )
  ]"

role B
where "B =
  [ Recv ''1regular'' ( PEnc <| sAV ''A'', sAV ''B'', sAV ''T'', sMV ''n'',
                                sC ''text'', sMV ''cA''
                             |>
                             ( sSK ''A'' )
                      )
  , Send ''2regular'' ( PEnc <| PEnc <| sAV ''A'', sAV ''B'', sAV ''T'',
                                        sMV ''n'', sC ''text'', sMV ''cA''
                                     |>
                                     ( sSK ''A'' ),
                                PHash ( sN ''sB'' )
                             |>
                             ( sSK ''B'' )
                      )
  , Recv ''3regular'' ( sMV ''sA'' )
  , MatchEq ''4regular'' ( MVar ''cA'' ) ( PHash ( sMV ''sA'' ) )
  , Send ''5regular'' ( sN ''sB'' )
  ]"

role Ta
where "Ta =
  [ Send ''00abort'' ( PEnc <| sC ''bind'', sAV ''T'', sN ''n'' |>
                            ( sSK ''T'' )
                     )
  , Recv ''2abort'' ( PEnc <| sC ''aborted'',
                              PEnc <| sMV ''A'', sMV ''B'', sAV ''T'', sN ''n'', sC ''text'',
                                      sMV ''cA''
                                   |>
                                   ( PAsymSK ( sMV ''A'' ) )
                           |>
                           ( PAsymSK ( sMV ''A'' ) )
                    )
  , Send ''3abort'' ( PEnc <| sC ''aborted'',
                              PEnc <| sC ''aborted'',
                                      PEnc <| sMV ''A'', sMV ''B'', sAV ''T'', sN ''n'', sC ''text'',
                                              sMV ''cA''
                                           |>
                                           ( PAsymSK ( sMV ''A'' ) )
                                   |>
                                   ( PAsymSK ( sMV ''A'' ) )
                           |>
                           ( sSK ''T'' )
                    )
  ]"

role Tr
where "Tr =
  [ Send ''00resolve'' ( PEnc <| sC ''bind'', sAV ''T'', sN ''n'' |>
                              ( sSK ''T'' )
                       )
  , Recv ''resolve1'' <| PEnc <| sMV ''A'', sMV ''B'', sAV ''T'', sN ''n'',
                                 sC ''text'', sMV ''cA''
                              |>
                              ( PAsymSK ( sMV ''A'' ) ),
                         PEnc <| PEnc <| sMV ''A'', sMV ''B'', sAV ''T'', sN ''n'', sC ''text'',
                                         sMV ''cA''
                                      |>
                                      ( PAsymSK ( sMV ''A'' ) ),
                                 sMV ''cB''
                              |>
                              ( PAsymSK ( sMV ''B'' ) )
                      |>
  , Send ''resolve2'' ( PEnc <| PEnc <| sMV ''A'', sMV ''B'', sAV ''T'',
                                        sN ''n'', sC ''text'', sMV ''cA''
                                     |>
                                     ( PAsymSK ( sMV ''A'' ) ),
                                PEnc <| PEnc <| sMV ''A'', sMV ''B'', sAV ''T'', sN ''n'', sC ''text'',
                                                sMV ''cA''
                                             |>
                                             ( PAsymSK ( sMV ''A'' ) ),
                                        sMV ''cB''
                                     |>
                                     ( PAsymSK ( sMV ''B'' ) )
                             |>
                             ( sSK ''T'' )
                      )
  ]"

role V
where "V =
  [ Recv ''verify'' <| PEnc <| sMV ''A'', sMV ''B'', sAV ''T'', sMV ''n'',
                               sC ''text'', PHash ( sMV ''sA'' )
                            |>
                            ( PAsymSK ( sMV ''A'' ) ),
                       sMV ''sA'',
                       PEnc <| PEnc <| sMV ''A'', sMV ''B'', sAV ''T'', sMV ''n'', sC ''text'',
                                       PHash ( sMV ''sA'' )
                                    |>
                                    ( PAsymSK ( sMV ''A'' ) ),
                               PHash ( sMV ''sB'' )
                            |>
                            ( PAsymSK ( sMV ''B'' ) ),
                       sMV ''sB''
                    |>
  ]"

role Vr
where "Vr =
  [ Recv ''verifyr'' ( PEnc <| PEnc <| sMV ''A'', sMV ''B'', sAV ''T'',
                                       sMV ''n'', sC ''text'', sMV ''cA''
                                    |>
                                    ( PAsymSK ( sMV ''A'' ) ),
                               PEnc <| PEnc <| sMV ''A'', sMV ''B'', sAV ''T'', sMV ''n'', sC ''text'',
                                               sMV ''cA''
                                            |>
                                            ( PAsymSK ( sMV ''A'' ) ),
                                       sMV ''cB''
                                    |>
                                    ( PAsymSK ( sMV ''B'' ) )
                            |>
                            ( sSK ''T'' )
                     )
  ]"

protocol Contract
where "Contract = { A, Aa, B, Ta, Tr, V, Vr }"

locale restricted_Contract_state = Contract_state

(* subsection:  Security Properties  *)

type_invariant Contract_typing for Contract
where "Contract_typing = mk_typing
  [ ((Ta, ''A''), (SumT (KnownT Ta_2abort) AgentT))
  , ((Tr, ''A''), (SumT (KnownT Tr_resolve1) AgentT))
  , ((V, ''A''), (SumT (KnownT V_verify) AgentT))
  , ((Vr, ''A''), (SumT (KnownT Vr_verifyr) AgentT))
  , ((Ta, ''B''), (SumT (KnownT Ta_2abort) AgentT))
  , ((Tr, ''B''), (SumT (KnownT Tr_resolve1) AgentT))
  , ((V, ''B''), (SumT (KnownT V_verify) AgentT))
  , ((Vr, ''B''), (SumT (KnownT Vr_verifyr) AgentT))
  , ((B, ''cA''),
     (SumT (KnownT B_1regular) (SumT (HashT (NonceT A ''sA'')) (HashT (NonceT Aa ''sA'')))))
  , ((Ta, ''cA''),
     (SumT (KnownT Ta_2abort) (SumT (HashT (NonceT A ''sA'')) (HashT (NonceT Aa ''sA'')))))
  , ((Tr, ''cA''),
     (SumT (KnownT Tr_resolve1) (SumT (HashT (NonceT A ''sA'')) (HashT (NonceT Aa ''sA'')))))
  , ((Vr, ''cA''),
     (SumT (KnownT Vr_verifyr) (SumT (HashT (NonceT A ''sA'')) (HashT (NonceT Aa ''sA'')))))
  , ((A, ''cB''), (SumT (KnownT A_2regular) (HashT (NonceT B ''sB''))))
  , ((Tr, ''cB''), (SumT (KnownT Tr_resolve1) (HashT (NonceT B ''sB''))))
  , ((Vr, ''cB''), (SumT (KnownT Vr_verifyr) (HashT (NonceT B ''sB''))))
  , ((A, ''n''),
     (SumT (KnownT A_0regular) (SumT (NonceT Ta ''n'') (NonceT Tr ''n''))))
  , ((Aa, ''n''),
     (SumT (KnownT Aa_0abort) (SumT (NonceT Ta ''n'') (NonceT Tr ''n''))))
  , ((B, ''n''),
     (SumT (KnownT B_1regular) (SumT (NonceT Ta ''n'') (NonceT Tr ''n''))))
  , ((V, ''n''),
     (SumT (KnownT V_verify) (SumT (NonceT Ta ''n'') (NonceT Tr ''n''))))
  , ((Vr, ''n''),
     (SumT (KnownT Vr_verifyr) (SumT (NonceT Ta ''n'') (NonceT Tr ''n''))))
  , ((B, ''sA''), (KnownT B_3regular))
  , ((V, ''sA''), (SumT (KnownT V_verify) (NonceT A ''sA'')))
  , ((A, ''sB''), (KnownT A_5regular))
  , ((V, ''sB''), (SumT (KnownT V_verify) (NonceT B ''sB'')))
  ]"

sublocale Contract_state < Contract_typing_state
proof -
  have "(t,r,s) : approx Contract_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF Contract_typing.monoTyp, completeness_cases_rule])
    case (A_0regular_n t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_0regular_n
    thus ?case
    proof(sources! "
        Enc {| LC ''bind'', s(AV ''T'' tid0), s(MV ''n'' tid0) |}
            ( SK ( s(AV ''T'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (A_2regular_cB t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_2regular_cB
    thus ?case
    proof(sources! "
        Enc {| Enc {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(AV ''T'' tid0),
                      s(MV ''n'' tid0), LC ''text'', Hash ( LN ''sA'' tid0 )
                   |}
                   ( SK ( s(AV ''A'' tid0) ) ),
               s(MV ''cB'' tid0)
            |}
            ( SK ( s(AV ''B'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (Aa_0abort_n t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Aa_0abort_n
    thus ?case
    proof(sources! "
        Enc {| LC ''bind'', s(AV ''T'' tid0), s(MV ''n'' tid0) |}
            ( SK ( s(AV ''T'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (B_1regular_cA t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = B_1regular_cA
    thus ?case
    proof(sources! "
        Enc {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(AV ''T'' tid0),
               s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
            |}
            ( SK ( s(AV ''A'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (B_1regular_n t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = B_1regular_n
    thus ?case
    proof(sources! "
        Enc {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(AV ''T'' tid0),
               s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
            |}
            ( SK ( s(AV ''A'' tid0) ) ) ")
      case (A_1regular_enc tid1) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''bind'', s(AV ''T'' tid0), s(MV ''n'' tid0) |}
                           ( SK ( s(AV ''T'' tid0) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
    next
      case (Aa_1abort_enc tid1) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''bind'', s(AV ''T'' tid0), s(MV ''n'' tid0) |}
                           ( SK ( s(AV ''T'' tid0) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
    next
      case (Aa_2abort_enc_1 tid1) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''bind'', s(AV ''T'' tid0), s(MV ''n'' tid0) |}
                           ( SK ( s(AV ''T'' tid0) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (Ta_2abort_A t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Ta_2abort_A
    thus ?case
    proof(sources! "
        Enc {| LC ''aborted'',
               Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                      LN ''n'' tid0, LC ''text'', s(MV ''cA'' tid0)
                   |}
                   ( SK ( s(MV ''A'' tid0) ) )
            |}
            ( SK ( s(MV ''A'' tid0) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                              LN ''n'' tid0, LC ''text'', s(MV ''cA'' tid0)
                           |}
                           ( SK ( s(MV ''A'' tid0) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits) | ((clarsimp, order?) | order | fast))+)?)
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (Ta_2abort_B t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Ta_2abort_B
    thus ?case
    proof(sources! "
        Enc {| LC ''aborted'',
               Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                      LN ''n'' tid0, LC ''text'', s(MV ''cA'' tid0)
                   |}
                   ( SK ( s(MV ''A'' tid0) ) )
            |}
            ( SK ( s(MV ''A'' tid0) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                              LN ''n'' tid0, LC ''text'', s(MV ''cA'' tid0)
                           |}
                           ( SK ( s(MV ''A'' tid0) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits) | ((clarsimp, order?) | order | fast))+)?)
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (Ta_2abort_cA t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Ta_2abort_cA
    thus ?case
    proof(sources! "
        Enc {| LC ''aborted'',
               Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                      LN ''n'' tid0, LC ''text'', s(MV ''cA'' tid0)
                   |}
                   ( SK ( s(MV ''A'' tid0) ) )
            |}
            ( SK ( s(MV ''A'' tid0) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                              LN ''n'' tid0, LC ''text'', s(MV ''cA'' tid0)
                           |}
                           ( SK ( s(MV ''A'' tid0) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits) | ((clarsimp, order?) | order | fast))+)?)
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (Tr_resolve1_A t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Tr_resolve1_A
    thus ?case
    proof(sources! "
        Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
               LN ''n'' tid0, LC ''text'', s(MV ''cA'' tid0)
            |}
            ( SK ( s(MV ''A'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (Tr_resolve1_B t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Tr_resolve1_B
    thus ?case
    proof(sources! "
        Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
               LN ''n'' tid0, LC ''text'', s(MV ''cA'' tid0)
            |}
            ( SK ( s(MV ''A'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (Tr_resolve1_cA t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Tr_resolve1_cA
    thus ?case
    proof(sources! "
        Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
               LN ''n'' tid0, LC ''text'', s(MV ''cA'' tid0)
            |}
            ( SK ( s(MV ''A'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (Tr_resolve1_cB t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Tr_resolve1_cB
    thus ?case
    proof(sources! "
        Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                      LN ''n'' tid0, LC ''text'', s(MV ''cA'' tid0)
                   |}
                   ( SK ( s(MV ''A'' tid0) ) ),
               s(MV ''cB'' tid0)
            |}
            ( SK ( s(MV ''B'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (V_verify_A t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = V_verify_A
    thus ?case
    proof(sources! "
        Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
               s(MV ''n'' tid0), LC ''text'', Hash ( s(MV ''sA'' tid0) )
            |}
            ( SK ( s(MV ''A'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (V_verify_B t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = V_verify_B
    thus ?case
    proof(sources! "
        Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
               s(MV ''n'' tid0), LC ''text'', Hash ( s(MV ''sA'' tid0) )
            |}
            ( SK ( s(MV ''A'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (V_verify_n t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = V_verify_n
    thus ?case
    proof(sources! "
        Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
               s(MV ''n'' tid0), LC ''text'', Hash ( s(MV ''sA'' tid0) )
            |}
            ( SK ( s(MV ''A'' tid0) ) ) ")
      case (A_1regular_enc tid1) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''bind'', s(AV ''T'' tid0), s(MV ''n'' tid0) |}
                           ( SK ( s(AV ''T'' tid0) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
    next
      case (Aa_1abort_enc tid1) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''bind'', s(AV ''T'' tid0), s(MV ''n'' tid0) |}
                           ( SK ( s(AV ''T'' tid0) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
    next
      case (Aa_2abort_enc_1 tid1) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''bind'', s(AV ''T'' tid0), s(MV ''n'' tid0) |}
                           ( SK ( s(AV ''T'' tid0) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (V_verify_sA t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = V_verify_sA
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (V_verify_sB t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = V_verify_sB
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (Vr_verifyr_A t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Vr_verifyr_A
    thus ?case
    proof(sources! "
        Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                      s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                   |}
                   ( SK ( s(MV ''A'' tid0) ) ),
               Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                             s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                          |}
                          ( SK ( s(MV ''A'' tid0) ) ),
                      s(MV ''cB'' tid0)
                   |}
                   ( SK ( s(MV ''B'' tid0) ) )
            |}
            ( SK ( s(AV ''T'' tid0) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                              s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                           |}
                           ( SK ( s(MV ''A'' tid0) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
    next
      case (Tr_resolve2_enc tid1) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                              LN ''n'' tid1, LC ''text'', s(MV ''cA'' tid0)
                           |}
                           ( SK ( s(MV ''A'' tid0) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  next
    case (Vr_verifyr_B t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Vr_verifyr_B
    thus ?case
    proof(sources! "
        Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                      s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                   |}
                   ( SK ( s(MV ''A'' tid0) ) ),
               Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                             s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                          |}
                          ( SK ( s(MV ''A'' tid0) ) ),
                      s(MV ''cB'' tid0)
                   |}
                   ( SK ( s(MV ''B'' tid0) ) )
            |}
            ( SK ( s(AV ''T'' tid0) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                              s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                           |}
                           ( SK ( s(MV ''A'' tid0) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
    next
      case (Tr_resolve2_enc tid1) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                              LN ''n'' tid1, LC ''text'', s(MV ''cA'' tid0)
                           |}
                           ( SK ( s(MV ''A'' tid0) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  next
    case (Vr_verifyr_cA t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Vr_verifyr_cA
    thus ?case
    proof(sources! "
        Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                      s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                   |}
                   ( SK ( s(MV ''A'' tid0) ) ),
               Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                             s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                          |}
                          ( SK ( s(MV ''A'' tid0) ) ),
                      s(MV ''cB'' tid0)
                   |}
                   ( SK ( s(MV ''B'' tid0) ) )
            |}
            ( SK ( s(AV ''T'' tid0) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                              s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                           |}
                           ( SK ( s(MV ''A'' tid0) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
    next
      case (Tr_resolve2_enc tid1) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                              LN ''n'' tid1, LC ''text'', s(MV ''cA'' tid0)
                           |}
                           ( SK ( s(MV ''A'' tid0) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  next
    case (Vr_verifyr_cB t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Vr_verifyr_cB
    thus ?case
    proof(sources! "
        Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                      s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                   |}
                   ( SK ( s(MV ''A'' tid0) ) ),
               Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                             s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                          |}
                          ( SK ( s(MV ''A'' tid0) ) ),
                      s(MV ''cB'' tid0)
                   |}
                   ( SK ( s(MV ''B'' tid0) ) )
            |}
            ( SK ( s(AV ''T'' tid0) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                                     s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                                  |}
                                  ( SK ( s(MV ''A'' tid0) ) ),
                              s(MV ''cB'' tid0)
                           |}
                           ( SK ( s(MV ''B'' tid0) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
    next
      case (Tr_resolve2_enc tid1) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                                     LN ''n'' tid1, LC ''text'', s(MV ''cA'' tid0)
                                  |}
                                  ( SK ( s(MV ''A'' tid0) ) ),
                              s(MV ''cB'' tid0)
                           |}
                           ( SK ( s(MV ''B'' tid0) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  next
    case (Vr_verifyr_n t r s tid0)
    then interpret state: Contract_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = Vr_verifyr_n
    thus ?case
    proof(sources! "
        Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                      s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                   |}
                   ( SK ( s(MV ''A'' tid0) ) ),
               Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                             s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                          |}
                          ( SK ( s(MV ''A'' tid0) ) ),
                      s(MV ''cB'' tid0)
                   |}
                   ( SK ( s(MV ''B'' tid0) ) )
            |}
            ( SK ( s(AV ''T'' tid0) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                              s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                           |}
                           ( SK ( s(MV ''A'' tid0) ) ) ")
        case (A_1regular_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''bind'', s(AV ''T'' tid0), s(MV ''n'' tid0) |}
                             ( SK ( s(AV ''T'' tid0) ) ) ")
        qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
      next
        case (Aa_1abort_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''bind'', s(AV ''T'' tid0), s(MV ''n'' tid0) |}
                             ( SK ( s(AV ''T'' tid0) ) ) ")
        qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
      next
        case (Aa_2abort_enc_1 tid1) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''bind'', s(AV ''T'' tid0), s(MV ''n'' tid0) |}
                             ( SK ( s(AV ''T'' tid0) ) ) ")
        qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  qed
  thus "Contract_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context Contract_state begin

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

lemma (in restricted_Contract_state) regular_agree_A:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some A &
          RLKR(s(AV ''A'' tid0)) ~: reveals t &
          RLKR(s(AV ''B'' tid0)) ~: reveals t & ( tid0, A_6regular ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some B &
          ( tid1, B_5regular ) : steps t &
          {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(AV ''T'' tid1),
             s(MV ''n'' tid1), s(MV ''sA'' tid1), LN ''sB'' tid1
          |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(AV ''T'' tid0),
                  s(MV ''n'' tid0), LN ''sA'' tid0, s(MV ''sB'' tid0)
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
                       Enc {| Enc {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(AV ''T'' tid0),
                                     s(MV ''n'' tid0), LC ''text'', Hash ( LN ''sA'' tid0 )
                                  |}
                                  ( SK ( s(AV ''A'' tid0) ) ),
                              Hash ( s(MV ''sB'' tid0) )
                           |}
                           ( SK ( s(AV ''B'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (B_2regular_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! " LN ''sB'' tid1 ")
          case B_5regular_sB note_unified facts = this facts
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

lemma (in restricted_Contract_state) regular_agree_B:
  assumes facts:
    "roleMap r tid0 = Some B"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "( tid0, B_4regular ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some A &
        ( tid1, A_3regular ) : steps t &
        {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(AV ''T'' tid1),
           s(MV ''n'' tid1), LN ''sA'' tid1
        |} = {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(AV ''T'' tid0),
                s(MV ''n'' tid0), s(MV ''sA'' tid0)
             |})"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| s(AV ''A'' tid0), s(AV ''B'' tid0), s(AV ''T'' tid0),
                          s(MV ''n'' tid0), LC ''text'', Hash ( s(MV ''sA'' tid0) )
                       |}
                       ( SK ( s(AV ''A'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (A_1regular_enc tid1) note_unified facts = this facts
    thus ?thesis proof(sources! " LN ''sA'' tid1 ")
      case A_3regular_sA note_unified facts = this facts
      thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  next
    case (Aa_1abort_enc tid1) note_unified facts = this facts
    thus ?thesis proof(sources! " LN ''sA'' tid1 ")
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  next
    case (Aa_2abort_enc_1 tid1) note_unified facts = this facts
    thus ?thesis proof(sources! " LN ''sA'' tid1 ")
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_Contract_state) regular_verified:
  assumes facts:
    "roleMap r tid0 = Some V"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "( tid0, V_verify ) : steps t"
  shows
    "(?  tid1.
        (?  tid2.
           roleMap r tid1 = Some A &
           roleMap r tid2 = Some B &
           ( tid1, A_3regular ) : steps t &
           ( tid2, B_5regular ) : steps t &
           s(MV ''A'' tid0) = s(AV ''A'' tid1) &
           s(MV ''A'' tid0) = s(AV ''A'' tid2) &
           s(MV ''B'' tid0) = s(AV ''B'' tid1) &
           s(MV ''B'' tid0) = s(AV ''B'' tid2) &
           s(AV ''T'' tid0) = s(AV ''T'' tid1) &
           s(AV ''T'' tid0) = s(AV ''T'' tid2) &
           s(MV ''n'' tid0) = s(MV ''n'' tid1) &
           s(MV ''n'' tid0) = s(MV ''n'' tid2) &
           s(MV ''sA'' tid0) = LN ''sA'' tid1 &
           s(MV ''sB'' tid0) = LN ''sB'' tid2))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                          s(MV ''n'' tid0), LC ''text'', Hash ( s(MV ''sA'' tid0) )
                       |}
                       ( SK ( s(MV ''A'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (A_1regular_enc tid1) note_unified facts = this facts
    thus ?thesis proof(sources! " LN ''sA'' tid1 ")
      case A_3regular_sA note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| Enc {| s(AV ''A'' tid1), s(AV ''B'' tid1), s(AV ''T'' tid0),
                                     s(MV ''n'' tid0), LC ''text'', Hash ( LN ''sA'' tid1 )
                                  |}
                                  ( SK ( s(AV ''A'' tid1) ) ),
                              Hash ( s(MV ''sB'' tid0) )
                           |}
                           ( SK ( s(AV ''B'' tid1) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (B_2regular_enc tid2) note_unified facts = this facts
        thus ?thesis proof(sources! " LN ''sB'' tid2 ")
          case B_5regular_sB note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  next
    case (Aa_1abort_enc tid1) note_unified facts = this facts
    thus ?thesis proof(sources! " LN ''sA'' tid1 ")
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  next
    case (Aa_2abort_enc_1 tid1) note_unified facts = this facts
    thus ?thesis proof(sources! " LN ''sA'' tid1 ")
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_Contract_state) resolve_verified:
  assumes facts:
    "roleMap r tid0 = Some Vr"
    "RLKR(s(AV ''T'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "( tid0, Vr_verifyr ) : steps t"
  shows
    "(?  tid1.
        (?  tid2.
           roleMap r tid2 = Some B &
           ( tid2, B_2regular ) : steps t &
           s(MV ''A'' tid0) = s(AV ''A'' tid2) &
           s(MV ''B'' tid0) = s(AV ''B'' tid2) &
           s(AV ''T'' tid0) = s(AV ''T'' tid2) &
           s(MV ''n'' tid0) = s(MV ''n'' tid2) &
           s(MV ''cB'' tid0) = Hash ( LN ''sB'' tid2 ) &
           ((roleMap r tid1 = Some A &
             ( tid1, A_1regular ) : steps t &
             s(MV ''A'' tid0) = s(AV ''A'' tid1) &
             s(MV ''B'' tid0) = s(AV ''B'' tid1) &
             s(AV ''T'' tid0) = s(AV ''T'' tid1) &
             s(MV ''n'' tid0) = s(MV ''n'' tid1) &
             s(MV ''cA'' tid0) = Hash ( LN ''sA'' tid1 )) |
            (roleMap r tid1 = Some Aa &
             ( tid1, Aa_1abort ) : steps t &
             s(MV ''A'' tid0) = s(AV ''A'' tid1) &
             s(MV ''B'' tid0) = s(AV ''B'' tid1) &
             s(AV ''T'' tid0) = s(AV ''T'' tid1) &
             s(MV ''n'' tid0) = s(MV ''n'' tid1) &
             s(MV ''cA'' tid0) = Hash ( LN ''sA'' tid1 )))))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                                 s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                              |}
                              ( SK ( s(MV ''A'' tid0) ) ),
                          Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                                        s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                                     |}
                                     ( SK ( s(MV ''A'' tid0) ) ),
                                 s(MV ''cB'' tid0)
                              |}
                              ( SK ( s(MV ''B'' tid0) ) )
                       |}
                       ( SK ( s(AV ''T'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (Tr_resolve2_enc tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                                   LN ''n'' tid1, LC ''text'', s(MV ''cA'' tid0)
                                |}
                                ( SK ( s(MV ''A'' tid0) ) ),
                            s(MV ''cB'' tid0)
                         |}
                         ( SK ( s(MV ''B'' tid0) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (auto dest!: ltk_secrecy)
    next
      case (B_2regular_enc tid2) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| s(AV ''A'' tid2), s(AV ''B'' tid2), s(AV ''T'' tid0),
                              LN ''n'' tid1, LC ''text'', s(MV ''cA'' tid0)
                           |}
                           ( SK ( s(AV ''A'' tid2) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (A_1regular_enc tid3) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      next
        case (Aa_1abort_enc tid3) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      next
        case (Aa_2abort_enc_1 tid3) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_Contract_state) regular_verified_not_aborted:
  assumes facts:
    "roleMap r tid0 = Some V"
    "RLKR(s(AV ''T'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, V_verify ) : steps t"
    "Enc {| LC ''aborted'',
            Enc {| LC ''aborted'',
                   Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                          s(MV ''n'' tid0), LC ''text'', LN ''cA'' tid0
                       |}
                       ( SK ( s(MV ''A'' tid0) ) )
                |}
                ( SK ( s(MV ''A'' tid0) ) )
         |}
         ( SK ( s(AV ''T'' tid0) ) ) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''aborted'',
                          Enc {| LC ''aborted'',
                                 Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                                        s(MV ''n'' tid0), LC ''text'', LN ''cA'' tid0
                                     |}
                                     ( SK ( s(MV ''A'' tid0) ) )
                              |}
                              ( SK ( s(MV ''A'' tid0) ) )
                       |}
                       ( SK ( s(AV ''T'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (Ta_3abort_enc tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''aborted'',
                            Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                                   LN ''n'' tid1, LC ''text'', LN ''cA'' tid0
                                |}
                                ( SK ( s(MV ''A'' tid0) ) )
                         |}
                         ( SK ( s(MV ''A'' tid0) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (auto dest!: ltk_secrecy)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_Contract_state) resolve_verified_not_aborted:
  assumes facts:
    "roleMap r tid0 = Some Vr"
    "RLKR(s(AV ''T'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, Vr_verifyr ) : steps t"
    "Enc {| LC ''aborted'',
            Enc {| LC ''aborted'',
                   Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                          s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                       |}
                       ( SK ( s(MV ''A'' tid0) ) )
                |}
                ( SK ( s(MV ''A'' tid0) ) )
         |}
         ( SK ( s(AV ''T'' tid0) ) ) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''aborted'',
                          Enc {| LC ''aborted'',
                                 Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                                        s(MV ''n'' tid0), LC ''text'', s(MV ''cA'' tid0)
                                     |}
                                     ( SK ( s(MV ''A'' tid0) ) )
                              |}
                              ( SK ( s(MV ''A'' tid0) ) )
                       |}
                       ( SK ( s(AV ''T'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (Ta_3abort_enc tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                                   LN ''n'' tid1, LC ''text'', s(MV ''cA'' tid0)
                                |}
                                ( SK ( s(MV ''A'' tid0) ) ),
                            Enc {| Enc {| s(MV ''A'' tid0), s(MV ''B'' tid0), s(AV ''T'' tid0),
                                          LN ''n'' tid1, LC ''text'', s(MV ''cA'' tid0)
                                       |}
                                       ( SK ( s(MV ''A'' tid0) ) ),
                                   s(MV ''cB'' tid0)
                                |}
                                ( SK ( s(MV ''B'' tid0) ) )
                         |}
                         ( SK ( s(AV ''T'' tid0) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (auto dest!: ltk_secrecy)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

end