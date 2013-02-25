theory "Lowe_modified_Denning_Sacco_shared_key_cert_auto"
imports
  "ESPLogic"
begin

(* section:  Denning-Sacco Shared Key Protocol  *)

(* text: 
  Modeled after the description in the SPORE library:

    http://www.lsv.ens-cachan.fr/Software/spore/denningSacco.html

  Notable differences:

    1. We do not support reasoning about timestamps yet. Therefore, we use a
       single global constant 'Time' instead of timestamps; i.e., we assume
       that everything happens at the same timepoint.

    2. We are using explicit global constants instead of implicit typing to
       discern the different encryptions.

    3. We model 'dec(x)' as an invertible function using tupling with a fixed
       global constant; i.e., we only exploit its tagging properties.

 *)

role A
where "A =
  [ Send ''1'' <| sAV ''A'', sAV ''B'' |>
  , Recv ''2'' <| sMV ''S'',
                  PEnc <| sC ''2'', sAV ''B'', sMV ''Kab'', sC ''Time'', sMV ''Ticket'' |>
                       ( PSymK ( sAV ''A'' ) ( sMV ''S'' ) )
               |>
  , Send ''3'' <| sMV ''S'', sMV ''Ticket'' |>
  , Recv ''4'' ( PEnc <| sC ''4'', sMV ''Nb'' |> ( sMV ''Kab'' ) )
  , Send ''5'' ( PEnc <| sC ''5'', sC ''dec'', sMV ''Nb'' |>
                      ( sMV ''Kab'' )
               )
  ]"

role B
where "B =
  [ Recv ''3'' <| sMV ''S'',
                  PEnc <| sC ''3'', sMV ''Kab'', sMV ''A'', sC ''Time'' |>
                       ( PSymK ( sAV ''B'' ) ( sMV ''S'' ) )
               |>
  , Send ''4'' ( PEnc <| sC ''4'', sN ''Nb'' |> ( sMV ''Kab'' ) )
  , Recv ''5'' ( PEnc <| sC ''5'', sC ''dec'', sN ''Nb'' |> ( sMV ''Kab'' )
               )
  ]"

role S
where "S =
  [ Recv ''1'' <| sMV ''A'', sMV ''B'' |>
  , Send ''2'' <| sAV ''S'',
                  PEnc <| sC ''2'', sMV ''B'', sN ''Kab'', sC ''Time'',
                          PEnc <| sC ''3'', sN ''Kab'', sMV ''A'', sC ''Time'' |>
                               ( PSymK ( sMV ''B'' ) ( sAV ''S'' ) )
                       |>
                       ( PSymK ( sMV ''A'' ) ( sAV ''S'' ) )
               |>
  ]"

protocol DenningSacco
where "DenningSacco = { A, B, S }"

locale restricted_DenningSacco_state = DenningSacco_state

type_invariant DenningSacco_msc_typing for DenningSacco
where "DenningSacco_msc_typing = mk_typing
  [ ((B, ''A''), (SumT (KnownT B_3) AgentT))
  , ((S, ''A''), (KnownT S_1))
  , ((S, ''B''), (KnownT S_1))
  , ((A, ''Kab''), (SumT (KnownT A_2) (NonceT S ''Kab'')))
  , ((B, ''Kab''), (SumT (KnownT B_3) (NonceT S ''Kab'')))
  , ((A, ''Nb''), (SumT (KnownT A_4) (NonceT B ''Nb'')))
  , ((A, ''S''), (KnownT A_2))
  , ((B, ''S''), (KnownT B_3))
  , ((A, ''Ticket''),
     (SumT (KnownT A_2) (EncT (TupT (ConstT ''3'') (TupT (NonceT S ''Kab'') (TupT AgentT (ConstT ''Time'')))) (KT AgentT AgentT))))
  ]"

sublocale DenningSacco_state < DenningSacco_msc_typing_state
proof -
  have "(t,r,s) : approx DenningSacco_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF DenningSacco_msc_typing.monoTyp, completeness_cases_rule])
    case (A_2_Kab t r s tid0) note facts = this
    then interpret state: DenningSacco_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''2'', s(AV ''B'' tid0), s(MV ''Kab'' tid0), LC ''Time'',
               s(MV ''Ticket'' tid0)
            |}
            ( K ( s(AV ''A'' tid0) ) ( s(MV ''S'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (A_2_S t r s tid0) note facts = this
    then interpret state: DenningSacco_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (A_2_Ticket t r s tid0) note facts = this
    then interpret state: DenningSacco_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''2'', s(AV ''B'' tid0), s(MV ''Kab'' tid0), LC ''Time'',
               s(MV ''Ticket'' tid0)
            |}
            ( K ( s(AV ''A'' tid0) ) ( s(MV ''S'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (A_4_Nb t r s tid0) note facts = this
    then interpret state: DenningSacco_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''4'', s(MV ''Nb'' tid0) |} ( s(MV ''Kab'' tid0) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (B_3_A t r s tid0) note facts = this
    then interpret state: DenningSacco_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''3'', s(MV ''Kab'' tid0), s(MV ''A'' tid0), LC ''Time'' |}
            ( K ( s(AV ''B'' tid0) ) ( s(MV ''S'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (B_3_Kab t r s tid0) note facts = this
    then interpret state: DenningSacco_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''3'', s(MV ''Kab'' tid0), s(MV ''A'' tid0), LC ''Time'' |}
            ( K ( s(AV ''B'' tid0) ) ( s(MV ''S'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (B_3_S t r s tid0) note facts = this
    then interpret state: DenningSacco_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (S_1_A t r s tid0) note facts = this
    then interpret state: DenningSacco_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (S_1_B t r s tid0) note facts = this
    then interpret state: DenningSacco_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "DenningSacco_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context DenningSacco_state begin

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

lemma (in restricted_DenningSacco_state) B_Kab_secrecy:
  assumes facts:
    "roleMap r tid0 = Some B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''S'' tid0)) ~: reveals t"
    "( tid0, B_3 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''3'', s(MV ''Kab'' tid0), s(MV ''A'' tid0), LC ''Time'' |}
                       ( K ( s(AV ''B'' tid0) ) ( s(MV ''S'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (A_3_Ticket_enc tid1 tid2 a0 a1 a2) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''2'', s(AV ''B'' tid1), s(MV ''Kab'' tid1), LC ''Time'',
                            Enc {| LC ''3'', LN ''Kab'' tid2, a0, LC ''Time'' |}
                                ( K ( s(AV ''B'' tid0) ) ( a2 ) )
                         |}
                         ( K ( s(AV ''A'' tid1) ) ( s(MV ''S'' tid1) ) ) ")
      case (S_2_enc tid3) note_unified facts = this facts
      thus ?thesis proof(sources! " LN ''Kab'' tid2 ")
        case (A_3_Ticket_Kab tid3 a0 a1 a2) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''2'', s(AV ''B'' tid3), s(MV ''Kab'' tid3), LC ''Time'',
                                Enc {| LC ''3'', LN ''Kab'' tid2, a0, LC ''Time'' |} ( K ( a1 ) ( a2 ) )
                             |}
                             ( K ( s(AV ''A'' tid3) ) ( s(MV ''S'' tid3) ) ) ")
          case (S_2_enc tid4) note_unified facts = this facts
          thus ?thesis by (fastforce dest!: ltk_secrecy)
        qed (insert facts, (((clarsimp, order?) | order))+)?
      next
        case S_2_Kab note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      next
        case S_2_Kab_1 note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      qed (insert facts, fastforce+)?
    qed (insert facts, (((clarsimp, order?) | order))+)?
  next
    case (S_2_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_DenningSacco_state) A_Kab_secrecy:
  assumes facts:
    "roleMap r tid0 = Some A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''S'' tid0)) ~: reveals t"
    "( tid0, A_2 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''2'', s(AV ''B'' tid0), s(MV ''Kab'' tid0), LC ''Time'',
                          s(MV ''Ticket'' tid0)
                       |}
                       ( K ( s(AV ''A'' tid0) ) ( s(MV ''S'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (S_2_enc tid1) note_unified facts = this facts
    thus ?thesis proof(sources! " LN ''Kab'' tid1 ")
      case (A_3_Ticket_Kab tid2 a0 a1 a2) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''2'', s(AV ''B'' tid2), s(MV ''Kab'' tid2), LC ''Time'',
                              Enc {| LC ''3'', LN ''Kab'' tid1, a0, LC ''Time'' |} ( K ( a1 ) ( a2 ) )
                           |}
                           ( K ( s(AV ''A'' tid2) ) ( s(MV ''S'' tid2) ) ) ")
        case (S_2_enc tid3) note_unified facts = this facts
        thus ?thesis by (fastforce dest!: ltk_secrecy)
      qed (insert facts, (((clarsimp, order?) | order))+)?
    next
      case S_2_Kab note_unified facts = this facts
      thus ?thesis by (fastforce dest!: ltk_secrecy)
    next
      case S_2_Kab_1 note_unified facts = this facts
      thus ?thesis by (fastforce dest!: ltk_secrecy)
    qed (insert facts, fastforce+)?
  qed (insert facts, fastforce+)?
qed

(* text: 
  Note that the following authentication properties only specify the existence
  of partner threads of a certain structure and not the uniqueness. However,
  these partner threads agree on the nonces of each other, which implies that
  we can prove injective authentication. We can do this using Isabelle/HOL
  and exploiting the automatically proven properties below.
 *)

lemma (in restricted_DenningSacco_state) A_noninjective_agree:
  assumes facts:
    "roleMap r tid1 = Some A"
    "RLKR(s(AV ''A'' tid1)) ~: reveals t"
    "RLKR(s(AV ''B'' tid1)) ~: reveals t"
    "RLKR(s(MV ''S'' tid1)) ~: reveals t"
    "( tid1, A_4 ) : steps t"
  shows
    "(?  tid2.
        (?  tid3.
           roleMap r tid2 = Some B &
           roleMap r tid3 = Some S &
           s(AV ''A'' tid1) = s(MV ''A'' tid2) &
           s(MV ''A'' tid2) = s(MV ''A'' tid3) &
           s(AV ''B'' tid1) = s(AV ''B'' tid2) &
           s(AV ''B'' tid2) = s(MV ''B'' tid3) &
           s(MV ''S'' tid1) = s(MV ''S'' tid2) &
           s(MV ''S'' tid2) = s(AV ''S'' tid3) &
           s(MV ''Kab'' tid1) = s(MV ''Kab'' tid2) &
           s(MV ''Kab'' tid2) = LN ''Kab'' tid3 &
           s(MV ''Nb'' tid1) = LN ''Nb'' tid2))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''2'', s(AV ''B'' tid1), s(MV ''Kab'' tid1), LC ''Time'',
                          s(MV ''Ticket'' tid1)
                       |}
                       ( K ( s(AV ''A'' tid1) ) ( s(MV ''S'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (S_2_enc tid2) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''4'', s(MV ''Nb'' tid1) |} ( LN ''Kab'' tid2 ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastforce dest: A_Kab_secrecy intro: event_predOrdI)
    next
      case (B_4_enc tid3) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''3'', LN ''Kab'' tid2, s(MV ''A'' tid3), LC ''Time'' |}
                           ( K ( s(AV ''B'' tid3) ) ( s(MV ''S'' tid3) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest: A_Kab_secrecy intro: event_predOrdI)
      next
        case (A_3_Ticket_enc tid4 tid5 a0 a1 a2) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''2'', s(AV ''B'' tid4), s(MV ''Kab'' tid4), LC ''Time'',
                                Enc {| LC ''3'', LN ''Kab'' tid2, a0, LC ''Time'' |}
                                    ( K ( s(AV ''B'' tid3) ) ( a2 ) )
                             |}
                             ( K ( s(AV ''A'' tid4) ) ( s(MV ''S'' tid4) ) ) ")
          case (S_2_enc tid5) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (insert facts, (((clarsimp, order?) | order))+)?
      next
        case (S_2_enc_1 tid4) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (insert facts, fastforce+)?
    qed (insert facts, fastforce+)?
  qed (insert facts, fastforce+)?
qed

lemma (in restricted_DenningSacco_state) B_noninjective_agree:
  assumes facts:
    "roleMap r tid2 = Some B"
    "RLKR(s(AV ''B'' tid2)) ~: reveals t"
    "RLKR(s(MV ''A'' tid2)) ~: reveals t"
    "RLKR(s(MV ''S'' tid2)) ~: reveals t"
    "( tid2, B_5 ) : steps t"
  shows
    "(?  tid1.
        (?  tid3.
           roleMap r tid1 = Some A &
           roleMap r tid3 = Some S &
           s(AV ''A'' tid1) = s(MV ''A'' tid2) &
           s(MV ''A'' tid2) = s(MV ''A'' tid3) &
           s(AV ''B'' tid1) = s(AV ''B'' tid2) &
           s(AV ''B'' tid2) = s(MV ''B'' tid3) &
           s(MV ''S'' tid1) = s(MV ''S'' tid2) &
           s(MV ''S'' tid2) = s(AV ''S'' tid3) &
           s(MV ''Kab'' tid1) = s(MV ''Kab'' tid2) &
           s(MV ''Kab'' tid2) = LN ''Kab'' tid3 &
           s(MV ''Nb'' tid1) = LN ''Nb'' tid2))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''3'', s(MV ''Kab'' tid2), s(MV ''A'' tid2), LC ''Time'' |}
                       ( K ( s(AV ''B'' tid2) ) ( s(MV ''S'' tid2) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  next
    case (A_3_Ticket_enc tid3 tid4 a0 a1 a2) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''2'', s(AV ''B'' tid3), s(MV ''Kab'' tid3), LC ''Time'',
                            Enc {| LC ''3'', LN ''Kab'' tid4, a0, LC ''Time'' |}
                                ( K ( s(AV ''B'' tid2) ) ( a2 ) )
                         |}
                         ( K ( s(AV ''A'' tid3) ) ( s(MV ''S'' tid3) ) ) ")
      case (S_2_enc tid5) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''5'', LC ''dec'', LN ''Nb'' tid2 |} ( LN ''Kab'' tid4 ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest: B_Kab_secrecy intro: event_predOrdI)
      next
        case (A_5_enc tid5) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''2'', s(AV ''B'' tid5), LN ''Kab'' tid4, LC ''Time'',
                                s(MV ''Ticket'' tid5)
                             |}
                             ( K ( s(AV ''A'' tid5) ) ( s(MV ''S'' tid5) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest: B_Kab_secrecy intro: event_predOrdI)
        next
          case (S_2_enc tid6) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (insert facts, fastforce+)?
      qed (insert facts, fastforce+)?
    qed (insert facts, (((clarsimp, order?) | order))+)?
  next
    case (S_2_enc_1 tid3) note_unified facts = this facts
    thus ?thesis by (fastforce dest!: ltk_secrecy)
  qed (insert facts, fastforce+)?
qed

end