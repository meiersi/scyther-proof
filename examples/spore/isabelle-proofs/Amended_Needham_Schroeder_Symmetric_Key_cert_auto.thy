theory "Amended_Needham_Schroeder_Symmetric_Key_cert_auto"
imports
  "ESPLogic"
begin

(* section:  The Amended Needham Schroeder Symmetric Key Protocol  *)

(* text: 
  Modelled according to the desciprtion in the SPORE library:

    http://www.lsv.ens-cachan.fr/Software/spore/nssk_amended.html

  Notable differences:

    1. Instead of assuming a typed model we are using global constants to
       ensure distinctness of messages from different steps.

    2. We use the weaker authentication property of non-injective agreement
       instead of injective agreement because the later cannot yet be proven
       automatically. However, based on the resulting Isabelle file it would be
       easy to also derive injective agreement from the proven non-injective
       variants.

    3. We model the invertible function 'dec(x)' as tupling with a fixed public
       constant 'dec'; i.e., we only exploit 'dec's tagging capabilities.

    TODO: Check that this protocol can also be verified with bidirectional
    shared keys.
 *)

role I
where "I =
  [ Send ''1'' ( sAV ''I'' )
  , Recv ''2'' ( sMV ''RequestR'' )
  , Send ''3'' <| sAV ''I'', sAV ''R'', sN ''ni'', sMV ''RequestR'' |>
  , Recv ''4'' <| sMV ''S'',
                  PEnc <| sC ''2'', sN ''ni'', sAV ''R'', sMV ''kIR'', sMV ''TicketR'' |>
                       ( PSymK ( sAV ''I'' ) ( sMV ''S'' ) )
               |>
  , Send ''5'' ( sMV ''TicketR'' )
  , Recv ''6'' ( PEnc <| sC ''4'', sMV ''nr'' |> ( sMV ''kIR'' ) )
  , Send ''7'' ( PEnc <| sC ''5'', sC ''dec'', sMV ''nr'' |>
                      ( sMV ''kIR'' )
               )
  ]"

role R
where "R =
  [ Recv ''1'' ( sMV ''I'' )
  , Send ''2'' ( PEnc <| sC ''1'', sMV ''I'', sN ''nr'' |>
                      ( sK ''R'' ''S'' )
               )
  , Recv ''5'' ( PEnc <| sC ''3'', sMV ''kIR'', sN ''nr'', sMV ''I'' |>
                      ( sK ''R'' ''S'' )
               )
  , Send ''6'' ( PEnc <| sC ''4'', sN ''nr'' |> ( sMV ''kIR'' ) )
  , Recv ''7'' ( PEnc <| sC ''5'', sC ''dec'', sN ''nr'' |> ( sMV ''kIR'' )
               )
  ]"

role S
where "S =
  [ Recv ''3'' <| sMV ''I'', sMV ''R'', sMV ''ni'',
                  PEnc <| sC ''1'', sMV ''I'', sMV ''nr'' |>
                       ( PSymK ( sMV ''R'' ) ( sAV ''S'' ) )
               |>
  , Send ''4'' <| sAV ''S'',
                  PEnc <| sC ''2'', sMV ''ni'', sMV ''R'', sN ''kIR'',
                          PEnc <| sC ''3'', sN ''kIR'', sMV ''nr'', sMV ''I'' |>
                               ( PSymK ( sMV ''R'' ) ( sAV ''S'' ) )
                       |>
                       ( PSymK ( sMV ''I'' ) ( sAV ''S'' ) )
               |>
  ]"

protocol AmendedNS
where "AmendedNS = { I, R, S }"

locale restricted_AmendedNS_state = AmendedNS_state

(* subsection:  Security Properties  *)

type_invariant AmendedNS_msc_typing for AmendedNS
where "AmendedNS_msc_typing = mk_typing
  [ ((R, ''I''), (KnownT R_1))
  , ((S, ''I''), (KnownT S_3))
  , ((S, ''R''), (KnownT S_3))
  , ((I, ''RequestR''), (KnownT I_2))
  , ((I, ''S''), (KnownT I_4))
  , ((I, ''TicketR''),
     (SumT (KnownT I_4) (EncT (TupT (ConstT ''3'') (TupT (NonceT S ''kIR'') (TupT (SumT (KnownT I_4) (NonceT R ''nr'')) AgentT))) (KT AgentT AgentT))))
  , ((I, ''kIR''), (SumT (KnownT I_4) (NonceT S ''kIR'')))
  , ((R, ''kIR''), (SumT (KnownT R_5) (NonceT S ''kIR'')))
  , ((S, ''ni''), (KnownT S_3))
  , ((I, ''nr''), (SumT (KnownT I_6) (NonceT R ''nr'')))
  , ((S, ''nr''), (SumT (KnownT S_3) (NonceT R ''nr'')))
  ]"

sublocale AmendedNS_state < AmendedNS_msc_typing_state
proof -
  have "(t,r,s) : approx AmendedNS_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF AmendedNS_msc_typing.monoTyp, completeness_cases_rule])
    case (I_4_S t r s tid0)
    then interpret state: AmendedNS_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = I_4_S
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (I_4_TicketR t r s tid0)
    then interpret state: AmendedNS_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = I_4_TicketR
    thus ?case
    proof(sources! "
        Enc {| LC ''2'', LN ''ni'' tid0, s(AV ''R'' tid0), s(MV ''kIR'' tid0),
               s(MV ''TicketR'' tid0)
            |}
            ( K ( s(AV ''I'' tid0) ) ( s(MV ''S'' tid0) ) ) ")
      case (S_4_enc tid1) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''1'', s(AV ''I'' tid0), s(MV ''nr'' tid1) |}
                           ( K ( s(AV ''R'' tid0) ) ( s(AV ''S'' tid1) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (I_4_kIR t r s tid0)
    then interpret state: AmendedNS_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = I_4_kIR
    thus ?case
    proof(sources! "
        Enc {| LC ''2'', LN ''ni'' tid0, s(AV ''R'' tid0), s(MV ''kIR'' tid0),
               s(MV ''TicketR'' tid0)
            |}
            ( K ( s(AV ''I'' tid0) ) ( s(MV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (I_6_nr t r s tid0)
    then interpret state: AmendedNS_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = I_6_nr
    thus ?case
    proof(sources! "
        Enc {| LC ''4'', s(MV ''nr'' tid0) |} ( s(MV ''kIR'' tid0) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (R_5_kIR t r s tid0)
    then interpret state: AmendedNS_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = R_5_kIR
    thus ?case
    proof(sources! "
        Enc {| LC ''3'', s(MV ''kIR'' tid0), LN ''nr'' tid0, s(MV ''I'' tid0) |}
            ( K ( s(AV ''R'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (S_3_I t r s tid0)
    then interpret state: AmendedNS_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_3_I
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (S_3_R t r s tid0)
    then interpret state: AmendedNS_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_3_R
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (S_3_ni t r s tid0)
    then interpret state: AmendedNS_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_3_ni
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (S_3_nr t r s tid0)
    then interpret state: AmendedNS_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_3_nr
    thus ?case
    proof(sources! "
        Enc {| LC ''1'', s(MV ''I'' tid0), s(MV ''nr'' tid0) |}
            ( K ( s(MV ''R'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  qed
  thus "AmendedNS_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context AmendedNS_state begin

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

lemma (in restricted_AmendedNS_state) S_kir_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''I'' tid0)) ~: reveals t"
    "RLKR(s(MV ''R'' tid0)) ~: reveals t"
    "LN ''kIR'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''kIR'' tid0 ")
  case (I_5_TicketR_kIR tid1 a0 a1 a2 a3) note_unified facts = this facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''2'', LN ''ni'' tid1, s(AV ''R'' tid1), s(MV ''kIR'' tid1),
                          Enc {| LC ''3'', LN ''kIR'' tid0, a0, a1 |} ( K ( a2 ) ( a3 ) )
                       |}
                       ( K ( s(AV ''I'' tid1) ) ( s(MV ''S'' tid1) ) ) ")
    case (S_4_enc tid2) note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  qed (safe?, simp_all?, insert facts, ((((clarsimp, order?) | order | fast))+)?)
next
  case S_4_kIR note_unified facts = this facts
  thus ?thesis by (auto dest!: ltk_secrecy)
next
  case S_4_kIR_1 note_unified facts = this facts
  thus ?thesis by (auto dest!: ltk_secrecy)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

lemma (in restricted_AmendedNS_state) I_kir_sec:
  assumes facts:
    "roleMap r tid0 = Some I"
    "RLKR(s(AV ''I'' tid0)) ~: reveals t"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "RLKR(s(MV ''S'' tid0)) ~: reveals t"
    "( tid0, I_4 ) : steps t"
    "s(MV ''kIR'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''2'', LN ''ni'' tid0, s(AV ''R'' tid0), s(MV ''kIR'' tid0),
                          s(MV ''TicketR'' tid0)
                       |}
                       ( K ( s(AV ''I'' tid0) ) ( s(MV ''S'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (S_4_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: S_kir_sec intro: event_predOrdI)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_AmendedNS_state) R_kir_sec:
  assumes facts:
    "roleMap r tid0 = Some R"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''I'' tid0)) ~: reveals t"
    "( tid0, R_5 ) : steps t"
    "s(MV ''kIR'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''3'', s(MV ''kIR'' tid0), LN ''nr'' tid0, s(MV ''I'' tid0) |}
                       ( K ( s(AV ''R'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (I_5_TicketR_enc tid1 tid2 a0 a1 a2 a3) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''2'', LN ''ni'' tid1, s(AV ''R'' tid1), s(MV ''kIR'' tid1),
                            Enc {| LC ''3'', LN ''kIR'' tid2, LN ''nr'' tid0, a1 |}
                                ( K ( s(AV ''R'' tid0) ) ( s(AV ''S'' tid0) ) )
                         |}
                         ( K ( s(AV ''I'' tid1) ) ( s(MV ''S'' tid1) ) ) ")
      case (S_4_enc tid3) note_unified facts = this facts
      thus ?thesis by (fastforce dest: S_kir_sec intro: event_predOrdI)
    qed (safe?, simp_all?, insert facts, ((((clarsimp, order?) | order | fast))+)?)
  next
    case (S_4_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_AmendedNS_state) I_ni_agree:
  assumes facts:
    "roleMap r tid1 = Some I"
    "RLKR(s(AV ''I'' tid1)) ~: reveals t"
    "RLKR(s(AV ''R'' tid1)) ~: reveals t"
    "RLKR(s(MV ''S'' tid1)) ~: reveals t"
    "( tid1, I_6 ) : steps t"
  shows
    "(?  tid2.
        (?  tid3.
           roleMap r tid2 = Some R &
           roleMap r tid3 = Some S &
           s(AV ''I'' tid1) = s(MV ''I'' tid2) &
           s(MV ''I'' tid2) = s(MV ''I'' tid3) &
           s(AV ''R'' tid1) = s(AV ''R'' tid2) &
           s(AV ''R'' tid2) = s(MV ''R'' tid3) &
           s(MV ''S'' tid1) = s(AV ''S'' tid2) &
           s(AV ''S'' tid2) = s(AV ''S'' tid3) &
           LN ''ni'' tid1 = s(MV ''ni'' tid3) &
           s(MV ''nr'' tid1) = LN ''nr'' tid2 &
           LN ''nr'' tid2 = s(MV ''nr'' tid3) &
           s(MV ''kIR'' tid1) = s(MV ''kIR'' tid2) &
           s(MV ''kIR'' tid2) = LN ''kIR'' tid3))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''2'', LN ''ni'' tid1, s(AV ''R'' tid1), s(MV ''kIR'' tid1),
                          s(MV ''TicketR'' tid1)
                       |}
                       ( K ( s(AV ''I'' tid1) ) ( s(MV ''S'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (S_4_enc tid2) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''4'', s(MV ''nr'' tid1) |} ( LN ''kIR'' tid2 ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastforce dest: S_kir_sec intro: event_predOrdI)
    next
      case (R_6_enc tid3) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''3'', LN ''kIR'' tid2, LN ''nr'' tid3, s(MV ''I'' tid3) |}
                           ( K ( s(AV ''R'' tid3) ) ( s(AV ''S'' tid3) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest: S_kir_sec intro: event_predOrdI)
      next
        case (I_5_TicketR_enc tid4 tid5 a0 a1 a2 a3) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''2'', LN ''ni'' tid4, s(AV ''R'' tid4), s(MV ''kIR'' tid4),
                                Enc {| LC ''3'', LN ''kIR'' tid2, LN ''nr'' tid3, a1 |}
                                    ( K ( s(AV ''R'' tid3) ) ( s(AV ''S'' tid3) ) )
                             |}
                             ( K ( s(AV ''I'' tid4) ) ( s(MV ''S'' tid4) ) ) ")
          case (S_4_enc tid5) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (safe?, simp_all?, insert facts, ((((clarsimp, order?) | order | fast))+)?)
      next
        case (S_4_enc_1 tid4) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_AmendedNS_state) R_ni_agree:
  assumes facts:
    "roleMap r tid2 = Some R"
    "RLKR(s(AV ''R'' tid2)) ~: reveals t"
    "RLKR(s(AV ''S'' tid2)) ~: reveals t"
    "RLKR(s(MV ''I'' tid2)) ~: reveals t"
    "( tid2, R_7 ) : steps t"
  shows
    "(?  tid1.
        (?  tid3.
           roleMap r tid1 = Some I &
           roleMap r tid3 = Some S &
           s(AV ''I'' tid1) = s(MV ''I'' tid2) &
           s(MV ''I'' tid2) = s(MV ''I'' tid3) &
           s(AV ''R'' tid1) = s(AV ''R'' tid2) &
           s(AV ''R'' tid2) = s(MV ''R'' tid3) &
           s(MV ''S'' tid1) = s(AV ''S'' tid2) &
           s(AV ''S'' tid2) = s(AV ''S'' tid3) &
           LN ''ni'' tid1 = s(MV ''ni'' tid3) &
           s(MV ''nr'' tid1) = LN ''nr'' tid2 &
           LN ''nr'' tid2 = s(MV ''nr'' tid3) &
           s(MV ''kIR'' tid1) = s(MV ''kIR'' tid2) &
           s(MV ''kIR'' tid2) = LN ''kIR'' tid3))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''3'', s(MV ''kIR'' tid2), LN ''nr'' tid2, s(MV ''I'' tid2) |}
                       ( K ( s(AV ''R'' tid2) ) ( s(AV ''S'' tid2) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (I_5_TicketR_enc tid3 tid4 a0 a1 a2 a3) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''2'', LN ''ni'' tid3, s(AV ''R'' tid3), s(MV ''kIR'' tid3),
                            Enc {| LC ''3'', LN ''kIR'' tid4, LN ''nr'' tid2, a1 |}
                                ( K ( s(AV ''R'' tid2) ) ( s(AV ''S'' tid2) ) )
                         |}
                         ( K ( s(AV ''I'' tid3) ) ( s(MV ''S'' tid3) ) ) ")
      case (S_4_enc tid5) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''5'', LC ''dec'', LN ''nr'' tid2 |} ( LN ''kIR'' tid4 ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest: S_kir_sec intro: event_predOrdI)
      next
        case (I_7_enc tid5) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''2'', LN ''ni'' tid5, s(AV ''R'' tid5), LN ''kIR'' tid4,
                                s(MV ''TicketR'' tid5)
                             |}
                             ( K ( s(AV ''I'' tid5) ) ( s(MV ''S'' tid5) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest: S_kir_sec intro: event_predOrdI)
        next
          case (S_4_enc tid6) note_unified facts = this facts
          thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
    qed (safe?, simp_all?, insert facts, ((((clarsimp, order?) | order | fast))+)?)
  next
    case (S_4_enc_1 tid3) note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

end