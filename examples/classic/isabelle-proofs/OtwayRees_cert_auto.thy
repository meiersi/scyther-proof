theory "OtwayRees_cert_auto"
imports
  "ESPLogic"
begin

(* section:  The Original Otway-Rees Protocol  *)

(* text: 
  Based on Paulson's model in Isabelle/src/HOL/Auth/OtwayRees.thy. Notable
  differences:

    1. Instead of implicit typing, we are using explicit global constants to
       differentiate between different encryptions.

    2. We do not model session key compromise, as our key compromise
       infrastructure is not ready yet.
 *)

role I
where "I =
  [ Send ''1'' <| sN ''ni'', sAV ''I'', sAV ''R'',
                  PEnc <| sC ''TT1'', sN ''ni'', sAV ''I'', sAV ''R'' |> ( sK ''I'' ''S'' )
               |>
  , Recv ''4'' <| sN ''ni'',
                  PEnc <| sC ''TT3'', sN ''ni'', sMV ''kIR'' |> ( sK ''I'' ''S'' )
               |>
  ]"

role R
where "R =
  [ Recv ''1'' <| sMV ''ni'', sMV ''I'', sAV ''R'', sMV ''Ticket1'' |>
  , Send ''2'' <| sMV ''ni'', sMV ''I'', sAV ''R'', sMV ''Ticket1'',
                  PEnc <| sC ''TT2'', sMV ''ni'', sN ''nr'', sMV ''I'', sAV ''R'' |>
                       ( sK ''R'' ''S'' )
               |>
  , Recv ''3'' <| sMV ''ni'', sMV ''Ticket2'',
                  PEnc <| sC ''TT3'', sN ''nr'', sMV ''kIR'' |> ( sK ''R'' ''S'' )
               |>
  , Send ''4'' <| sMV ''ni'', sMV ''Ticket2'' |>
  ]"

role S
where "S =
  [ Recv ''2'' <| sMV ''ni'', sMV ''I'', sMV ''R'',
                  PEnc <| sC ''TT1'', sMV ''ni'', sMV ''I'', sMV ''R'' |>
                       ( PSymK ( sMV ''I'' ) ( sAV ''S'' ) ),
                  PEnc <| sC ''TT2'', sMV ''ni'', sMV ''nr'', sMV ''I'', sMV ''R'' |>
                       ( PSymK ( sMV ''R'' ) ( sAV ''S'' ) )
               |>
  , Send ''3'' <| sMV ''ni'',
                  PEnc <| sC ''TT3'', sMV ''ni'', sN ''kIR'' |>
                       ( PSymK ( sMV ''I'' ) ( sAV ''S'' ) ),
                  PEnc <| sC ''TT3'', sMV ''nr'', sN ''kIR'' |>
                       ( PSymK ( sMV ''R'' ) ( sAV ''S'' ) )
               |>
  ]"

protocol OtwayRees
where "OtwayRees = { I, R, S }"

locale restricted_OtwayRees_state = OtwayRees_state

type_invariant OtwayRees_msc_typing for OtwayRees
where "OtwayRees_msc_typing = mk_typing
  [ ((R, ''I''), (KnownT R_1))
  , ((S, ''I''), (KnownT S_2))
  , ((S, ''R''), (KnownT S_2))
  , ((R, ''Ticket1''), (KnownT R_1))
  , ((R, ''Ticket2''), (KnownT R_3))
  , ((I, ''kIR''), (SumT (KnownT I_4) (NonceT S ''kIR'')))
  , ((R, ''kIR''), (SumT (KnownT R_3) (NonceT S ''kIR'')))
  , ((R, ''ni''), (KnownT R_1))
  , ((S, ''ni''), (KnownT S_2))
  , ((S, ''nr''), (SumT (KnownT S_2) (NonceT R ''nr'')))
  ]"

sublocale OtwayRees_state < OtwayRees_msc_typing_state
proof -
  have "(t,r,s) : approx OtwayRees_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF OtwayRees_msc_typing.monoTyp, completeness_cases_rule])
    case (I_4_kIR t r s tid0)
    then interpret state: OtwayRees_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = I_4_kIR
    thus ?case
    proof(sources! "
        Enc {| LC ''TT3'', LN ''ni'' tid0, s(MV ''kIR'' tid0) |}
            ( K ( s(AV ''I'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (R_1_I t r s tid0)
    then interpret state: OtwayRees_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = R_1_I
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (R_1_Ticket1 t r s tid0)
    then interpret state: OtwayRees_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = R_1_Ticket1
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (R_1_ni t r s tid0)
    then interpret state: OtwayRees_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = R_1_ni
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (R_3_Ticket2 t r s tid0)
    then interpret state: OtwayRees_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = R_3_Ticket2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (R_3_kIR t r s tid0)
    then interpret state: OtwayRees_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = R_3_kIR
    thus ?case
    proof(sources! "
        Enc {| LC ''TT3'', LN ''nr'' tid0, s(MV ''kIR'' tid0) |}
            ( K ( s(AV ''R'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (S_2_I t r s tid0)
    then interpret state: OtwayRees_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_2_I
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (S_2_R t r s tid0)
    then interpret state: OtwayRees_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_2_R
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (S_2_ni t r s tid0)
    then interpret state: OtwayRees_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_2_ni
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (S_2_nr t r s tid0)
    then interpret state: OtwayRees_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_2_nr
    thus ?case
    proof(sources! "
        Enc {| LC ''TT2'', s(MV ''ni'' tid0), s(MV ''nr'' tid0),
               s(MV ''I'' tid0), s(MV ''R'' tid0)
            |}
            ( K ( s(MV ''R'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  qed
  thus "OtwayRees_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context OtwayRees_state begin

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

(* subsection:  Secrecy Properties  *)

lemma (in restricted_OtwayRees_state) S_kIR_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''I'' tid0)) ~: reveals t"
    "RLKR(s(MV ''R'' tid0)) ~: reveals t"
    "LN ''kIR'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''kIR'' tid0 ")
  case S_3_kIR note_unified facts = this facts
  thus ?thesis by (auto dest!: ltk_secrecy)
next
  case S_3_kIR_1 note_unified facts = this facts
  thus ?thesis by (auto dest!: ltk_secrecy)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

lemma (in restricted_OtwayRees_state) R_kIR_sec:
  assumes facts:
    "roleMap r tid0 = Some R"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''I'' tid0)) ~: reveals t"
    "( tid0, R_3 ) : steps t"
    "s(MV ''kIR'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT3'', LN ''nr'' tid0, s(MV ''kIR'' tid0) |}
                       ( K ( s(AV ''R'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (S_3_enc tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', LN ''nr'' tid0, s(AV ''R'' tid0), s(MV ''R'' tid1) |}
                         ( K ( s(AV ''R'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (auto dest!: ltk_secrecy)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  next
    case (S_3_enc_1 tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', s(MV ''ni'' tid1), LN ''nr'' tid0, s(MV ''I'' tid1),
                            s(AV ''R'' tid0)
                         |}
                         ( K ( s(AV ''R'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (auto dest!: ltk_secrecy)
    next
      case (R_2_enc tid2) note_unified facts = this facts
      thus ?thesis by (fastforce dest: S_kIR_sec intro: event_predOrdI)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_OtwayRees_state) I_kIR_sec:
  assumes facts:
    "roleMap r tid0 = Some I"
    "RLKR(s(AV ''I'' tid0)) ~: reveals t"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "( tid0, I_4 ) : steps t"
    "s(MV ''kIR'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT3'', LN ''ni'' tid0, s(MV ''kIR'' tid0) |}
                       ( K ( s(AV ''I'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (S_3_enc tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', LN ''ni'' tid0, s(AV ''I'' tid0), s(MV ''R'' tid1) |}
                         ( K ( s(AV ''I'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (auto dest!: ltk_secrecy)
    next
      case (I_1_enc tid2) note_unified facts = this facts
      thus ?thesis by (fastforce dest: S_kIR_sec intro: event_predOrdI)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  next
    case (S_3_enc_1 tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', s(MV ''ni'' tid1), LN ''ni'' tid0, s(MV ''I'' tid1),
                            s(AV ''I'' tid0)
                         |}
                         ( K ( s(AV ''I'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (auto dest!: ltk_secrecy)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

(* subsection:  Authentication Properties  *)

lemma (in restricted_OtwayRees_state) ni_first_send:
  assumes facts:
    "roleMap r tid1 = Some I"
    "LN ''ni'' tid1 : knows t"
  shows "predOrd t (St( tid1, I_1 )) (Ln(LN ''ni'' tid1))"
using facts proof(sources! " LN ''ni'' tid1 ")
  case I_1_ni note_unified facts = this facts
  thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
next
  case I_1_ni_1 note_unified facts = this facts
  thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

(* text: 
  Note that the guarantees would be way better, if we the initiator would
  receive an unfakeable message from the responder after he received the
  session key. Currently, we just don't have a means to check that the
  responder received the servers message. Hence, we cannot prove agreement on
  'kIR'.
 *)

lemma (in restricted_OtwayRees_state) I_auth:
  assumes facts:
    "roleMap r tid1 = Some I"
    "RLKR(s(AV ''I'' tid1)) ~: reveals t"
    "RLKR(s(AV ''R'' tid1)) ~: reveals t"
    "RLKR(s(AV ''S'' tid1)) ~: reveals t"
    "( tid1, I_4 ) : steps t"
  shows
    "(?  tid2.
        (?  tid3.
           roleMap r tid2 = Some R &
           roleMap r tid3 = Some S &
           s(AV ''I'' tid1) = s(MV ''I'' tid3) &
           s(AV ''R'' tid1) = s(MV ''R'' tid3) &
           s(AV ''S'' tid1) = s(AV ''S'' tid3) &
           LN ''ni'' tid1 = s(MV ''ni'' tid3) &
           s(MV ''kIR'' tid1) = LN ''kIR'' tid3 &
           s(AV ''I'' tid1) = s(MV ''I'' tid2) &
           s(AV ''R'' tid1) = s(AV ''R'' tid2) &
           s(AV ''S'' tid1) = s(AV ''S'' tid2) &
           LN ''ni'' tid1 = s(MV ''ni'' tid2) &
           LN ''nr'' tid2 = s(MV ''nr'' tid3) &
           predOrd t (St( tid1, I_1 )) (St( tid2, R_1 )) &
           predOrd t (St( tid2, R_1 )) (St( tid2, R_2 )) &
           predOrd t (St( tid2, R_2 )) (St( tid3, S_2 )) &
           predOrd t (St( tid3, S_2 )) (St( tid3, S_3 )) &
           predOrd t (St( tid3, S_3 )) (St( tid1, I_4 ))))"
proof -
  note_prefix_closed facts = facts
  have f1: "roleMap r tid1 = Some I" using facts by (auto intro: event_predOrdI)
  have f2: "LN ''ni'' tid1 : knows t" using facts by (auto intro: event_predOrdI)
  note facts = facts ni_first_send[OF f1 f2, simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT3'', LN ''ni'' tid1, s(MV ''kIR'' tid1) |}
                       ( K ( s(AV ''I'' tid1) ) ( s(AV ''S'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (S_3_enc tid2) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', LN ''ni'' tid1, s(AV ''I'' tid1), s(MV ''R'' tid2) |}
                         ( K ( s(AV ''I'' tid1) ) ( s(AV ''S'' tid1) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (auto dest!: ltk_secrecy)
    next
      case (I_1_enc tid3) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT2'', LN ''ni'' tid1, s(MV ''nr'' tid2), s(AV ''I'' tid1),
                              s(AV ''R'' tid1)
                           |}
                           ( K ( s(AV ''R'' tid1) ) ( s(AV ''S'' tid1) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (R_2_enc tid3) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  next
    case (S_3_enc_1 tid2) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', s(MV ''ni'' tid2), LN ''ni'' tid1, s(MV ''I'' tid2),
                            s(AV ''I'' tid1)
                         |}
                         ( K ( s(AV ''I'' tid1) ) ( s(AV ''S'' tid1) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (auto dest!: ltk_secrecy)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_OtwayRees_state) R_ni_agree:
  assumes facts:
    "roleMap r tid2 = Some R"
    "RLKR(s(AV ''R'' tid2)) ~: reveals t"
    "RLKR(s(AV ''S'' tid2)) ~: reveals t"
    "RLKR(s(MV ''I'' tid2)) ~: reveals t"
    "( tid2, R_3 ) : steps t"
  shows
    "(?  tid1.
        (?  tid3.
           roleMap r tid1 = Some I &
           roleMap r tid3 = Some S &
           s(MV ''I'' tid2) = s(AV ''I'' tid1) &
           s(AV ''R'' tid2) = s(AV ''R'' tid1) &
           s(AV ''S'' tid2) = s(AV ''S'' tid1) &
           s(MV ''ni'' tid2) = LN ''ni'' tid1 &
           s(MV ''I'' tid2) = s(MV ''I'' tid3) &
           s(AV ''R'' tid2) = s(MV ''R'' tid3) &
           s(AV ''S'' tid2) = s(AV ''S'' tid3) &
           s(MV ''ni'' tid2) = s(MV ''ni'' tid3) &
           LN ''nr'' tid2 = s(MV ''nr'' tid3) &
           s(MV ''kIR'' tid2) = LN ''kIR'' tid3 &
           predOrd t (St( tid1, I_1 )) (St( tid2, R_1 )) &
           predOrd t (St( tid2, R_1 )) (St( tid2, R_2 )) &
           predOrd t (St( tid2, R_2 )) (St( tid3, S_2 )) &
           predOrd t (St( tid3, S_2 )) (St( tid3, S_3 )) &
           predOrd t (St( tid3, S_3 )) (St( tid2, R_3 ))))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT3'', LN ''nr'' tid2, s(MV ''kIR'' tid2) |}
                       ( K ( s(AV ''R'' tid2) ) ( s(AV ''S'' tid2) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (S_3_enc tid3) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', LN ''nr'' tid2, s(AV ''R'' tid2), s(MV ''R'' tid3) |}
                         ( K ( s(AV ''R'' tid2) ) ( s(AV ''S'' tid2) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (auto dest!: ltk_secrecy)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  next
    case (S_3_enc_1 tid3) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', s(MV ''ni'' tid3), LN ''nr'' tid2, s(MV ''I'' tid3),
                            s(AV ''R'' tid2)
                         |}
                         ( K ( s(AV ''R'' tid2) ) ( s(AV ''S'' tid2) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (auto dest!: ltk_secrecy)
    next
      case (R_2_enc tid4) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT1'', s(MV ''ni'' tid2), s(MV ''I'' tid2), s(AV ''R'' tid2)
                           |}
                           ( K ( s(MV ''I'' tid2) ) ( s(AV ''S'' tid2) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (I_1_enc tid4) note_unified facts = this facts
        have f1: "roleMap r tid4 = Some I" using facts by (auto intro: event_predOrdI)
        have f2: "LN ''ni'' tid4 : knows t" using facts by (auto intro: event_predOrdI)
        note facts = facts ni_first_send[OF f1 f2, simplified]
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

(* text: 
  Comparing the proofs of S_ni_agree and R_ni_agree we see that they are pretty
  similar. We have yet to find the right formulation that allows to share the
  similar subproofs.
 *)

lemma (in restricted_OtwayRees_state) S_ni_agree:
  assumes facts:
    "roleMap r tid3 = Some S"
    "RLKR(s(AV ''S'' tid3)) ~: reveals t"
    "RLKR(s(MV ''I'' tid3)) ~: reveals t"
    "RLKR(s(MV ''R'' tid3)) ~: reveals t"
    "( tid3, S_2 ) : steps t"
  shows
    "(?  tid1.
        (?  tid2.
           roleMap r tid1 = Some I &
           roleMap r tid2 = Some R &
           s(MV ''I'' tid2) = s(AV ''I'' tid1) &
           s(AV ''R'' tid2) = s(AV ''R'' tid1) &
           s(AV ''S'' tid2) = s(AV ''S'' tid1) &
           s(MV ''ni'' tid2) = LN ''ni'' tid1 &
           s(MV ''I'' tid2) = s(MV ''I'' tid3) &
           s(AV ''R'' tid2) = s(MV ''R'' tid3) &
           s(AV ''S'' tid2) = s(AV ''S'' tid3) &
           s(MV ''ni'' tid2) = s(MV ''ni'' tid3) &
           LN ''nr'' tid2 = s(MV ''nr'' tid3) &
           predOrd t (St( tid1, I_1 )) (St( tid2, R_1 )) &
           predOrd t (St( tid2, R_1 )) (St( tid2, R_2 )) &
           predOrd t (St( tid2, R_2 )) (St( tid3, S_2 ))))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(MV ''ni'' tid3), s(MV ''I'' tid3), s(MV ''R'' tid3)
                       |}
                       ( K ( s(MV ''I'' tid3) ) ( s(AV ''S'' tid3) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (I_1_enc tid4) note_unified facts = this facts
    have f1: "roleMap r tid4 = Some I" using facts by (auto intro: event_predOrdI)
    have f2: "LN ''ni'' tid4 : knows t" using facts by (auto intro: event_predOrdI)
    note facts = facts ni_first_send[OF f1 f2, simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', LN ''ni'' tid4, s(MV ''nr'' tid3), s(AV ''I'' tid4),
                            s(AV ''R'' tid4)
                         |}
                         ( K ( s(AV ''R'' tid4) ) ( s(AV ''S'' tid3) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (auto dest!: ltk_secrecy)
    next
      case (R_2_enc tid5) note_unified facts = this facts
      thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

end