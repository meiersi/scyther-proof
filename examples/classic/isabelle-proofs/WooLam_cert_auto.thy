theory "WooLam_cert_auto"
imports
  "ESPLogic"
begin

(* section:  Woo and Lam Mutual Authentication Protocol  *)

(* text: 
  Modeled after the description in the SPORE library:

    http://www.lsv.ens-cachan.fr/Software/spore/wooLamMutual.html

  Notable differences:

    1. We are using explicit global constants to discern between different
       encryptions instead of the implicit typing, which introduces
       ambiguities. This implies that we are not precisely modeling the Woo and
       Lam protocol of the SPORE library and hence we may miss some attacks
       possible on it. However, every implementation of the SPORE model could
       easily be changed to our version and benefit from the full correctness
       proof.
 *)

role A
where "A =
  [ Send ''1'' <| sAV ''A'', sN ''na'' |>
  , Recv ''2'' <| sMV ''B'', sMV ''nb'' |>
  , Send ''3'' ( PEnc <| sC ''enc3'', sAV ''A'', sMV ''B'', sN ''na'',
                         sMV ''nb''
                      |>
                      ( sK ''A'' ''S'' )
               )
  , Recv ''6'' <| PEnc <| sC ''enc51'', sMV ''B'', sN ''na'', sMV ''nb'',
                          sMV ''kab''
                       |>
                       ( sK ''A'' ''S'' ),
                  PEnc <| sC ''enc6'', sN ''na'', sMV ''nb'' |> ( sMV ''kab'' )
               |>
  , Send ''7'' ( PEnc <| sC ''enc7'', sMV ''nb'' |> ( sMV ''kab'' ) )
  ]"

role B
where "B =
  [ Recv ''1'' <| sMV ''A'', sMV ''na'' |>
  , Send ''2'' <| sAV ''B'', sN ''nb'' |>
  , Recv ''3'' ( sMV ''Ticket1'' )
  , Send ''4'' <| sMV ''Ticket1'',
                  PEnc <| sC ''enc4'', sMV ''A'', sAV ''B'', sMV ''na'', sN ''nb'' |>
                       ( sK ''B'' ''S'' )
               |>
  , Recv ''5'' <| sMV ''Ticket2'',
                  PEnc <| sC ''enc52'', sMV ''A'', sMV ''na'', sN ''nb'', sMV ''kab'' |>
                       ( sK ''B'' ''S'' )
               |>
  , Send ''6'' <| sMV ''Ticket2'',
                  PEnc <| sC ''enc6'', sMV ''na'', sN ''nb'' |> ( sMV ''kab'' )
               |>
  , Recv ''7'' ( PEnc <| sC ''enc7'', sN ''nb'' |> ( sMV ''kab'' ) )
  ]"

role S
where "S =
  [ Recv ''4'' <| PEnc <| sC ''enc3'', sMV ''A'', sMV ''B'', sMV ''na'',
                          sMV ''nb''
                       |>
                       ( PSymK ( sMV ''A'' ) ( sAV ''S'' ) ),
                  PEnc <| sC ''enc4'', sMV ''A'', sMV ''B'', sMV ''na'', sMV ''nb'' |>
                       ( PSymK ( sMV ''A'' ) ( sAV ''S'' ) )
               |>
  , Send ''5'' <| PEnc <| sC ''enc51'', sMV ''B'', sMV ''na'', sMV ''nb'',
                          sN ''kab''
                       |>
                       ( PSymK ( sMV ''A'' ) ( sAV ''S'' ) ),
                  PEnc <| sC ''enc52'', sMV ''A'', sMV ''na'', sMV ''nb'', sN ''kab'' |>
                       ( PSymK ( sMV ''B'' ) ( sAV ''S'' ) )
               |>
  ]"

protocol WooLam
where "WooLam = { A, B, S }"

locale restricted_WooLam_state = WooLam_state

type_invariant WooLam_msc_typing for WooLam
where "WooLam_msc_typing = mk_typing
  [ ((B, ''A''), (KnownT B_1))
  , ((S, ''A''), (SumT (KnownT S_4) AgentT))
  , ((A, ''B''), (KnownT A_2))
  , ((S, ''B''), (SumT (KnownT S_4) AgentT))
  , ((B, ''Ticket1''), (KnownT B_3))
  , ((B, ''Ticket2''), (KnownT B_5))
  , ((A, ''kab''), (SumT (KnownT A_6) (NonceT S ''kab'')))
  , ((B, ''kab''), (SumT (KnownT B_5) (NonceT S ''kab'')))
  , ((B, ''na''), (KnownT B_1))
  , ((S, ''na''), (SumT (KnownT S_4) (NonceT A ''na'')))
  , ((A, ''nb''), (KnownT A_2))
  , ((S, ''nb''), (SumT (KnownT S_4) (NonceT B ''nb'')))
  ]"

sublocale WooLam_state < WooLam_msc_typing_state
proof -
  have "(t,r,s) : approx WooLam_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF WooLam_msc_typing.monoTyp, completeness_cases_rule])
    case (A_2_B t r s tid0)
    then interpret state: WooLam_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_2_B
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (A_2_nb t r s tid0)
    then interpret state: WooLam_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_2_nb
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (A_6_kab t r s tid0)
    then interpret state: WooLam_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_6_kab
    thus ?case
    proof(sources! "
        Enc {| LC ''enc51'', s(MV ''B'' tid0), LN ''na'' tid0, s(MV ''nb'' tid0),
               s(MV ''kab'' tid0)
            |}
            ( K ( s(AV ''A'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (B_1_A t r s tid0)
    then interpret state: WooLam_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = B_1_A
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (B_1_na t r s tid0)
    then interpret state: WooLam_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = B_1_na
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (B_5_Ticket2 t r s tid0)
    then interpret state: WooLam_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = B_5_Ticket2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (B_5_kab t r s tid0)
    then interpret state: WooLam_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = B_5_kab
    thus ?case
    proof(sources! "
        Enc {| LC ''enc52'', s(MV ''A'' tid0), s(MV ''na'' tid0), LN ''nb'' tid0,
               s(MV ''kab'' tid0)
            |}
            ( K ( s(AV ''B'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (S_4_A t r s tid0)
    then interpret state: WooLam_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_4_A
    thus ?case
    proof(sources! "
        Enc {| LC ''enc3'', s(MV ''A'' tid0), s(MV ''B'' tid0),
               s(MV ''na'' tid0), s(MV ''nb'' tid0)
            |}
            ( K ( s(MV ''A'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (S_4_B t r s tid0)
    then interpret state: WooLam_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_4_B
    thus ?case
    proof(sources! "
        Enc {| LC ''enc3'', s(MV ''A'' tid0), s(MV ''B'' tid0),
               s(MV ''na'' tid0), s(MV ''nb'' tid0)
            |}
            ( K ( s(MV ''A'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (S_4_na t r s tid0)
    then interpret state: WooLam_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_4_na
    thus ?case
    proof(sources! "
        Enc {| LC ''enc3'', s(MV ''A'' tid0), s(MV ''B'' tid0),
               s(MV ''na'' tid0), s(MV ''nb'' tid0)
            |}
            ( K ( s(MV ''A'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (S_4_nb t r s tid0)
    then interpret state: WooLam_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_4_nb
    thus ?case
    proof(sources! "
        Enc {| LC ''enc3'', s(MV ''A'' tid0), s(MV ''B'' tid0),
               s(MV ''na'' tid0), s(MV ''nb'' tid0)
            |}
            ( K ( s(MV ''A'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  qed
  thus "WooLam_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context WooLam_state begin

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

lemma (in restricted_WooLam_state) S_sec_kab:
  assumes facts:
    "roleMap r tid0 = Some S"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "LN ''kab'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''kab'' tid0 ")
  case S_5_kab note_unified facts = this facts
  thus ?thesis by (auto dest!: ltk_secrecy)
next
  case S_5_kab_1 note_unified facts = this facts
  thus ?thesis by (auto dest!: ltk_secrecy)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

lemma (in restricted_WooLam_state) A_sec_kab:
  assumes facts:
    "roleMap r tid0 = Some A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "( tid0, A_6 ) : steps t"
    "s(MV ''kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc51'', s(MV ''B'' tid0), LN ''na'' tid0, s(MV ''nb'' tid0),
                          s(MV ''kab'' tid0)
                       |}
                       ( K ( s(AV ''A'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (S_5_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: S_sec_kab intro: event_predOrdI)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_WooLam_state) B_sec_kab:
  assumes facts:
    "roleMap r tid0 = Some B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, B_5 ) : steps t"
    "s(MV ''kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc52'', s(MV ''A'' tid0), s(MV ''na'' tid0), LN ''nb'' tid0,
                          s(MV ''kab'' tid0)
                       |}
                       ( K ( s(AV ''B'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (S_5_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: S_sec_kab intro: event_predOrdI)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_WooLam_state) A_sec_inv_kab:
  assumes facts:
    "roleMap r tid0 = Some A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "( tid0, A_6 ) : steps t"
    "inv(s(MV ''kab'' tid0)) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc51'', s(MV ''B'' tid0), LN ''na'' tid0, s(MV ''nb'' tid0),
                          s(MV ''kab'' tid0)
                       |}
                       ( K ( s(AV ''A'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (S_5_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: S_sec_kab intro: event_predOrdI)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_WooLam_state) B_sec_inv_kab:
  assumes facts:
    "roleMap r tid0 = Some B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, B_5 ) : steps t"
    "inv(s(MV ''kab'' tid0)) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc52'', s(MV ''A'' tid0), s(MV ''na'' tid0), LN ''nb'' tid0,
                          s(MV ''kab'' tid0)
                       |}
                       ( K ( s(AV ''B'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (S_5_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: S_sec_kab intro: event_predOrdI)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

(* subsection:  Authentication  *)

lemma (in restricted_WooLam_state) na_first_send:
  assumes facts:
    "roleMap r tid1 = Some A"
    "LN ''na'' tid1 : knows t"
  shows "predOrd t (St( tid1, A_1 )) (Ln(LN ''na'' tid1))"
using facts proof(sources! " LN ''na'' tid1 ")
  case A_1_na note_unified facts = this facts
  thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
next
  case A_3_na note_unified facts = this facts
  thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
next
  case (S_5_na tid2) note_unified facts = this facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(MV ''A'' tid2), s(MV ''B'' tid2), LN ''na'' tid1,
                          s(MV ''nb'' tid2)
                       |}
                       ( K ( s(MV ''A'' tid2) ) ( s(AV ''S'' tid2) ) ) ")
    case (A_3_enc tid3) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (safe?, simp_all?, insert facts, ((((clarsimp, order?) | order | fast))+)?)
next
  case (S_5_na_1 tid2) note_unified facts = this facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(MV ''A'' tid2), s(MV ''B'' tid2), LN ''na'' tid1,
                          s(MV ''nb'' tid2)
                       |}
                       ( K ( s(MV ''A'' tid2) ) ( s(AV ''S'' tid2) ) ) ")
    case (A_3_enc tid3) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (safe?, simp_all?, insert facts, ((((clarsimp, order?) | order | fast))+)?)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

lemma (in restricted_WooLam_state) nb_first_send:
  assumes facts:
    "roleMap r tid1 = Some B"
    "LN ''nb'' tid1 : knows t"
  shows "predOrd t (St( tid1, B_2 )) (Ln(LN ''nb'' tid1))"
using facts proof(sources! " LN ''nb'' tid1 ")
  case B_2_nb note_unified facts = this facts
  thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
next
  case B_4_nb note_unified facts = this facts
  thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
next
  case B_6_nb note_unified facts = this facts
  thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
next
  case (S_5_nb tid2) note_unified facts = this facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(MV ''A'' tid2), s(MV ''B'' tid2),
                          s(MV ''na'' tid2), LN ''nb'' tid1
                       |}
                       ( K ( s(MV ''A'' tid2) ) ( s(AV ''S'' tid2) ) ) ")
  qed (safe?, simp_all?, insert facts, ((((clarsimp, order?) | order | fast))+)?)
next
  case (S_5_nb_1 tid2) note_unified facts = this facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(MV ''A'' tid2), s(MV ''B'' tid2),
                          s(MV ''na'' tid2), LN ''nb'' tid1
                       |}
                       ( K ( s(MV ''A'' tid2) ) ( s(AV ''S'' tid2) ) ) ")
  qed (safe?, simp_all?, insert facts, ((((clarsimp, order?) | order | fast))+)?)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

lemma (in restricted_WooLam_state) A_ni_synch:
  assumes facts:
    "roleMap r tid1 = Some A"
    "RLKR(s(AV ''A'' tid1)) ~: reveals t"
    "RLKR(s(AV ''S'' tid1)) ~: reveals t"
    "RLKR(s(MV ''B'' tid1)) ~: reveals t"
    "( tid1, A_6 ) : steps t"
  shows
    "(?  tid2.
        (?  tid3.
           roleMap r tid2 = Some B &
           roleMap r tid3 = Some S &
           s(AV ''A'' tid1) = s(MV ''A'' tid2) &
           s(MV ''B'' tid1) = s(AV ''B'' tid2) &
           s(AV ''S'' tid1) = s(AV ''S'' tid2) &
           LN ''na'' tid1 = s(MV ''na'' tid2) &
           s(MV ''nb'' tid1) = LN ''nb'' tid2 &
           s(MV ''kab'' tid1) = s(MV ''kab'' tid2) &
           s(AV ''A'' tid1) = s(MV ''A'' tid3) &
           s(MV ''B'' tid1) = s(MV ''B'' tid3) &
           s(AV ''S'' tid1) = s(AV ''S'' tid3) &
           LN ''na'' tid1 = s(MV ''na'' tid3) &
           s(MV ''nb'' tid1) = s(MV ''nb'' tid3) &
           s(MV ''kab'' tid1) = LN ''kab'' tid3 &
           predOrd t (St( tid1, A_1 )) (St( tid2, B_1 )) &
           predOrd t (St( tid2, B_1 )) (St( tid2, B_2 )) &
           predOrd t (St( tid2, B_2 )) (St( tid1, A_2 )) &
           predOrd t (St( tid1, A_2 )) (St( tid1, A_3 )) &
           predOrd t (St( tid1, A_3 )) (St( tid3, S_4 )) &
           predOrd t (St( tid3, S_4 )) (St( tid3, S_5 )) &
           predOrd t (St( tid3, S_5 )) (St( tid2, B_5 )) &
           predOrd t (St( tid2, B_5 )) (St( tid2, B_6 )) &
           predOrd t (St( tid2, B_6 )) (St( tid1, A_6 )) &
           predOrd t (St( tid2, B_3 )) (St( tid2, B_4 )) &
           predOrd t (St( tid2, B_4 )) (St( tid3, S_4 ))))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc51'', s(MV ''B'' tid1), LN ''na'' tid1, s(MV ''nb'' tid1),
                          s(MV ''kab'' tid1)
                       |}
                       ( K ( s(AV ''A'' tid1) ) ( s(AV ''S'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (S_5_enc tid2) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''enc3'', s(AV ''A'' tid1), s(MV ''B'' tid1), LN ''na'' tid1,
                            s(MV ''nb'' tid1)
                         |}
                         ( K ( s(AV ''A'' tid1) ) ( s(AV ''S'' tid1) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (auto dest!: ltk_secrecy)
    next
      case (A_3_enc tid3) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc4'', s(AV ''A'' tid1), s(MV ''B'' tid1), LN ''na'' tid1,
                              s(MV ''nb'' tid1)
                           |}
                           ( K ( s(AV ''A'' tid1) ) ( s(AV ''S'' tid1) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (B_4_enc tid3) note_unified facts = this facts
        have f1: "roleMap r tid1 = Some A" using facts by (auto intro: event_predOrdI)
        have f2: "LN ''na'' tid1 : knows t" using facts by (auto intro: event_predOrdI)
        note facts = facts na_first_send[OF f1 f2, simplified]
        have f1: "roleMap r tid3 = Some B" using facts by (auto intro: event_predOrdI)
        have f2: "LN ''nb'' tid3 : knows t" using facts by (auto intro: event_predOrdI)
        note facts = facts nb_first_send[OF f1 f2, simplified]
        thus ?thesis proof(sources! "
                         Enc {| LC ''enc6'', LN ''na'' tid1, LN ''nb'' tid3 |}
                             ( LN ''kab'' tid2 ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastforce dest: S_sec_kab intro: event_predOrdI)
        next
          case (B_6_enc tid4) note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''enc52'', s(AV ''A'' tid1), LN ''na'' tid1, LN ''nb'' tid3,
                                  LN ''kab'' tid2
                               |}
                               ( K ( s(AV ''A'' tid1) ) ( s(AV ''S'' tid1) ) ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (auto dest!: ltk_secrecy)
          next
            case (S_5_enc_1 tid4) note_unified facts = this facts
            thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
          qed (safe?, simp_all?, insert facts, (fastforce+)?)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_WooLam_state) B_ni_synch:
  assumes facts:
    "roleMap r tid2 = Some B"
    "RLKR(s(AV ''B'' tid2)) ~: reveals t"
    "RLKR(s(AV ''S'' tid2)) ~: reveals t"
    "RLKR(s(MV ''A'' tid2)) ~: reveals t"
    "( tid2, B_7 ) : steps t"
  shows
    "(?  tid1.
        (?  tid3.
           roleMap r tid1 = Some A &
           roleMap r tid3 = Some S &
           s(MV ''A'' tid2) = s(AV ''A'' tid1) &
           s(AV ''B'' tid2) = s(MV ''B'' tid1) &
           s(AV ''S'' tid2) = s(AV ''S'' tid1) &
           s(MV ''na'' tid2) = LN ''na'' tid1 &
           LN ''nb'' tid2 = s(MV ''nb'' tid1) &
           s(MV ''kab'' tid2) = s(MV ''kab'' tid1) &
           s(MV ''A'' tid2) = s(MV ''A'' tid3) &
           s(AV ''B'' tid2) = s(MV ''B'' tid3) &
           s(AV ''S'' tid2) = s(AV ''S'' tid3) &
           s(MV ''na'' tid2) = s(MV ''na'' tid3) &
           LN ''nb'' tid2 = s(MV ''nb'' tid3) &
           s(MV ''kab'' tid2) = LN ''kab'' tid3 &
           predOrd t (St( tid1, A_1 )) (St( tid2, B_1 )) &
           predOrd t (St( tid2, B_1 )) (St( tid2, B_2 )) &
           predOrd t (St( tid2, B_2 )) (St( tid1, A_2 )) &
           predOrd t (St( tid1, A_2 )) (St( tid1, A_3 )) &
           predOrd t (St( tid1, A_3 )) (St( tid3, S_4 )) &
           predOrd t (St( tid3, S_4 )) (St( tid3, S_5 )) &
           predOrd t (St( tid3, S_5 )) (St( tid2, B_5 )) &
           predOrd t (St( tid2, B_5 )) (St( tid2, B_6 )) &
           predOrd t (St( tid2, B_6 )) (St( tid1, A_6 )) &
           predOrd t (St( tid1, A_6 )) (St( tid1, A_7 )) &
           predOrd t (St( tid1, A_7 )) (St( tid2, B_7 )) &
           predOrd t (St( tid2, B_3 )) (St( tid2, B_4 )) &
           predOrd t (St( tid2, B_4 )) (St( tid3, S_4 ))))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc52'', s(MV ''A'' tid2), s(MV ''na'' tid2), LN ''nb'' tid2,
                          s(MV ''kab'' tid2)
                       |}
                       ( K ( s(AV ''B'' tid2) ) ( s(AV ''S'' tid2) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (S_5_enc_1 tid3) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''enc3'', s(MV ''A'' tid2), s(AV ''B'' tid2),
                            s(MV ''na'' tid2), LN ''nb'' tid2
                         |}
                         ( K ( s(MV ''A'' tid2) ) ( s(AV ''S'' tid2) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (auto dest!: ltk_secrecy)
    next
      case (A_3_enc tid4) note_unified facts = this facts
      have f1: "roleMap r tid4 = Some A" using facts by (auto intro: event_predOrdI)
      have f2: "LN ''na'' tid4 : knows t" using facts by (auto intro: event_predOrdI)
      note facts = facts na_first_send[OF f1 f2, simplified]
      have f1: "roleMap r tid2 = Some B" using facts by (auto intro: event_predOrdI)
      have f2: "LN ''nb'' tid2 : knows t" using facts by (auto intro: event_predOrdI)
      note facts = facts nb_first_send[OF f1 f2, simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''enc7'', LN ''nb'' tid2 |} ( LN ''kab'' tid3 ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest: S_sec_kab intro: event_predOrdI)
      next
        case (A_7_enc tid5) note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''enc4'', s(AV ''A'' tid4), s(AV ''B'' tid2), LN ''na'' tid4,
                                LN ''nb'' tid2
                             |}
                             ( K ( s(AV ''A'' tid4) ) ( s(AV ''S'' tid2) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (auto dest!: ltk_secrecy)
        next
          case (B_4_enc tid6) note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''enc6'', LN ''na'' tid5, LN ''nb'' tid2 |}
                               ( LN ''kab'' tid3 ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastforce dest: S_sec_kab intro: event_predOrdI)
          next
            case (B_6_enc tid6) note_unified facts = this facts
            thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
          qed (safe?, simp_all?, insert facts, (fastforce+)?)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_WooLam_state) S_ni_synch:
  assumes facts:
    "roleMap r tid3 = Some S"
    "RLKR(s(AV ''S'' tid3)) ~: reveals t"
    "RLKR(s(MV ''A'' tid3)) ~: reveals t"
    "RLKR(s(MV ''B'' tid3)) ~: reveals t"
    "( tid3, S_4 ) : steps t"
  shows
    "(?  tid1.
        (?  tid2.
           roleMap r tid1 = Some A &
           roleMap r tid2 = Some B &
           s(MV ''A'' tid2) = s(AV ''A'' tid1) &
           s(AV ''B'' tid2) = s(MV ''B'' tid1) &
           s(AV ''S'' tid2) = s(AV ''S'' tid1) &
           s(MV ''na'' tid2) = LN ''na'' tid1 &
           LN ''nb'' tid2 = s(MV ''nb'' tid1) &
           s(MV ''A'' tid2) = s(MV ''A'' tid3) &
           s(AV ''B'' tid2) = s(MV ''B'' tid3) &
           s(AV ''S'' tid2) = s(AV ''S'' tid3) &
           s(MV ''na'' tid2) = s(MV ''na'' tid3) &
           LN ''nb'' tid2 = s(MV ''nb'' tid3) &
           predOrd t (St( tid1, A_1 )) (St( tid2, B_1 )) &
           predOrd t (St( tid2, B_1 )) (St( tid2, B_2 )) &
           predOrd t (St( tid2, B_2 )) (St( tid1, A_2 )) &
           predOrd t (St( tid1, A_2 )) (St( tid1, A_3 )) &
           predOrd t (St( tid1, A_3 )) (St( tid3, S_4 )) &
           predOrd t (St( tid2, B_3 )) (St( tid2, B_4 )) &
           predOrd t (St( tid2, B_4 )) (St( tid3, S_4 ))))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''enc3'', s(MV ''A'' tid3), s(MV ''B'' tid3),
                          s(MV ''na'' tid3), s(MV ''nb'' tid3)
                       |}
                       ( K ( s(MV ''A'' tid3) ) ( s(AV ''S'' tid3) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (A_3_enc tid4) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''enc4'', s(AV ''A'' tid4), s(MV ''B'' tid3), LN ''na'' tid4,
                            s(MV ''nb'' tid3)
                         |}
                         ( K ( s(AV ''A'' tid4) ) ( s(AV ''S'' tid3) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (auto dest!: ltk_secrecy)
    next
      case (B_4_enc tid5) note_unified facts = this facts
      have f1: "roleMap r tid4 = Some A" using facts by (auto intro: event_predOrdI)
      have f2: "LN ''na'' tid4 : knows t" using facts by (auto intro: event_predOrdI)
      note facts = facts na_first_send[OF f1 f2, simplified]
      have f1: "roleMap r tid5 = Some B" using facts by (auto intro: event_predOrdI)
      have f2: "LN ''nb'' tid5 : knows t" using facts by (auto intro: event_predOrdI)
      note facts = facts nb_first_send[OF f1 f2, simplified]
      thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

end