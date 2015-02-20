theory "Wide_Mouth_Frog_cert_auto"
imports
  "ESPLogic"
begin

(* section:  Wide Mouthed Frog  *)

(* text: 
  The protocol is modeled after the description in the SPORE library:

    http://www.lsv.ens-cachan.fr/Software/spore/wideMouthedFrog.html

  Timestamps are modelled as fresh numbers that are immediatly made public.
 *)

role I
where "I =
  [ Send ''1_leak'' ( sN ''TimeI'' )
  , Send ''1'' <| sAV ''I'', sAV ''R'',
                  PEnc <| sC ''1'', sN ''TimeI'', sAV ''R'', sN ''kIR'' |>
                       ( sK ''I'' ''S'' )
               |>
  ]"

role R
where "R =
  [ Recv ''2'' <| sMV ''S'', sMV ''I'',
                  PEnc <| sC ''2'', sMV ''TimeS'', sMV ''I'', sMV ''kIR'' |>
                       ( PSymK ( sAV ''R'' ) ( sMV ''S'' ) )
               |>
  ]"

role S
where "S =
  [ Recv ''1'' <| sMV ''I'', sMV ''R'',
                  PEnc <| sC ''1'', sMV ''TimeI'', sMV ''R'', sMV ''kIR'' |>
                       ( PSymK ( sMV ''I'' ) ( sAV ''S'' ) )
               |>
  , Send ''2_leak'' ( sN ''TimeS'' )
  , Send ''2'' <| sAV ''S'', sMV ''I'',
                  PEnc <| sC ''2'', sN ''TimeS'', sMV ''I'', sMV ''kIR'' |>
                       ( PSymK ( sMV ''R'' ) ( sAV ''S'' ) )
               |>
  ]"

protocol WMF
where "WMF = { I, R, S }"

locale restricted_WMF_state = WMF_state

type_invariant WMF_msc_typing for WMF
where "WMF_msc_typing = mk_typing
  [ ((R, ''I''), (KnownT R_2))
  , ((S, ''I''), (KnownT S_1))
  , ((S, ''R''), (KnownT S_1))
  , ((R, ''S''), (KnownT R_2))
  , ((S, ''TimeI''), (SumT (KnownT S_1) (NonceT I ''TimeI'')))
  , ((R, ''TimeS''), (SumT (KnownT R_2) (NonceT S ''TimeS'')))
  , ((R, ''kIR''), (SumT (KnownT R_2) (NonceT I ''kIR'')))
  , ((S, ''kIR''), (SumT (KnownT S_1) (NonceT I ''kIR'')))
  ]"

sublocale WMF_state < WMF_msc_typing_state
proof -
  have "(t,r,s) : approx WMF_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF WMF_msc_typing.monoTyp, completeness_cases_rule])
    case (R_2_I t r s tid0)
    then interpret state: WMF_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = R_2_I
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (R_2_S t r s tid0)
    then interpret state: WMF_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = R_2_S
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (R_2_TimeS t r s tid0)
    then interpret state: WMF_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = R_2_TimeS
    thus ?case
    proof(sources! "
        Enc {| LC ''2'', s(MV ''TimeS'' tid0), s(MV ''I'' tid0),
               s(MV ''kIR'' tid0)
            |}
            ( K ( s(AV ''R'' tid0) ) ( s(MV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (R_2_kIR t r s tid0)
    then interpret state: WMF_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = R_2_kIR
    thus ?case
    proof(sources! "
        Enc {| LC ''2'', s(MV ''TimeS'' tid0), s(MV ''I'' tid0),
               s(MV ''kIR'' tid0)
            |}
            ( K ( s(AV ''R'' tid0) ) ( s(MV ''S'' tid0) ) ) ")
      case (S_2_enc tid1) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''1'', s(MV ''TimeI'' tid1), s(AV ''R'' tid0),
                              s(MV ''kIR'' tid0)
                           |}
                           ( K ( s(MV ''I'' tid0) ) ( s(AV ''S'' tid1) ) ) ")
      qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (S_1_I t r s tid0)
    then interpret state: WMF_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_1_I
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (S_1_R t r s tid0)
    then interpret state: WMF_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_1_R
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (S_1_TimeI t r s tid0)
    then interpret state: WMF_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_1_TimeI
    thus ?case
    proof(sources! "
        Enc {| LC ''1'', s(MV ''TimeI'' tid0), s(MV ''R'' tid0),
               s(MV ''kIR'' tid0)
            |}
            ( K ( s(MV ''I'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (S_1_kIR t r s tid0)
    then interpret state: WMF_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_1_kIR
    thus ?case
    proof(sources! "
        Enc {| LC ''1'', s(MV ''TimeI'' tid0), s(MV ''R'' tid0),
               s(MV ''kIR'' tid0)
            |}
            ( K ( s(MV ''I'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  qed
  thus "WMF_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context WMF_state begin

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

lemma (in restricted_WMF_state) I_kIR_sec:
  assumes facts:
    "roleMap r tid0 = Some I"
    "RLKR(s(AV ''I'' tid0)) ~: reveals t"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "LN ''kIR'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''kIR'' tid0 ")
  case I_1_kIR note_unified facts = this facts
  thus ?thesis by (auto dest!: ltk_secrecy)
next
  case (S_2_kIR tid1) note_unified facts = this facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''1'', s(MV ''TimeI'' tid1), s(MV ''R'' tid1), LN ''kIR'' tid0
                       |}
                       ( K ( s(MV ''I'' tid1) ) ( s(AV ''S'' tid1) ) ) ")
    case (I_1_enc tid2) note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  qed (safe?, simp_all?, insert facts, ((((clarsimp, order?) | order | fast))+)?)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

lemma (in restricted_WMF_state) S_kIR_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''I'' tid0)) ~: reveals t"
    "RLKR(s(MV ''R'' tid0)) ~: reveals t"
    "( tid0, S_1 ) : steps t"
    "s(MV ''kIR'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''1'', s(MV ''TimeI'' tid0), s(MV ''R'' tid0),
                          s(MV ''kIR'' tid0)
                       |}
                       ( K ( s(MV ''I'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (I_1_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: I_kIR_sec intro: event_predOrdI)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_WMF_state) R_kIR_sec:
  assumes facts:
    "roleMap r tid0 = Some R"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "RLKR(s(MV ''I'' tid0)) ~: reveals t"
    "RLKR(s(MV ''S'' tid0)) ~: reveals t"
    "( tid0, R_2 ) : steps t"
    "s(MV ''kIR'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''2'', s(MV ''TimeS'' tid0), s(MV ''I'' tid0),
                          s(MV ''kIR'' tid0)
                       |}
                       ( K ( s(AV ''R'' tid0) ) ( s(MV ''S'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (S_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: S_kIR_sec intro: event_predOrdI)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

(* subsection:  Authentication Properties  *)

(* text: 
  The authentication guarantee for the initiator is trivial because it does not
  receive any confirmation that the responder received the new session-key.
 *)

lemma (in restricted_WMF_state) S_ni_synch:
  assumes facts:
    "roleMap r tid3 = Some S"
    "RLKR(s(AV ''S'' tid3)) ~: reveals t"
    "RLKR(s(MV ''I'' tid3)) ~: reveals t"
    "( tid3, S_1 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some I &
        s(AV ''I'' tid1) = s(MV ''I'' tid3) &
        s(AV ''R'' tid1) = s(MV ''R'' tid3) &
        s(AV ''S'' tid1) = s(AV ''S'' tid3) &
        LN ''TimeI'' tid1 = s(MV ''TimeI'' tid3) &
        LN ''kIR'' tid1 = s(MV ''kIR'' tid3) &
        predOrd t (St( tid1, I_1 )) (St( tid3, S_1 )))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''1'', s(MV ''TimeI'' tid3), s(MV ''R'' tid3),
                          s(MV ''kIR'' tid3)
                       |}
                       ( K ( s(MV ''I'' tid3) ) ( s(AV ''S'' tid3) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (I_1_enc tid4) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_WMF_state) R_ni_synch:
  assumes facts:
    "roleMap r tid2 = Some R"
    "RLKR(s(AV ''R'' tid2)) ~: reveals t"
    "RLKR(s(MV ''I'' tid2)) ~: reveals t"
    "RLKR(s(MV ''S'' tid2)) ~: reveals t"
    "( tid2, R_2 ) : steps t"
  shows
    "(?  tid1.
        (?  tid3.
           roleMap r tid1 = Some I &
           roleMap r tid3 = Some S &
           s(AV ''I'' tid1) = s(MV ''I'' tid2) &
           s(MV ''I'' tid2) = s(MV ''I'' tid3) &
           s(AV ''R'' tid1) = s(AV ''R'' tid2) &
           s(AV ''R'' tid2) = s(MV ''R'' tid3) &
           s(AV ''S'' tid1) = s(MV ''S'' tid2) &
           s(MV ''S'' tid2) = s(AV ''S'' tid3) &
           LN ''TimeI'' tid1 = s(MV ''TimeI'' tid3) &
           s(MV ''TimeS'' tid2) = LN ''TimeS'' tid3 &
           LN ''kIR'' tid1 = s(MV ''kIR'' tid2) &
           s(MV ''kIR'' tid2) = s(MV ''kIR'' tid3) &
           predOrd t (St( tid1, I_1 )) (St( tid3, S_1 )) &
           predOrd t (St( tid3, S_1 )) (St( tid3, S_2 )) &
           predOrd t (St( tid3, S_2 )) (St( tid2, R_2 ))))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''2'', s(MV ''TimeS'' tid2), s(MV ''I'' tid2),
                          s(MV ''kIR'' tid2)
                       |}
                       ( K ( s(AV ''R'' tid2) ) ( s(MV ''S'' tid2) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (S_2_enc tid3) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''1'', s(MV ''TimeI'' tid3), s(AV ''R'' tid2),
                            s(MV ''kIR'' tid2)
                         |}
                         ( K ( s(MV ''I'' tid2) ) ( s(AV ''S'' tid3) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (auto dest!: ltk_secrecy)
    next
      case (I_1_enc tid4) note_unified facts = this facts
      thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

end