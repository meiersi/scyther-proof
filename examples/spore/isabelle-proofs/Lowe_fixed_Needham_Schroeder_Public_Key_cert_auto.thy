theory "Lowe_fixed_Needham_Schroeder_Public_Key_cert_auto"
imports
  "ESPLogic"
begin

(* section:  Needham-Schroeder-Lowe Public-Key Protocol  *)

(* text: 
  Modelled after SPORE.

  Notable differences:
    1. We use explicit global constants instead of implicit typing to discern
       the different messages.
    
    2. We model a single certificate-authority (CA) server role, which is used
       to answer the certificate requests from both A and B.

    2. We prove non-injective synchronization, which is stronger than the
       entity authentication property stated in SPORE as the requirement on
       this protocol.

 *)

role I
where "I =
  [ Send ''ca1'' <| sAV ''I'', sAV ''R'' |>
  , Recv ''ca2'' <| sMV ''S'',
                    PSign <| sC ''ca2'', sMV ''pkR'', sAV ''R'' |> ( PAsymPK ( sMV ''S'' ) )
                 |>
  , Send ''1'' <| sAV ''I'',
                  PEnc <| sC ''1'', sN ''ni'', sAV ''I'' |> ( sMV ''pkR'' )
               |>
  , Recv ''2'' ( PEnc <| sC ''2'', sN ''ni'', sMV ''nr'', sAV ''R'' |>
                      ( sPK ''I'' )
               )
  , Send ''3'' ( PEnc <| sC ''3'', sMV ''nr'' |> ( sMV ''pkR'' ) )
  ]"

role R
where "R =
  [ Recv ''1'' <| sMV ''I'',
                  PEnc <| sC ''1'', sMV ''ni'', sMV ''I'' |> ( sPK ''R'' )
               |>
  , Send ''ca1'' <| sAV ''R'', sMV ''I'' |>
  , Recv ''ca2'' <| sMV ''S'',
                    PSign <| sC ''ca2'', sMV ''pkI'', sMV ''I'' |> ( PAsymPK ( sMV ''S'' ) )
                 |>
  , Send ''2'' ( PEnc <| sC ''2'', sMV ''ni'', sN ''nr'', sAV ''R'' |>
                      ( sMV ''pkI'' )
               )
  , Recv ''3'' ( PEnc <| sC ''3'', sN ''nr'' |> ( sPK ''R'' ) )
  ]"

role S
where "S =
  [ Recv ''ca1'' <| sMV ''A'', sMV ''B'' |>
  , Send ''ca2'' <| sAV ''S'',
                    PSign <| sC ''ca2'', PAsymPK ( sMV ''B'' ), sMV ''B'' |> ( sPK ''S'' )
                 |>
  ]"

protocol NSLPK
where "NSLPK = { I, R, S }"

locale restricted_NSLPK_state = NSLPK_state +
  assumes I_uncompromised_S:
    "!! tid1.
       [| roleMap r tid1 = Some I |] ==> RLKR(s(MV ''S'' tid1)) ~: reveals t"
  assumes R_uncompromised_S:
    "!! tid1.
       [| roleMap r tid1 = Some R |] ==> RLKR(s(MV ''S'' tid1)) ~: reveals t"

type_invariant NSLPK_msc_typing for NSLPK
where "NSLPK_msc_typing = mk_typing
  [ ((S, ''A''), (KnownT S_ca1))
  , ((S, ''B''), (KnownT S_ca1))
  , ((R, ''I''), (KnownT R_1))
  , ((I, ''S''), (KnownT I_ca2))
  , ((R, ''S''), (KnownT R_ca2))
  , ((R, ''ni''), (SumT (KnownT R_1) (NonceT I ''ni'')))
  , ((I, ''nr''), (SumT (KnownT I_2) (NonceT R ''nr'')))
  , ((R, ''pkI''), (KnownT R_ca2))
  , ((I, ''pkR''), (KnownT I_ca2))
  ]"

sublocale NSLPK_state < NSLPK_msc_typing_state
proof -
  have "(t,r,s) : approx NSLPK_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF NSLPK_msc_typing.monoTyp, completeness_cases_rule])
    case (I_ca2_S t r s tid0)
    then interpret state: NSLPK_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = I_ca2_S
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (I_ca2_pkR t r s tid0)
    then interpret state: NSLPK_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = I_ca2_pkR
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (I_2_nr t r s tid0)
    then interpret state: NSLPK_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = I_2_nr
    thus ?case
    proof(sources! "
        Enc {| LC ''2'', LN ''ni'' tid0, s(MV ''nr'' tid0), s(AV ''R'' tid0) |}
            ( PK ( s(AV ''I'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (R_1_I t r s tid0)
    then interpret state: NSLPK_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = R_1_I
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (R_1_ni t r s tid0)
    then interpret state: NSLPK_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = R_1_ni
    thus ?case
    proof(sources! "
        Enc {| LC ''1'', s(MV ''ni'' tid0), s(MV ''I'' tid0) |}
            ( PK ( s(AV ''R'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (R_ca2_S t r s tid0)
    then interpret state: NSLPK_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = R_ca2_S
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (R_ca2_pkI t r s tid0)
    then interpret state: NSLPK_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = R_ca2_pkI
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (S_ca1_A t r s tid0)
    then interpret state: NSLPK_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_ca1_A
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (S_ca1_B t r s tid0)
    then interpret state: NSLPK_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = S_ca1_B
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "NSLPK_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context NSLPK_state begin

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

(* subsection:  Assumptions  *)

(* text:  
  Initiators as well as responders talk to an uncompromised server. 
 *)



(* subsection:  Security Properties  *)

lemma (in restricted_NSLPK_state) I_pkR_auth:
  assumes facts:
    "roleMap r tid1 = Some I"
    "( tid1, I_ca2 ) : steps t"
  shows "s(MV ''pkR'' tid1) = PK ( s(AV ''R'' tid1) )"
proof -
  note_prefix_closed facts = facts
  have f1: "roleMap r tid1 = Some I" using facts by (auto intro: event_predOrdI)
  note facts = facts I_uncompromised_S[OF f1, simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''ca2'', s(MV ''pkR'' tid1), s(AV ''R'' tid1) |}
                       ( SK ( s(MV ''S'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (S_ca2_enc tid2) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_NSLPK_state) R_pkI_auth:
  assumes facts:
    "roleMap r tid1 = Some R"
    "( tid1, R_ca2 ) : steps t"
  shows "s(MV ''pkI'' tid1) = PK ( s(MV ''I'' tid1) )"
proof -
  note_prefix_closed facts = facts
  have f1: "roleMap r tid1 = Some R" using facts by (auto intro: event_predOrdI)
  note facts = facts R_uncompromised_S[OF f1, simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''ca2'', s(MV ''pkI'' tid1), s(MV ''I'' tid1) |}
                       ( SK ( s(MV ''S'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (S_ca2_enc tid2) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_NSLPK_state) I_ni_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "RLKR(s(AV ''I'' tid0)) ~: reveals t"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "LN ''ni'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''ni'' tid0 ")
  case I_1_ni note_unified facts = this facts
  have f1: "roleMap r tid0 = Some I" using facts by (auto intro: event_predOrdI)
  have f2: "( tid0, I_ca2
            ) : steps t" using facts by (auto intro: event_predOrdI)
  note facts = facts I_pkR_auth[OF f1 f2, simplified]
  thus ?thesis by (auto dest!: ltk_secrecy)
next
  case (R_2_ni tid1) note_unified facts = this facts
  have f1: "roleMap r tid1 = Some R" using facts by (auto intro: event_predOrdI)
  have f2: "( tid1, R_ca2
            ) : steps t" using facts by (auto intro: event_predOrdI)
  note facts = facts R_pkI_auth[OF f1 f2, simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''1'', LN ''ni'' tid0, s(MV ''I'' tid1) |}
                       ( PK ( s(AV ''R'' tid1) ) ) ")
    case (I_1_enc tid2) note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  qed (safe?, simp_all?, insert facts, ((((clarsimp, order?) | order | fast))+)?)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

lemma (in restricted_NSLPK_state) R_nr_secrecy:
  assumes facts:
    "roleMap r tid0 = Some R"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "RLKR(s(MV ''I'' tid0)) ~: reveals t"
    "LN ''nr'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''nr'' tid0 ")
  case (I_3_nr tid1) note_unified facts = this facts
  have f1: "roleMap r tid1 = Some I" using facts by (auto intro: event_predOrdI)
  have f2: "( tid1, I_ca2
            ) : steps t" using facts by (auto intro: event_predOrdI)
  note facts = facts I_pkR_auth[OF f1 f2, simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''2'', LN ''ni'' tid1, LN ''nr'' tid0, s(AV ''R'' tid1) |}
                       ( PK ( s(AV ''I'' tid1) ) ) ")
    case (R_2_enc tid2) note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  qed (safe?, simp_all?, insert facts, ((((clarsimp, order?) | order | fast))+)?)
next
  case R_2_nr note_unified facts = this facts
  have f1: "roleMap r tid0 = Some R" using facts by (auto intro: event_predOrdI)
  have f2: "( tid0, R_ca2
            ) : steps t" using facts by (auto intro: event_predOrdI)
  note facts = facts R_pkI_auth[OF f1 f2, simplified]
  thus ?thesis by (auto dest!: ltk_secrecy)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

lemma (in restricted_NSLPK_state) I_nr_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "RLKR(s(AV ''I'' tid0)) ~: reveals t"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "( tid0, I_2 ) : steps t"
    "s(MV ''nr'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''2'', LN ''ni'' tid0, s(MV ''nr'' tid0), s(AV ''R'' tid0) |}
                       ( PK ( s(AV ''I'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest: I_ni_secrecy intro: event_predOrdI)
  next
    case (R_2_enc tid1) note_unified facts = this facts
    have f1: "roleMap r tid1 = Some R" using facts by (auto intro: event_predOrdI)
    have f2: "( tid1, R_ca2
              ) : steps t" using facts by (auto intro: event_predOrdI)
    note facts = facts R_pkI_auth[OF f1 f2, simplified]
    thus ?thesis by (fastforce dest: R_nr_secrecy intro: event_predOrdI)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_NSLPK_state) R_ni_secrecy:
  assumes facts:
    "roleMap r tid0 = Some R"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "RLKR(s(MV ''I'' tid0)) ~: reveals t"
    "( tid0, R_3 ) : steps t"
    "s(MV ''ni'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  have f1: "roleMap r tid0 = Some R" using facts by (auto intro: event_predOrdI)
  have f2: "( tid0, R_ca2
            ) : steps t" using facts by (auto intro: event_predOrdI)
  note facts = facts R_pkI_auth[OF f1 f2, simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''3'', LN ''nr'' tid0 |} ( PK ( s(AV ''R'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest: R_nr_secrecy intro: event_predOrdI)
  next
    case (I_3_enc tid1) note_unified facts = this facts
    have f1: "roleMap r tid1 = Some I" using facts by (auto intro: event_predOrdI)
    have f2: "( tid1, I_ca2
              ) : steps t" using facts by (auto intro: event_predOrdI)
    note facts = facts I_pkR_auth[OF f1 f2, simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''2'', LN ''ni'' tid1, LN ''nr'' tid0, s(AV ''R'' tid0) |}
                         ( PK ( s(AV ''I'' tid1) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastforce dest: R_nr_secrecy intro: event_predOrdI)
    next
      case (R_2_enc tid2) note_unified facts = this facts
      thus ?thesis by (fastforce dest: I_ni_secrecy intro: event_predOrdI)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_NSLPK_state) I_noninjective_synch:
  assumes facts:
    "roleMap r tid1 = Some I"
    "RLKR(s(AV ''I'' tid1)) ~: reveals t"
    "RLKR(s(AV ''R'' tid1)) ~: reveals t"
    "( tid1, I_2 ) : steps t"
  shows
    "(?  tid2.
        roleMap r tid2 = Some R &
        s(AV ''I'' tid1) = s(MV ''I'' tid2) &
        s(AV ''R'' tid1) = s(AV ''R'' tid2) &
        LN ''ni'' tid1 = s(MV ''ni'' tid2) &
        s(MV ''nr'' tid1) = LN ''nr'' tid2 &
        predOrd t (St( tid1, I_1 )) (St( tid2, R_1 )) &
        predOrd t (St( tid2, R_2 )) (St( tid1, I_2 )) &
        predOrd t (St( tid1, I_1 )) (St( tid1, I_2 )) &
        predOrd t (St( tid2, R_1 )) (St( tid2, R_2 )))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''2'', LN ''ni'' tid1, s(MV ''nr'' tid1), s(AV ''R'' tid1) |}
                       ( PK ( s(AV ''I'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest: I_ni_secrecy intro: event_predOrdI)
  next
    case (R_2_enc tid2) note_unified facts = this facts
    have f1: "roleMap r tid2 = Some R" using facts by (auto intro: event_predOrdI)
    have f2: "( tid2, R_ca2
              ) : steps t" using facts by (auto intro: event_predOrdI)
    note facts = facts R_pkI_auth[OF f1 f2, simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''1'', LN ''ni'' tid1, s(AV ''I'' tid1) |}
                         ( PK ( s(AV ''R'' tid1) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastforce dest: I_ni_secrecy intro: event_predOrdI)
    next
      case (I_1_enc tid3) note_unified facts = this facts
      thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_NSLPK_state) R_noninjective_synch:
  assumes facts:
    "roleMap r tid2 = Some R"
    "RLKR(s(AV ''R'' tid2)) ~: reveals t"
    "RLKR(s(MV ''I'' tid2)) ~: reveals t"
    "( tid2, R_3 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some I &
        s(AV ''I'' tid1) = s(MV ''I'' tid2) &
        s(AV ''R'' tid1) = s(AV ''R'' tid2) &
        LN ''ni'' tid1 = s(MV ''ni'' tid2) &
        s(MV ''nr'' tid1) = LN ''nr'' tid2 &
        predOrd t (St( tid1, I_1 )) (St( tid2, R_1 )) &
        predOrd t (St( tid2, R_2 )) (St( tid1, I_2 )) &
        predOrd t (St( tid1, I_3 )) (St( tid2, R_3 )) &
        predOrd t (St( tid1, I_1 )) (St( tid1, I_2 )) &
        predOrd t (St( tid1, I_2 )) (St( tid1, I_3 )) &
        predOrd t (St( tid2, R_1 )) (St( tid2, R_2 )) &
        predOrd t (St( tid2, R_2 )) (St( tid2, R_3 )))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''1'', s(MV ''ni'' tid2), s(MV ''I'' tid2) |}
                       ( PK ( s(AV ''R'' tid2) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest: R_ni_secrecy intro: event_predOrdI)
  next
    case (I_1_enc tid3) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''3'', LN ''nr'' tid2 |} ( PK ( s(AV ''R'' tid2) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastforce dest: R_nr_secrecy intro: event_predOrdI)
    next
      case (I_3_enc tid4) note_unified facts = this facts
      have f1: "roleMap r tid4 = Some I" using facts by (auto intro: event_predOrdI)
      have f2: "( tid4, I_ca2
                ) : steps t" using facts by (auto intro: event_predOrdI)
      note facts = facts I_pkR_auth[OF f1 f2, simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''2'', LN ''ni'' tid4, LN ''nr'' tid2, s(AV ''R'' tid2) |}
                           ( PK ( s(AV ''I'' tid4) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest: R_nr_secrecy intro: event_predOrdI)
      next
        case (R_2_enc tid5) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

end