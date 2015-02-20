theory "BKE_cert_auto"
imports
  "ESPLogic"
begin

(* section:  Bilateral Key Exchange with Public Key protocol (BKEPK)  *)

(* text: 
  Modeled after the description 6.6.6 in the Clark-Jacob library:

   http://www.csl.sri.com/users/millen/capsl/library2.html

 Notable differences:

   1. We are using explicit global constants to identify the different
      encryptions instead of implicit typing.

 *)

role I
where "I =
  [ Send ''1'' <| sAV ''I'',
                  PEnc <| sC ''TT1'', sN ''ni'', sAV ''I'' |> ( sPK ''R'' )
               |>
  , Recv ''2'' ( PEnc <| sC ''TT2'', PHash ( sN ''ni'' ), sMV ''nr'',
                         sAV ''R'', sMV ''kir''
                      |>
                      ( sPK ''I'' )
               )
  , Send ''3'' ( PEnc <| sC ''TT3'', PHash ( sMV ''nr'' ) |>
                      ( sMV ''kir'' )
               )
  ]"

role R
where "R =
  [ Recv ''1'' <| sMV ''I'',
                  PEnc <| sC ''TT1'', sMV ''ni'', sMV ''I'' |> ( sPK ''R'' )
               |>
  , Send ''2'' ( PEnc <| sC ''TT2'', PHash ( sMV ''ni'' ), sN ''nr'',
                         sAV ''R'', sN ''kir''
                      |>
                      ( PAsymPK ( sMV ''I'' ) )
               )
  , Recv ''3'' ( PEnc <| sC ''TT3'', PHash ( sN ''nr'' ) |> ( sN ''kir'' )
               )
  ]"

protocol BKE
where "BKE = { I, R }"

locale restricted_BKE_state = BKE_state

(* subsection:  Secrecy Properties  *)

type_invariant auto_msc_typing for BKE
where "auto_msc_typing = mk_typing
  [ ((R, ''I''), (KnownT R_1))
  , ((I, ''kir''), (SumT (KnownT I_2) (NonceT R ''kir'')))
  , ((R, ''ni''), (SumT (KnownT R_1) (NonceT I ''ni'')))
  , ((I, ''nr''), (SumT (KnownT I_2) (NonceT R ''nr'')))
  ]"

sublocale BKE_state < auto_msc_typing_state
proof -
  have "(t,r,s) : approx auto_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF auto_msc_typing.monoTyp, completeness_cases_rule])
    case (I_2_kir t r s tid0)
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = I_2_kir
    thus ?case
    proof(sources! "
        Enc {| LC ''TT2'', Hash ( LN ''ni'' tid0 ), s(MV ''nr'' tid0),
               s(AV ''R'' tid0), s(MV ''kir'' tid0)
            |}
            ( PK ( s(AV ''I'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (I_2_nr t r s tid0)
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = I_2_nr
    thus ?case
    proof(sources! "
        Enc {| LC ''TT2'', Hash ( LN ''ni'' tid0 ), s(MV ''nr'' tid0),
               s(AV ''R'' tid0), s(MV ''kir'' tid0)
            |}
            ( PK ( s(AV ''I'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (R_1_I t r s tid0)
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = R_1_I
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (R_1_ni t r s tid0)
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = R_1_ni
    thus ?case
    proof(sources! "
        Enc {| LC ''TT1'', s(MV ''ni'' tid0), s(MV ''I'' tid0) |}
            ( PK ( s(AV ''R'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  qed
  thus "auto_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context BKE_state begin

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

lemma (in restricted_BKE_state) I_ni_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "RLKR(s(AV ''I'' tid0)) ~: reveals t"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "LN ''ni'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''ni'' tid0 ")
  case I_1_ni note_unified facts = this facts
  thus ?thesis by (auto dest!: ltk_secrecy)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

lemma (in restricted_BKE_state) R_nr_secrecy:
  assumes facts:
    "roleMap r tid0 = Some R"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "RLKR(s(MV ''I'' tid0)) ~: reveals t"
    "LN ''nr'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''nr'' tid0 ")
  case R_2_nr note_unified facts = this facts
  thus ?thesis by (auto dest!: ltk_secrecy)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

lemma (in restricted_BKE_state) R_kir_secrecy:
  assumes facts:
    "roleMap r tid0 = Some R"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "RLKR(s(MV ''I'' tid0)) ~: reveals t"
    "LN ''kir'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''kir'' tid0 ")
  case R_2_kir note_unified facts = this facts
  thus ?thesis by (auto dest!: ltk_secrecy)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

lemma (in restricted_BKE_state) I_hash_ni_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "RLKR(s(AV ''I'' tid0)) ~: reveals t"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "Hash ( LN ''ni'' tid0 ) : knows t"
  shows "False"
using facts proof(sources! " Hash ( LN ''ni'' tid0 ) ")
  case fake note_unified facts = this facts
  thus ?thesis by (fastforce dest: I_ni_secrecy intro: event_predOrdI)
next
  case (I_3_hash tid1) note_unified facts = this facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT2'', Hash ( LN ''ni'' tid1 ), LN ''ni'' tid0,
                          s(AV ''R'' tid1), s(MV ''kir'' tid1)
                       |}
                       ( PK ( s(AV ''I'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest: I_ni_secrecy intro: event_predOrdI)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
next
  case (R_2_hash tid1) note_unified facts = this facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', LN ''ni'' tid0, s(MV ''I'' tid1) |}
                       ( PK ( s(AV ''R'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest: I_ni_secrecy intro: event_predOrdI)
  next
    case (I_1_enc tid2) note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

lemma (in restricted_BKE_state) R_hash_nr_secrecy:
  assumes facts:
    "roleMap r tid0 = Some R"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "RLKR(s(MV ''I'' tid0)) ~: reveals t"
    "Hash ( LN ''nr'' tid0 ) : knows t"
  shows "False"
using facts proof(sources! " Hash ( LN ''nr'' tid0 ) ")
  case fake note_unified facts = this facts
  thus ?thesis by (fastforce dest: R_nr_secrecy intro: event_predOrdI)
next
  case (I_3_hash tid1) note_unified facts = this facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT2'', Hash ( LN ''ni'' tid1 ), LN ''nr'' tid0,
                          s(AV ''R'' tid1), s(MV ''kir'' tid1)
                       |}
                       ( PK ( s(AV ''I'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest: R_nr_secrecy intro: event_predOrdI)
  next
    case (R_2_enc tid2) note_unified facts = this facts
    thus ?thesis by (fastforce dest: R_kir_secrecy intro: event_predOrdI)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
next
  case (R_2_hash tid1) note_unified facts = this facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', LN ''nr'' tid0, s(MV ''I'' tid1) |}
                       ( PK ( s(AV ''R'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest: R_nr_secrecy intro: event_predOrdI)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

lemma (in restricted_BKE_state) I_nr_secrecy:
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
                   Enc {| LC ''TT2'', Hash ( LN ''ni'' tid0 ), s(MV ''nr'' tid0),
                          s(AV ''R'' tid0), s(MV ''kir'' tid0)
                       |}
                       ( PK ( s(AV ''I'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest: I_hash_ni_secrecy intro: event_predOrdI)
  next
    case (R_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: R_nr_secrecy intro: event_predOrdI)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_BKE_state) I_kir_secrecy:
  assumes facts:
    "roleMap r tid0 = Some I"
    "RLKR(s(AV ''I'' tid0)) ~: reveals t"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "( tid0, I_2 ) : steps t"
    "s(MV ''kir'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT2'', Hash ( LN ''ni'' tid0 ), s(MV ''nr'' tid0),
                          s(AV ''R'' tid0), s(MV ''kir'' tid0)
                       |}
                       ( PK ( s(AV ''I'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest: I_hash_ni_secrecy intro: event_predOrdI)
  next
    case (R_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: R_kir_secrecy intro: event_predOrdI)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_BKE_state) R_ni_secrecy:
  assumes facts:
    "roleMap r tid0 = Some R"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "RLKR(s(MV ''I'' tid0)) ~: reveals t"
    "( tid0, R_3 ) : steps t"
    "s(MV ''ni'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT3'', Hash ( LN ''nr'' tid0 ) |} ( LN ''kir'' tid0 ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest: R_kir_secrecy intro: event_predOrdI)
  next
    case (I_3_enc tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', Hash ( LN ''ni'' tid1 ), LN ''nr'' tid0,
                            s(AV ''R'' tid1), LN ''kir'' tid0
                         |}
                         ( PK ( s(AV ''I'' tid1) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastforce dest: R_nr_secrecy intro: event_predOrdI)
    next
      case (R_2_enc tid2) note_unified facts = this facts
      thus ?thesis by (fastforce dest: I_ni_secrecy intro: event_predOrdI)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

(* subsection:  Authentication Properties  *)

lemma (in restricted_BKE_state) I_ni_synch:
  assumes facts:
    "roleMap r tid1 = Some I"
    "RLKR(s(AV ''I'' tid1)) ~: reveals t"
    "RLKR(s(AV ''R'' tid1)) ~: reveals t"
    "( tid1, I_3 ) : steps t"
  shows
    "(?  tid2.
        roleMap r tid2 = Some R &
        s(AV ''I'' tid1) = s(MV ''I'' tid2) &
        s(AV ''R'' tid1) = s(AV ''R'' tid2) &
        LN ''ni'' tid1 = s(MV ''ni'' tid2) &
        s(MV ''nr'' tid1) = LN ''nr'' tid2 &
        s(MV ''kir'' tid1) = LN ''kir'' tid2 &
        predOrd t (St( tid1, I_1 )) (St( tid2, R_1 )) &
        predOrd t (St( tid2, R_1 )) (St( tid2, R_2 )) &
        predOrd t (St( tid2, R_2 )) (St( tid1, I_2 )) &
        predOrd t (St( tid1, I_2 )) (St( tid1, I_3 )))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT2'', Hash ( LN ''ni'' tid1 ), s(MV ''nr'' tid1),
                          s(AV ''R'' tid1), s(MV ''kir'' tid1)
                       |}
                       ( PK ( s(AV ''I'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest: I_hash_ni_secrecy intro: event_predOrdI)
  next
    case (R_2_enc tid2) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', LN ''ni'' tid1, s(AV ''I'' tid1) |}
                         ( PK ( s(AV ''R'' tid1) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastforce dest: I_ni_secrecy intro: event_predOrdI)
    next
      case (I_1_enc tid3) note_unified facts = this facts
      thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_BKE_state) R_ni_synch:
  assumes facts:
    "roleMap r tid1 = Some R"
    "RLKR(s(AV ''R'' tid1)) ~: reveals t"
    "RLKR(s(MV ''I'' tid1)) ~: reveals t"
    "( tid1, R_3 ) : steps t"
  shows
    "(?  tid2.
        roleMap r tid2 = Some I &
        s(MV ''I'' tid1) = s(AV ''I'' tid2) &
        s(AV ''R'' tid1) = s(AV ''R'' tid2) &
        s(MV ''ni'' tid1) = LN ''ni'' tid2 &
        LN ''nr'' tid1 = s(MV ''nr'' tid2) &
        LN ''kir'' tid1 = s(MV ''kir'' tid2) &
        predOrd t (St( tid2, I_1 )) (St( tid1, R_1 )) &
        predOrd t (St( tid1, R_1 )) (St( tid1, R_2 )) &
        predOrd t (St( tid1, R_2 )) (St( tid2, I_2 )) &
        predOrd t (St( tid2, I_2 )) (St( tid2, I_3 )) &
        predOrd t (St( tid2, I_3 )) (St( tid1, R_3 )))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(MV ''ni'' tid1), s(MV ''I'' tid1) |}
                       ( PK ( s(AV ''R'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest: R_ni_secrecy intro: event_predOrdI)
  next
    case (I_1_enc tid2) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT3'', Hash ( LN ''nr'' tid1 ) |} ( LN ''kir'' tid1 ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastforce dest: R_kir_secrecy intro: event_predOrdI)
    next
      case (I_3_enc tid3) note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT2'', Hash ( LN ''ni'' tid3 ), LN ''nr'' tid1,
                              s(AV ''R'' tid3), LN ''kir'' tid1
                           |}
                           ( PK ( s(AV ''I'' tid3) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastforce dest: R_nr_secrecy intro: event_predOrdI)
      next
        case (R_2_enc tid4) note_unified facts = this facts
        thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

end