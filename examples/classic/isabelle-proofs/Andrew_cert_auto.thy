theory "Andrew_cert_auto"
imports
  "../ESPLogic"
begin

(* section:  Andrew Secure RPC  *)

(* text: 
  We do not have the original model of the Isabelle/OFMC AndrewRPC protocol.
  Therefore, we orient ourself on the SPORE library model.

  Notable differences:

    1. Instead of implicit typing, we are using explicit global constants to
       discern messages.
 *)

role I
where "I =
  [ Send ''1'' <| sAV ''I'',
                  PEnc <| sC ''TT1'', sN ''ni'' |> ( sK ''I'' ''R'' )
               |>
  , Recv ''2'' ( PEnc <| sC ''TT2'', PHash <| sC ''TT1'', sN ''ni'' |>,
                         sMV ''nr''
                      |>
                      ( sK ''I'' ''R'' )
               )
  , Send ''3'' ( PEnc <| sC ''TT3'', PHash <| sC ''TT1'', sMV ''nr'' |> |>
                      ( sK ''I'' ''R'' )
               )
  , Recv ''4'' ( PEnc <| sC ''TT4'', sMV ''kIR'', sMV ''nr2'' |>
                      ( sK ''I'' ''R'' )
               )
  ]"

role R
where "R =
  [ Recv ''1'' <| sMV ''I'',
                  PEnc <| sC ''TT1'', sMV ''ni'' |> ( PSymK ( sMV ''I'' ) ( sAV ''R'' ) )
               |>
  , Send ''2'' ( PEnc <| sC ''TT2'', PHash <| sC ''TT1'', sMV ''ni'' |>,
                         sN ''nr''
                      |>
                      ( PSymK ( sMV ''I'' ) ( sAV ''R'' ) )
               )
  , Recv ''3'' ( PEnc <| sC ''TT3'', PHash <| sC ''TT1'', sN ''nr'' |> |>
                      ( PSymK ( sMV ''I'' ) ( sAV ''R'' ) )
               )
  , Send ''4'' ( PEnc <| sC ''TT4'', sN ''kIR'', sN ''nr2'' |>
                      ( PSymK ( sMV ''I'' ) ( sAV ''R'' ) )
               )
  ]"

protocol Andrew
where "Andrew = { I, R }"

locale restricted_Andrew_state = Andrew_state

type_invariant Andrew_msc_typing for Andrew
where "Andrew_msc_typing = mk_typing
  [ ((R, ''I''), (KnownT R_1))
  , ((I, ''kIR''), (SumT (KnownT I_4) (NonceT R ''kIR'')))
  , ((R, ''ni''), (SumT (KnownT R_1) (NonceT I ''ni'')))
  , ((I, ''nr''), (SumT (KnownT I_2) (NonceT R ''nr'')))
  , ((I, ''nr2''), (SumT (KnownT I_4) (NonceT R ''nr2'')))
  ]"

sublocale Andrew_state < Andrew_msc_typing_state
proof -
  have "(t,r,s) : approx Andrew_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF Andrew_msc_typing.monoTyp, completeness_cases_rule])
    case (I_2_nr t r s tid0) note facts = this
    then interpret state: Andrew_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''TT2'', Hash {| LC ''TT1'', LN ''ni'' tid0 |},
               s(MV ''nr'' tid0)
            |}
            ( K ( s(AV ''I'' tid0) ) ( s(AV ''R'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (I_4_kIR t r s tid0) note facts = this
    then interpret state: Andrew_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''TT4'', s(MV ''kIR'' tid0), s(MV ''nr2'' tid0) |}
            ( K ( s(AV ''I'' tid0) ) ( s(AV ''R'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (I_4_nr2 t r s tid0) note facts = this
    then interpret state: Andrew_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''TT4'', s(MV ''kIR'' tid0), s(MV ''nr2'' tid0) |}
            ( K ( s(AV ''I'' tid0) ) ( s(AV ''R'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (R_1_I t r s tid0) note facts = this
    then interpret state: Andrew_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (R_1_ni t r s tid0) note facts = this
    then interpret state: Andrew_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''TT1'', s(MV ''ni'' tid0) |}
            ( K ( s(MV ''I'' tid0) ) ( s(AV ''R'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  qed
  thus "Andrew_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context Andrew_state begin

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

lemma (in restricted_Andrew_state) R_sec_kIR:
  assumes facts:
    "roleMap r tid0 = Some R"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "RLKR(s(MV ''I'' tid0)) ~: reveals t"
    "LN ''kIR'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''kIR'' tid0 ")
  case R_4_kIR note_unified facts = this facts
  thus ?thesis by (fastsimp dest!: ltk_secrecy)
qed (insert facts, fastsimp+)?

lemma (in restricted_Andrew_state) I_sec_kIR:
  assumes facts:
    "roleMap r tid0 = Some I"
    "RLKR(s(AV ''I'' tid0)) ~: reveals t"
    "RLKR(s(AV ''R'' tid0)) ~: reveals t"
    "( tid0, I_4 ) : steps t"
    "s(MV ''kIR'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT4'', s(MV ''kIR'' tid0), s(MV ''nr2'' tid0) |}
                       ( K ( s(AV ''I'' tid0) ) ( s(AV ''R'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (R_4_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp dest: R_sec_kIR intro: event_predOrdI)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_Andrew_state) I_ni_agree:
  assumes facts:
    "roleMap r tid1 = Some I"
    "RLKR(s(AV ''I'' tid1)) ~: reveals t"
    "RLKR(s(AV ''R'' tid1)) ~: reveals t"
    "( tid1, I_4 ) : steps t"
  shows
    "(?  tid2.
        roleMap r tid2 = Some R &
        s(AV ''I'' tid1) = s(MV ''I'' tid2) &
        s(AV ''R'' tid1) = s(AV ''R'' tid2) &
        s(MV ''nr2'' tid1) = LN ''nr2'' tid2 &
        s(MV ''kIR'' tid1) = LN ''kIR'' tid2)"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT4'', s(MV ''kIR'' tid1), s(MV ''nr2'' tid1) |}
                       ( K ( s(AV ''I'' tid1) ) ( s(AV ''R'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (R_4_enc tid2) note_unified facts = this facts
    thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_Andrew_state) R_ni_agree:
  assumes facts:
    "roleMap r tid1 = Some R"
    "RLKR(s(AV ''R'' tid1)) ~: reveals t"
    "RLKR(s(MV ''I'' tid1)) ~: reveals t"
    "( tid1, R_4 ) : steps t"
  shows
    "(?  tid2.
        roleMap r tid2 = Some I &
        s(MV ''I'' tid1) = s(AV ''I'' tid2) &
        s(AV ''R'' tid1) = s(AV ''R'' tid2) &
        s(MV ''ni'' tid1) = LN ''ni'' tid2 & LN ''nr'' tid1 = s(MV ''nr'' tid2))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT3'', Hash {| LC ''TT1'', LN ''nr'' tid1 |} |}
                       ( K ( s(MV ''I'' tid1) ) ( s(AV ''R'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (I_3_enc tid2) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT2'', Hash {| LC ''TT1'', LN ''ni'' tid2 |}, LN ''nr'' tid1
                         |}
                         ( K ( s(AV ''I'' tid2) ) ( s(AV ''R'' tid1) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest!: ltk_secrecy)
    next
      case (R_2_enc tid3) note_unified facts = this facts
      thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
    qed (insert facts, fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

end