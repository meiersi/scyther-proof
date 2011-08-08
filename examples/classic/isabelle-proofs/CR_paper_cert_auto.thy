theory "CR_paper_cert_auto"
imports
  "../ESPLogic"
begin

(* section:  The Running Example of Our CSF'10 Paper  *)

role C
where "C =
  [ Send ''1'' ( PEnc ( sN ''k'' ) ( sPK ''S'' ) )
  , Recv ''2'' ( PHash ( sN ''k'' ) )
  ]"

role S
where "S =
  [ Recv ''1'' ( PEnc ( sMV ''k'' ) ( sPK ''S'' ) )
  , Send ''2'' ( PHash ( sMV ''k'' ) )
  ]"

protocol CR
where "CR = { C, S }"

locale restricted_CR_state = CR_state

type_invariant CR_msc_typing for CR
where "CR_msc_typing = mk_typing
  [ ((S, ''k''), (SumT (KnownT S_1) (NonceT C ''k'')))
  ]"

sublocale CR_state < CR_msc_typing_state
proof -
  have "(t,r,s) : approx CR_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF CR_msc_typing.monoTyp, completeness_cases_rule])
    case (S_1_k t r s tid0) note facts = this
    then interpret state: CR_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! " Enc ( s(MV ''k'' tid0) ) ( PK ( s(AV ''S'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  qed
  thus "CR_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context CR_state begin

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

lemma (in restricted_CR_state) C_k_secrecy:
  assumes facts:
    "roleMap r tid0 = Some C"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "LN ''k'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''k'' tid0 ")
  case C_1_k note_unified facts = this facts
  thus ?thesis by (fastsimp dest!: ltk_secrecy)
qed (insert facts, fastsimp+)?

(* subsection:  Authentication Properties  *)

lemma (in restricted_CR_state) C_ni_synch:
  assumes facts:
    "roleMap r tid1 = Some C"
    "RLKR(s(AV ''S'' tid1)) ~: reveals t"
    "( tid1, C_2 ) : steps t"
  shows
    "(?  tid2.
        roleMap r tid2 = Some S &
        s(AV ''S'' tid1) = s(AV ''S'' tid2) &
        LN ''k'' tid1 = s(MV ''k'' tid2) &
        predOrd t (St( tid1, C_1 )) (St( tid2, S_1 )) &
        predOrd t (St( tid2, S_1 )) (St( tid2, S_2 )) &
        predOrd t (St( tid2, S_2 )) (St( tid1, C_2 )))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! " Hash ( LN ''k'' tid1 ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest: C_k_secrecy intro: event_predOrdI)
  next
    case (S_2_hash tid2) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc ( LN ''k'' tid1 ) ( PK ( s(AV ''S'' tid2) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest: C_k_secrecy intro: event_predOrdI)
    next
      case (C_1_enc tid3) note_unified facts = this facts
      thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
    qed (insert facts, fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

end