theory "Paulson_strengthened_Yahalom_cert_auto"
imports
  "../ESPLogic"
begin

(* section:  Yahalom strengthened by Paulson  *)

(* text: 
  Modeled after the model in the SPORE library.

  Notable differences:

    1. Instead of implicit typing, we are using explicit global constants to
       discern messages.

    2. The third message includes the identity of S in plaintext, as it is
       required by role A to lookup the corresponding shared key.

    3. We model longterm shared keys such that k[A,B] = k[B,A]. This extension
       is described in "Provably Repairing the ISO/IEC 9798 Standard for Entity
       Authentication" by Basin, Cremers, and Meier
       (http://people.inf.ethz.ch/cremersc/downloads/download.php?file=papers/BCM2011-iso9798.pdf)

 *)

role A
where "A =
  [ Send ''1'' <| sAV ''A'', sN ''Na'' |>
  , Recv ''3'' <| sMV ''S'', sMV ''Nb'',
                  PEnc <| sC ''3_1'', sMV ''B'', sMV ''Kab'', sN ''Na'' |>
                       ( sKbd (AVar ''A'') (MVar ''S'') ),
                  sMV ''TicketB''
               |>
  , Send ''4'' <| sMV ''TicketB'',
                  PEnc <| sC ''4'', sMV ''Nb'' |> ( sMV ''Kab'' )
               |>
  ]"

role B
where "B =
  [ Recv ''1'' <| sMV ''A'', sMV ''Na'' |>
  , Send ''2'' <| sAV ''B'', sN ''Nb'',
                  PEnc <| sC ''2'', sMV ''A'', sMV ''Na'' |>
                       ( sKbd (AVar ''B'') (AVar ''S'') )
               |>
  , Recv ''4'' <| PEnc <| sC ''3_2'', sMV ''A'', sAV ''B'', sMV ''Kab'',
                          sN ''Nb''
                       |>
                       ( sKbd (AVar ''B'') (AVar ''S'') ),
                  PEnc <| sC ''4'', sN ''Nb'' |> ( sMV ''Kab'' )
               |>
  ]"

role S
where "S =
  [ Recv ''2'' <| sMV ''B'', sMV ''Nb'',
                  PEnc <| sC ''2'', sMV ''A'', sMV ''Na'' |>
                       ( sKbd (MVar ''B'') (AVar ''S'') )
               |>
  , Send ''3'' <| sAV ''S'', sMV ''Nb'',
                  PEnc <| sC ''3_1'', sMV ''B'', sN ''Kab'', sMV ''Na'' |>
                       ( sKbd (MVar ''A'') (AVar ''S'') ),
                  PEnc <| sC ''3_2'', sMV ''A'', sMV ''B'', sN ''Kab'', sMV ''Nb'' |>
                       ( sKbd (MVar ''B'') (AVar ''S'') )
               |>
  ]"

protocol Yahalom
where "Yahalom = { A, B, S }"

locale restricted_Yahalom_state = Yahalom_state +
  assumes different_actors_A_S:
    "!! tid0 tid1.
       [| roleMap r tid0 = Some A; roleMap r tid1 = Some S;
         s(AV ''S'' tid1) = s(AV ''A'' tid0)
       |] ==> False"
  assumes different_actors_B_S:
    "!! tid0 tid1.
       [| roleMap r tid0 = Some B; roleMap r tid1 = Some S;
         s(AV ''S'' tid1) = s(AV ''B'' tid0)
       |] ==> False"

type_invariant Yahalom_msc_typing for Yahalom
where "Yahalom_msc_typing = mk_typing
  [ ((B, ''A''), (KnownT B_1))
  , ((S, ''A''), (SumT (KnownT S_2) AgentT))
  , ((A, ''B''), (SumT (KnownT A_3) AgentT))
  , ((S, ''B''), (KnownT S_2))
  , ((A, ''Kab''), (SumT (KnownT A_3) (NonceT S ''Kab'')))
  , ((B, ''Kab''), (SumT (KnownT B_4) (NonceT S ''Kab'')))
  , ((B, ''Na''), (KnownT B_1))
  , ((S, ''Na''), (SumT (KnownT S_2) (NonceT A ''Na'')))
  , ((A, ''Nb''), (KnownT A_3))
  , ((S, ''Nb''), (KnownT S_2))
  , ((A, ''S''), (KnownT A_3))
  , ((A, ''TicketB''), (KnownT A_3))
  ]"

sublocale Yahalom_state < Yahalom_msc_typing_state
proof -
  have "(t,r,s) : approx Yahalom_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF Yahalom_msc_typing.monoTyp, completeness_cases_rule])
    case (A_3_B t r s tid0) note facts = this
    then interpret state: Yahalom_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''3_1'', s(MV ''B'' tid0), s(MV ''Kab'' tid0), LN ''Na'' tid0
            |}
            ( Kbd ( s(AV ''A'' tid0) ) ( s(MV ''S'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (A_3_Kab t r s tid0) note facts = this
    then interpret state: Yahalom_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''3_1'', s(MV ''B'' tid0), s(MV ''Kab'' tid0), LN ''Na'' tid0
            |}
            ( Kbd ( s(AV ''A'' tid0) ) ( s(MV ''S'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (A_3_Nb t r s tid0) note facts = this
    then interpret state: Yahalom_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (A_3_S t r s tid0) note facts = this
    then interpret state: Yahalom_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (A_3_TicketB t r s tid0) note facts = this
    then interpret state: Yahalom_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (B_1_A t r s tid0) note facts = this
    then interpret state: Yahalom_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (B_1_Na t r s tid0) note facts = this
    then interpret state: Yahalom_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (B_4_Kab t r s tid0) note facts = this
    then interpret state: Yahalom_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''3_2'', s(MV ''A'' tid0), s(AV ''B'' tid0),
               s(MV ''Kab'' tid0), LN ''Nb'' tid0
            |}
            ( Kbd ( s(AV ''B'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (S_2_A t r s tid0) note facts = this
    then interpret state: Yahalom_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''2'', s(MV ''A'' tid0), s(MV ''Na'' tid0) |}
            ( Kbd ( s(AV ''S'' tid0) ) ( s(MV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (S_2_B t r s tid0) note facts = this
    then interpret state: Yahalom_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (S_2_Na t r s tid0) note facts = this
    then interpret state: Yahalom_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''2'', s(MV ''A'' tid0), s(MV ''Na'' tid0) |}
            ( Kbd ( s(AV ''S'' tid0) ) ( s(MV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (S_2_Nb t r s tid0) note facts = this
    then interpret state: Yahalom_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  qed
  thus "Yahalom_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context Yahalom_state begin

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

lemma (in restricted_Yahalom_state) S_Kab_secret:
  assumes facts:
    "roleMap r tid0 = Some S"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "LN ''Kab'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''Kab'' tid0 ")
  case S_3_Kab note_unified facts = this facts
  thus ?thesis by (fastsimp dest!: ltk_secrecy)
next
  case S_3_Kab_1 note_unified facts = this facts
  thus ?thesis by (fastsimp dest!: ltk_secrecy)
qed (insert facts, fastsimp+)?

lemma (in restricted_Yahalom_state) A_Kab_secret:
  assumes facts:
    "roleMap r tid0 = Some A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''S'' tid0)) ~: reveals t"
    "( tid0, A_3 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''3_1'', s(MV ''B'' tid0), s(MV ''Kab'' tid0), LN ''Na'' tid0
                       |}
                       ( Kbd ( s(AV ''A'' tid0) ) ( s(MV ''S'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (S_3_enc tid1) note_unified facts = this facts
    hence "Kbd ( s(AV ''S'' tid1) )
               ( s(MV ''A'' tid1) ) = Kbd ( s(AV ''A'' tid0) ) ( s(MV ''S'' tid0) )"
      by simp note facts = this facts
    thus ?thesis proof(cases rule: Kbd_cases)
      case noswap note_unified facts = this facts
      thus ?thesis by (fastsimp dest: S_Kab_secret intro: event_predOrdI)
    next
      case swapped note_unified facts = this facts
      thus ?thesis by (fastsimp dest: S_Kab_secret intro: event_predOrdI)
    qed (fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_Yahalom_state) B_Kab_secret:
  assumes facts:
    "roleMap r tid0 = Some B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "( tid0, B_4 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''3_2'', s(MV ''A'' tid0), s(AV ''B'' tid0),
                          s(MV ''Kab'' tid0), LN ''Nb'' tid0
                       |}
                       ( Kbd ( s(AV ''B'' tid0) ) ( s(AV ''S'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (S_3_enc_1 tid1) note_unified facts = this facts
    hence "Kbd ( s(AV ''B'' tid0) )
               ( s(AV ''S'' tid1) ) = Kbd ( s(AV ''B'' tid0) ) ( s(AV ''S'' tid0) )"
      by simp note facts = this facts
    thus ?thesis proof(cases rule: Kbd_cases)
      case noswap note_unified facts = this facts
      thus ?thesis by (fastsimp dest: S_Kab_secret intro: event_predOrdI)
    next
      case swapped note_unified facts = this facts
      thus ?thesis by (fastsimp dest: S_Kab_secret intro: event_predOrdI)
    qed (fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

(* subsection:  Authentication Properties  *)

(* text:  This is what Paulson proves.  *)

lemma (in restricted_Yahalom_state) B_auth:
  assumes facts:
    "roleMap r tid2 = Some B"
    "RLKR(s(AV ''B'' tid2)) ~: reveals t"
    "RLKR(s(AV ''S'' tid2)) ~: reveals t"
    "RLKR(s(MV ''A'' tid2)) ~: reveals t"
    "( tid2, B_4 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some A &
        s(MV ''B'' tid1) = s(AV ''B'' tid2) &
        s(MV ''Kab'' tid1) = s(MV ''Kab'' tid2))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''4'', LN ''Nb'' tid2 |} ( s(MV ''Kab'' tid2) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest: B_Kab_secret intro: event_predOrdI)
  next
    case (A_4_enc tid3) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''3_2'', s(MV ''A'' tid2), s(AV ''B'' tid2),
                            s(MV ''Kab'' tid2), LN ''Nb'' tid2
                         |}
                         ( Kbd ( s(AV ''B'' tid2) ) ( s(AV ''S'' tid2) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest!: ltk_secrecy)
    next
      case (S_3_enc_1 tid4) note_unified facts = this facts
      hence "Kbd ( s(AV ''B'' tid2) )
                 ( s(AV ''S'' tid4) ) = Kbd ( s(AV ''B'' tid2) ) ( s(AV ''S'' tid2) )"
        by simp note facts = this facts
      thus ?thesis proof(cases rule: Kbd_cases)
        case noswap note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''3_1'', s(MV ''B'' tid3), LN ''Kab'' tid4, LN ''Na'' tid3 |}
                             ( Kbd ( s(AV ''A'' tid3) ) ( s(MV ''S'' tid3) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastsimp dest: S_Kab_secret intro: event_predOrdI)
        next
          case (S_3_enc tid5) note_unified facts = this facts
          thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
        qed (insert facts, fastsimp+)?
      next
        case swapped note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''3_1'', s(MV ''B'' tid3), LN ''Kab'' tid4, LN ''Na'' tid3 |}
                             ( Kbd ( s(AV ''A'' tid3) ) ( s(MV ''S'' tid3) ) ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastsimp dest: S_Kab_secret intro: event_predOrdI)
        next
          case (S_3_enc tid5) note_unified facts = this facts
          thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
        qed (insert facts, fastsimp+)?
      qed (fastsimp+)?
    qed (insert facts, fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

(* subsection:  Stonger Authentication Properties  *)

(* text: 
We can prove stronger authentication properties. However, they hold only under
the additional assumption that agents running the trusted third party do not
participate in the A or B role of the protocol. This is a reasonable assumption.

Without this assumption, the problem is that due to the swapping of identities
on the keys, the authentication properties below can be attacked. Note that the
proofs list exactly the reasoning steps where the axioms are exploited.
 *)



lemma (in restricted_Yahalom_state) A_strong_auth:
  assumes facts:
    "roleMap r tid1 = Some A"
    "RLKR(s(AV ''A'' tid1)) ~: reveals t"
    "RLKR(s(MV ''B'' tid1)) ~: reveals t"
    "RLKR(s(MV ''S'' tid1)) ~: reveals t"
    "( tid1, A_3 ) : steps t"
  shows
    "(?  tid2.
        (?  tid3.
           roleMap r tid2 = Some B &
           roleMap r tid3 = Some S &
           s(AV ''A'' tid1) = s(MV ''A'' tid2) &
           s(MV ''A'' tid2) = s(MV ''A'' tid3) &
           s(MV ''B'' tid1) = s(AV ''B'' tid2) &
           s(AV ''B'' tid2) = s(MV ''B'' tid3) &
           s(MV ''S'' tid1) = s(AV ''S'' tid2) &
           s(AV ''S'' tid2) = s(AV ''S'' tid3) &
           LN ''Na'' tid1 = s(MV ''Na'' tid2) &
           s(MV ''Na'' tid2) = s(MV ''Na'' tid3) &
           s(MV ''Kab'' tid1) = LN ''Kab'' tid3 &
           predOrd t (St( tid1, A_1 )) (St( tid2, B_1 )) &
           predOrd t (St( tid2, B_1 )) (St( tid2, B_2 )) &
           predOrd t (St( tid2, B_2 )) (St( tid3, S_2 )) &
           predOrd t (St( tid3, S_2 )) (St( tid3, S_3 )) &
           predOrd t (St( tid3, S_3 )) (St( tid1, A_3 ))))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''3_1'', s(MV ''B'' tid1), s(MV ''Kab'' tid1), LN ''Na'' tid1
                       |}
                       ( Kbd ( s(AV ''A'' tid1) ) ( s(MV ''S'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (S_3_enc tid2) note_unified facts = this facts
    hence "Kbd ( s(AV ''S'' tid2) )
               ( s(MV ''A'' tid2) ) = Kbd ( s(AV ''A'' tid1) ) ( s(MV ''S'' tid1) )"
      by simp note facts = this facts
    thus ?thesis proof(cases rule: Kbd_cases)
      case noswap note_unified facts = this facts
      thus ?thesis by (fastsimp dest: different_actors_A_S intro: event_predOrdI)
    next
      case swapped note_unified facts = this facts
      thus ?thesis proof(sources! "
                       Enc {| LC ''2'', s(AV ''A'' tid1), LN ''Na'' tid1 |}
                           ( Kbd ( s(AV ''S'' tid2) ) ( s(MV ''B'' tid1) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (fastsimp dest!: ltk_secrecy)
      next
        case (B_2_enc tid3) note_unified facts = this facts
        hence "Kbd ( s(AV ''S'' tid2) )
                   ( s(MV ''B'' tid1) ) = Kbd ( s(AV ''B'' tid3) ) ( s(AV ''S'' tid3) )"
          by simp note facts = this facts
        thus ?thesis proof(cases rule: Kbd_cases)
          case noswap note_unified facts = this facts
          thus ?thesis by (fastsimp dest: different_actors_B_S intro: event_predOrdI)
        next
          case swapped note_unified facts = this facts
          thus ?thesis proof(sources! " LN ''Na'' tid1 ")
            case A_1_Na note_unified facts = this facts
            thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
          next
            case (S_3_Na tid4) note_unified facts = this facts
            thus ?thesis proof(sources! "
                             Enc {| LC ''2'', s(MV ''A'' tid4), LN ''Na'' tid1 |}
                                 ( Kbd ( s(AV ''S'' tid4) ) ( s(MV ''B'' tid4) ) ) ")
            qed (insert facts, (((clarsimp, order?) | order))+)?
          qed (insert facts, fastsimp+)?
        qed (fastsimp+)?
      qed (insert facts, fastsimp+)?
    qed (fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_Yahalom_state) B_strong_auth:
  assumes facts:
    "roleMap r tid2 = Some B"
    "RLKR(s(AV ''B'' tid2)) ~: reveals t"
    "RLKR(s(AV ''S'' tid2)) ~: reveals t"
    "RLKR(s(MV ''A'' tid2)) ~: reveals t"
    "( tid2, B_4 ) : steps t"
  shows
    "(?  tid1.
        (?  tid3.
           roleMap r tid1 = Some A &
           roleMap r tid3 = Some S &
           s(AV ''A'' tid1) = s(MV ''A'' tid2) &
           s(MV ''A'' tid2) = s(MV ''A'' tid3) &
           s(MV ''B'' tid1) = s(AV ''B'' tid2) &
           s(AV ''B'' tid2) = s(MV ''B'' tid3) &
           s(MV ''S'' tid1) = s(AV ''S'' tid2) &
           s(AV ''S'' tid2) = s(AV ''S'' tid3) &
           s(MV ''Nb'' tid1) = LN ''Nb'' tid2 &
           LN ''Nb'' tid2 = s(MV ''Nb'' tid3) &
           s(MV ''Kab'' tid1) = s(MV ''Kab'' tid2) &
           s(MV ''Kab'' tid2) = LN ''Kab'' tid3 &
           predOrd t (St( tid2, B_1 )) (St( tid2, B_2 )) &
           predOrd t (St( tid2, B_2 )) (St( tid3, S_2 )) &
           predOrd t (St( tid3, S_2 )) (St( tid3, S_3 )) &
           predOrd t (St( tid3, S_3 )) (St( tid1, A_3 )) &
           predOrd t (St( tid1, A_3 )) (St( tid1, A_4 )) &
           predOrd t (St( tid1, A_4 )) (St( tid2, B_4 ))))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''3_2'', s(MV ''A'' tid2), s(AV ''B'' tid2),
                          s(MV ''Kab'' tid2), LN ''Nb'' tid2
                       |}
                       ( Kbd ( s(AV ''B'' tid2) ) ( s(AV ''S'' tid2) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (S_3_enc_1 tid3) note_unified facts = this facts
    hence "Kbd ( s(AV ''B'' tid2) )
               ( s(AV ''S'' tid3) ) = Kbd ( s(AV ''B'' tid2) ) ( s(AV ''S'' tid2) )"
      by simp note facts = this facts
    thus ?thesis proof(cases rule: Kbd_cases)
      case noswap note_unified facts = this facts
      thus ?thesis proof(sources! " LN ''Nb'' tid2 ")
        case B_2_Nb note_unified facts = this facts
        thus ?thesis proof(sources! "
                         Enc {| LC ''4'', LN ''Nb'' tid2 |} ( LN ''Kab'' tid3 ) ")
          case fake note_unified facts = this facts
          thus ?thesis by (fastsimp dest: S_Kab_secret intro: event_predOrdI)
        next
          case (A_4_enc tid4) note_unified facts = this facts
          thus ?thesis proof(sources! "
                           Enc {| LC ''3_1'', s(MV ''B'' tid4), LN ''Kab'' tid3, LN ''Na'' tid4 |}
                               ( Kbd ( s(AV ''A'' tid4) ) ( s(MV ''S'' tid4) ) ) ")
            case fake note_unified facts = this facts
            thus ?thesis by (fastsimp dest: S_Kab_secret intro: event_predOrdI)
          next
            case (S_3_enc tid5) note_unified facts = this facts
            hence "Kbd ( s(AV ''S'' tid2) )
                       ( s(MV ''A'' tid2) ) = Kbd ( s(AV ''A'' tid4) ) ( s(MV ''S'' tid4) )"
              by simp note facts = this facts
            thus ?thesis proof(cases rule: Kbd_cases)
              case noswap note_unified facts = this facts
              thus ?thesis by (fastsimp dest: different_actors_A_S intro: event_predOrdI)
            next
              case swapped note_unified facts = this facts
              thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
            qed (fastsimp+)?
          qed (insert facts, fastsimp+)?
        qed (insert facts, fastsimp+)?
      qed (insert facts, fastsimp+)?
    next
      case swapped note_unified facts = this facts
      thus ?thesis by (fastsimp dest: different_actors_B_S intro: event_predOrdI)
    qed (fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

end