theory "Andrew_Secure_RPC_cert_auto"
imports
  "../ESPLogic"
begin

(* section:  Andrew Secure RPC  *)

(* text: 
  Modeled after the model in the SPORE library.

  Notable differences:

    1. 'succ(x)' is invertible. Hence, we just model it as a tuple ('succ',x) of
       a global constant 'succ' and the variable x.  This means that we only
       exploit the tagging properties of 'succ', but do not assume any
       information hiding.

    2. Instead of implicit typing, we are using explicit global constants to
       discern messages.

  Note that when using a bidirectional key k[A,B] instead of the
  uni-directional key k(A,B) that is different depending on the used direction
  an attack becomes possible, as agreement on the agent identities is partially
  lost. Adding the A identity in the first message fixes that flaw.
 *)

role A
where "A =
  [ Send ''1'' <| sAV ''A'',
                  PEnc <| sC ''1'', sN ''Na'' |> ( sK ''A'' ''B'' )
               |>
  , Recv ''2'' ( PEnc <| sC ''2'', <| sC ''succ'', sN ''Na'' |>, sMV ''Nb''
                      |>
                      ( sK ''A'' ''B'' )
               )
  , Send ''3'' ( PEnc <| sC ''3'', sC ''succ'', sMV ''Nb'' |>
                      ( sK ''A'' ''B'' )
               )
  , Recv ''4'' ( PEnc <| sC ''4'', sMV ''Kab'', sMV ''Nbp'' |>
                      ( sK ''A'' ''B'' )
               )
  ]"

role B
where "B =
  [ Recv ''1'' <| sMV ''A'',
                  PEnc <| sC ''1'', sMV ''Na'' |> ( PSymK ( sMV ''A'' ) ( sAV ''B'' ) )
               |>
  , Send ''2'' ( PEnc <| sC ''2'', <| sC ''succ'', sMV ''Na'' |>, sN ''Nb''
                      |>
                      ( PSymK ( sMV ''A'' ) ( sAV ''B'' ) )
               )
  , Recv ''3'' ( PEnc <| sC ''3'', sC ''succ'', sN ''Nb'' |>
                      ( PSymK ( sMV ''A'' ) ( sAV ''B'' ) )
               )
  , Send ''4'' ( PEnc <| sC ''4'', sN ''Kab'', sN ''Nbp'' |>
                      ( PSymK ( sMV ''A'' ) ( sAV ''B'' ) )
               )
  ]"

protocol Andrew
where "Andrew = { A, B }"

locale restricted_Andrew_state = Andrew_state

type_invariant Andrew_msc_typing for Andrew
where "Andrew_msc_typing = mk_typing
  [ ((B, ''A''), (KnownT B_1))
  , ((A, ''Kab''), (SumT (KnownT A_4) (NonceT B ''Kab'')))
  , ((B, ''Na''), (SumT (KnownT B_1) (NonceT A ''Na'')))
  , ((A, ''Nb''), (SumT (KnownT A_2) (NonceT B ''Nb'')))
  , ((A, ''Nbp''), (SumT (KnownT A_4) (NonceT B ''Nbp'')))
  ]"

sublocale Andrew_state < Andrew_msc_typing_state
proof -
  have "(t,r,s) : approx Andrew_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF Andrew_msc_typing.monoTyp, completeness_cases_rule])
    case (A_2_Nb t r s tid0) note facts = this
    then interpret state: Andrew_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''2'', {| LC ''succ'', LN ''Na'' tid0 |}, s(MV ''Nb'' tid0) |}
            ( K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (A_4_Kab t r s tid0) note facts = this
    then interpret state: Andrew_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''4'', s(MV ''Kab'' tid0), s(MV ''Nbp'' tid0) |}
            ( K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (A_4_Nbp t r s tid0) note facts = this
    then interpret state: Andrew_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''4'', s(MV ''Kab'' tid0), s(MV ''Nbp'' tid0) |}
            ( K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  next
    case (B_1_A t r s tid0) note facts = this
    then interpret state: Andrew_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (B_1_Na t r s tid0) note facts = this
    then interpret state: Andrew_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''1'', s(MV ''Na'' tid0) |}
            ( K ( s(MV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
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

lemma (in restricted_Andrew_state) B_sec_Kab:
  assumes facts:
    "roleMap r tid0 = Some B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "LN ''Kab'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''Kab'' tid0 ")
  case B_4_Kab note_unified facts = this facts
  thus ?thesis by (fastsimp dest!: ltk_secrecy)
qed (insert facts, fastsimp+)?

lemma (in restricted_Andrew_state) A_sec_Kab:
  assumes facts:
    "roleMap r tid0 = Some A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "( tid0, A_4 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''4'', s(MV ''Kab'' tid0), s(MV ''Nbp'' tid0) |}
                       ( K ( s(AV ''A'' tid0) ) ( s(AV ''B'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (B_4_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp dest: B_sec_Kab intro: event_predOrdI)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_Andrew_state) A_noninjective_agreement:
  assumes facts:
    "roleMap r tid1 = Some A"
    "RLKR(s(AV ''A'' tid1)) ~: reveals t"
    "RLKR(s(AV ''B'' tid1)) ~: reveals t"
    "( tid1, A_4 ) : steps t"
  shows
    "(?  tid2.
        roleMap r tid2 = Some B &
        s(AV ''A'' tid1) = s(MV ''A'' tid2) &
        s(AV ''B'' tid1) = s(AV ''B'' tid2) &
        s(MV ''Nbp'' tid1) = LN ''Nbp'' tid2 &
        s(MV ''Kab'' tid1) = LN ''Kab'' tid2)"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''4'', s(MV ''Kab'' tid1), s(MV ''Nbp'' tid1) |}
                       ( K ( s(AV ''A'' tid1) ) ( s(AV ''B'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (B_4_enc tid2) note_unified facts = this facts
    thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
  qed (insert facts, fastsimp+)?
qed

(* text: 
The protocol does not achieve agreement over Na and Nb. They could be sent
by a different thread also executing the B role. Hence, the B-thread that sent
the key Kab does not agree on anything that is fresh from the perspective of A.
This gives rise to the claimed attack referenced in the SPORE library.
 *)

lemma (in restricted_Andrew_state) B_noninjective_agreement:
  assumes facts:
    "roleMap r tid1 = Some B"
    "RLKR(s(AV ''B'' tid1)) ~: reveals t"
    "RLKR(s(MV ''A'' tid1)) ~: reveals t"
    "( tid1, B_3 ) : steps t"
  shows
    "(?  tid2.
        roleMap r tid2 = Some A &
        s(MV ''A'' tid1) = s(AV ''A'' tid2) &
        s(AV ''B'' tid1) = s(AV ''B'' tid2) &
        s(MV ''Na'' tid1) = LN ''Na'' tid2 & LN ''Nb'' tid1 = s(MV ''Nb'' tid2))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''3'', LC ''succ'', LN ''Nb'' tid1 |}
                       ( K ( s(MV ''A'' tid1) ) ( s(AV ''B'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (A_3_enc tid2) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''2'', {| LC ''succ'', LN ''Na'' tid2 |}, LN ''Nb'' tid1 |}
                         ( K ( s(AV ''A'' tid2) ) ( s(AV ''B'' tid1) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest!: ltk_secrecy)
    next
      case (B_2_enc tid3) note_unified facts = this facts
      thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
    qed (insert facts, fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

(* text: 
The protocol does not achieve agreement on the key because B cannot check if it
has been received.
 *)

end