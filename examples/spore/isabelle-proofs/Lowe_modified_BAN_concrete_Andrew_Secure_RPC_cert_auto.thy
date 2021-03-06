theory "Lowe_modified_BAN_concrete_Andrew_Secure_RPC_cert_auto"
imports
  "ESPLogic"
begin

(* section:  Lowe modified BAN concrete Andrew Secure RPC  *)

(* text: 
  Modeled after the model in the SPORE library.

  Notable differences:

    1. 'succ(x)' is invertible. Hence, we just model it as a tuple ('succ',x) of
       a global constant 'succ' and the variable x.  This means that we only
       exploit the tagging properties of 'succ', but do not assume any
       information hiding.

    2. Instead of implicit typing, we are using explicit global constants to
       discern messages.
 *)

role A
where "A =
  [ Send ''1'' <| sAV ''A'', sN ''Na'' |>
  , Recv ''2'' <| sMV ''B'',
                  PEnc <| sC ''2'', sN ''Na'', sMV ''Kab'', sMV ''B'' |>
                       ( sKbd (AVar ''A'') (MVar ''B'') )
               |>
  , Send ''3'' ( PEnc <| sC ''3'', sN ''Na'' |> ( sMV ''Kab'' ) )
  , Recv ''4'' ( sMV ''Nb'' )
  ]"

role B
where "B =
  [ Recv ''1'' <| sMV ''A'', sMV ''Na'' |>
  , Send ''2'' <| sAV ''B'',
                  PEnc <| sC ''2'', sMV ''Na'', sN ''Kab'', sAV ''B'' |>
                       ( sKbd (MVar ''A'') (AVar ''B'') )
               |>
  , Recv ''3'' ( PEnc <| sC ''3'', sMV ''Na'' |> ( sN ''Kab'' ) )
  , Send ''4'' ( sN ''Nb'' )
  ]"

protocol Andrew
where "Andrew = { A, B }"

locale restricted_Andrew_state = Andrew_state

type_invariant Andrew_msc_typing for Andrew
where "Andrew_msc_typing = mk_typing
  [ ((B, ''A''), (KnownT B_1))
  , ((A, ''B''), (KnownT A_2))
  , ((A, ''Kab''), (SumT (KnownT A_2) (NonceT B ''Kab'')))
  , ((B, ''Na''), (KnownT B_1))
  , ((A, ''Nb''), (KnownT A_4))
  ]"

sublocale Andrew_state < Andrew_msc_typing_state
proof -
  have "(t,r,s) : approx Andrew_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF Andrew_msc_typing.monoTyp, completeness_cases_rule])
    case (A_2_B t r s tid0)
    then interpret state: Andrew_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_2_B
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (A_2_Kab t r s tid0)
    then interpret state: Andrew_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = A_2_Kab
    thus ?case
    proof(sources! "
        Enc {| LC ''2'', LN ''Na'' tid0, s(MV ''Kab'' tid0), s(MV ''B'' tid0) |}
            ( Kbd ( s(AV ''A'' tid0) ) ( s(MV ''B'' tid0) ) ) ")
    qed (safe?, simp_all?, insert facts, (((fastforce intro: event_predOrdI split: if_splits))+)?)
  next
    case (B_1_A t r s tid0)
    then interpret state: Andrew_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = B_1_A
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (B_1_Na t r s tid0)
    then interpret state: Andrew_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = B_1_Na
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
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

(* text:  
Note the additional B identity in the second message above. It guarantees that
despite using a bidirectional longterm symmetric key, we have agreement on the
involved roles.
 *)

(* subsection:  Security Properties  *)

lemma (in restricted_Andrew_state) B_sec_Kab:
  assumes facts:
    "roleMap r tid0 = Some B"
    "RLKR(s(AV ''B'' tid0)) ~: reveals t"
    "RLKR(s(MV ''A'' tid0)) ~: reveals t"
    "LN ''Kab'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''Kab'' tid0 ")
  case B_2_Kab note_unified facts = this facts
  thus ?thesis by (auto dest!: ltk_secrecy)
qed (safe?, simp_all?, insert facts, (fastforce+)?)

lemma (in restricted_Andrew_state) A_sec_Kab:
  assumes facts:
    "roleMap r tid0 = Some A"
    "RLKR(s(AV ''A'' tid0)) ~: reveals t"
    "RLKR(s(MV ''B'' tid0)) ~: reveals t"
    "( tid0, A_2 ) : steps t"
    "s(MV ''Kab'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''2'', LN ''Na'' tid0, s(MV ''Kab'' tid0), s(MV ''B'' tid0) |}
                       ( Kbd ( s(AV ''A'' tid0) ) ( s(MV ''B'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (B_2_enc tid1) note_unified facts = this facts
    thus ?thesis by (fastforce dest: B_sec_Kab intro: event_predOrdI)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

lemma (in restricted_Andrew_state) A_noninjective_agreement:
  assumes facts:
    "roleMap r tid1 = Some A"
    "RLKR(s(AV ''A'' tid1)) ~: reveals t"
    "RLKR(s(MV ''B'' tid1)) ~: reveals t"
    "( tid1, A_2 ) : steps t"
  shows
    "(?  tid2.
        roleMap r tid2 = Some B &
        s(AV ''A'' tid1) = s(MV ''A'' tid2) &
        s(MV ''B'' tid1) = s(AV ''B'' tid2) &
        LN ''Na'' tid1 = s(MV ''Na'' tid2) &
        s(MV ''Kab'' tid1) = LN ''Kab'' tid2)"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''2'', LN ''Na'' tid1, s(MV ''Kab'' tid1), s(MV ''B'' tid1) |}
                       ( Kbd ( s(AV ''A'' tid1) ) ( s(MV ''B'' tid1) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (auto dest!: ltk_secrecy)
  next
    case (B_2_enc tid2) note_unified facts = this facts
    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

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
        s(AV ''B'' tid1) = s(MV ''B'' tid2) &
        s(MV ''Na'' tid1) = LN ''Na'' tid2 &
        LN ''Kab'' tid1 = s(MV ''Kab'' tid2))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''3'', s(MV ''Na'' tid1) |} ( LN ''Kab'' tid1 ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastforce dest: B_sec_Kab intro: event_predOrdI)
  next
    case (A_3_enc tid2) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Enc {| LC ''2'', LN ''Na'' tid2, LN ''Kab'' tid1, s(MV ''B'' tid2) |}
                         ( Kbd ( s(AV ''A'' tid2) ) ( s(MV ''B'' tid2) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastforce dest: B_sec_Kab intro: event_predOrdI)
    next
      case (B_2_enc tid3) note_unified facts = this facts
      thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
    qed (safe?, simp_all?, insert facts, (fastforce+)?)
  qed (safe?, simp_all?, insert facts, (fastforce+)?)
qed

end