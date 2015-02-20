theory "BrandsChaum_iterated_cert_auto"
imports
  "ESPLogic"
begin

(* text: 

The same model of the Brands Chaum distance bounding protocol as in BrandsChaum.spthy
except that now two challenges are exchanged.

 *)

role P
where "P =
  [ Send ''1'' <| sAV ''P'', PEnc <| sN ''m1'', sN ''m2'' |> ( sN ''k'' )
               |>
  , Recv ''21'' ( sMV ''a1'' )
  , Send ''31'' ( PHash <| sMV ''a1'', sN ''m1'' |> )
  , Recv ''22'' ( sMV ''a2'' )
  , Send ''32'' ( PHash <| sMV ''a2'', sN ''m2'' |> )
  , Send ''4'' <| sN ''m1'', sN ''m2'', sN ''m3'', sN ''k'',
                  PEnc <| sMV ''a1'', PHash <| sMV ''a1'', sN ''m1'' |>, sMV ''a2'',
                          PHash <| sMV ''a2'', sN ''m2'' |>
                       |>
                       ( sSK ''P'' )
               |>
  ]"

role V
where "V =
  [ Recv ''1'' <| sMV ''P'', sMV ''c'' |>
  , Send ''21'' ( sN ''a1'' )
  , Recv ''31'' ( sMV ''b1'' )
  , Send ''22'' ( sN ''a2'' )
  , Recv ''32'' ( sMV ''b2'' )
  , Recv ''4'' <| sMV ''m1'', sMV ''m2'', sMV ''m3'', sMV ''k'',
                  PEnc <| sN ''a1'', sMV ''b1'', sN ''a2'', sMV ''b2'' |>
                       ( PAsymSK ( sMV ''P'' ) )
               |>
  , MatchEq ''5'' ( MVar ''c'' ) ( PEnc <| sMV ''m1'', sMV ''m2'' |>
                                        ( sMV ''k'' )
                                 )
  , MatchEq ''61'' ( MVar ''b1'' ) ( PHash <| sN ''a1'', sMV ''m1'' |> )
  , MatchEq ''62'' ( MVar ''b2'' ) ( PHash <| sN ''a2'', sMV ''m2'' |> )
  ]"

protocol BrandsChaum
where "BrandsChaum = { P, V }"

locale restricted_BrandsChaum_state = BrandsChaum_state

type_invariant BrandsChaum_msc_typing for BrandsChaum
where "BrandsChaum_msc_typing = mk_typing
  [ ((V, ''P''), (KnownT V_1))
  , ((P, ''a1''), (KnownT P_21))
  , ((P, ''a2''), (KnownT P_22))
  , ((V, ''b1''), (KnownT V_31))
  , ((V, ''b2''), (KnownT V_32))
  , ((V, ''c''), (KnownT V_1))
  , ((V, ''k''), (KnownT V_4))
  , ((V, ''m1''), (KnownT V_4))
  , ((V, ''m2''), (KnownT V_4))
  , ((V, ''m3''), (KnownT V_4))
  ]"

sublocale BrandsChaum_state < BrandsChaum_msc_typing_state
proof -
  have "(t,r,s) : approx BrandsChaum_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF BrandsChaum_msc_typing.monoTyp, completeness_cases_rule])
    case (V_1_P t r s tid0)
    then interpret state: BrandsChaum_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = V_1_P
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (V_1_c t r s tid0)
    then interpret state: BrandsChaum_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = V_1_c
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (V_4_k t r s tid0)
    then interpret state: BrandsChaum_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = V_4_k
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (V_4_m1 t r s tid0)
    then interpret state: BrandsChaum_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = V_4_m1
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (V_4_m2 t r s tid0)
    then interpret state: BrandsChaum_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = V_4_m2
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (V_4_m3 t r s tid0)
    then interpret state: BrandsChaum_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = V_4_m3
    thus ?case
    by (fastforce intro: event_predOrdI split: if_splits)
  qed
  thus "BrandsChaum_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context BrandsChaum_state begin

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

lemma (in restricted_BrandsChaum_state) prover_recent:
  "let
     prems =
       (% tid0.
          roleMap r tid0 = Some V &
          RLKR(s(MV ''P'' tid0)) ~: reveals t & ( tid0, V_62 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some P &
          s(MV ''P'' tid0) = s(AV ''P'' tid1) &
          s(MV ''m1'' tid0) = LN ''m1'' tid1 &
          s(MV ''m2'' tid0) = LN ''m2'' tid1 &
          s(MV ''k'' tid0) = LN ''k'' tid1 &
          LN ''a1'' tid0 = s(MV ''a1'' tid1) &
          LN ''a2'' tid0 = s(MV ''a2'' tid1) &
          predOrd t (St( tid1, P_1 )) (St( tid0, V_21 )) &
          predOrd t (St( tid0, V_21 )) (St( tid1, P_31 )) &
          predOrd t (St( tid1, P_31 )) (St( tid0, V_31 )) &
          predOrd t (St( tid0, V_31 )) (St( tid0, V_22 )) &
          predOrd t (St( tid0, V_22 )) (St( tid1, P_32 )) &
          predOrd t (St( tid1, P_32 )) (St( tid0, V_32 )))
   in ? f. inj_on f (Collect prems) & (! i. prems i --> concs i (f i))"
  (is "let prems = ?prems; concs = ?concs in ?P prems concs")
proof -
  { fix tid0 tid1
    assume facts: "?prems tid0"
    have " ? tid1. ?concs tid0 tid1"
    proof -
      note_unified facts = facts
      note_prefix_closed facts = facts
      thus ?thesis proof(sources! "
                       Enc {| LN ''a1'' tid0, Hash {| LN ''a1'' tid0, s(MV ''m1'' tid0) |},
                              LN ''a2'' tid0, Hash {| LN ''a2'' tid0, s(MV ''m2'' tid0) |}
                           |}
                           ( SK ( s(MV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (P_4_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! " LN ''a1'' tid0 ")
          case V_21_a1 note_unified facts = this facts
          thus ?thesis proof(sources! " LN ''a2'' tid0 ")
            case V_22_a2 note_unified facts = this facts
            thus ?thesis proof(sources! "
                             Enc {| LN ''m1'' tid1, LN ''m2'' tid1 |} ( s(MV ''k'' tid0) ) ")
              case fake note_unified facts = this facts
              thus ?thesis proof(sources! " LN ''m1'' tid1 ")
                case P_1_m1 note_unified facts = this facts
                thus ?thesis proof(sources! " LN ''k'' tid1 ")
                qed (safe?, simp_all?, insert facts, (fastforce+)?)
              qed (safe?, simp_all?, insert facts, (fastforce+)?)
            next
              case (P_1_enc tid2) note_unified facts = this facts
              thus ?thesis proof(sources! " LN ''k'' tid1 ")
                case P_4_k note_unified facts = this facts
                thus ?thesis proof(sources! "
                                 Hash {| LN ''a1'' tid0, LN ''m1'' tid1 |} ")
                  case fake note_unified facts = this facts
                  thus ?thesis proof(sources! " LN ''m1'' tid1 ")
                  qed (safe?, simp_all?, insert facts, (fastforce+)?)
                next
                  case (P_31_hash tid2) note_unified facts = this facts
                  thus ?thesis proof(sources! "
                                   Hash {| LN ''a2'' tid0, LN ''m2'' tid1 |} ")
                    case fake note_unified facts = this facts
                    thus ?thesis proof(sources! " LN ''m2'' tid1 ")
                      case P_1_m2 note_unified facts = this facts
                      thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
                    next
                      case P_4_m2 note_unified facts = this facts
                      thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
                    qed (safe?, simp_all?, insert facts, (fastforce+)?)
                  next
                    case (P_32_hash tid2) note_unified facts = this facts
                    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
                  next
                    case (P_4_hash_1 tid2) note_unified facts = this facts
                    thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
                  qed (safe?, simp_all?, insert facts, (fastforce+)?)
                qed (safe?, simp_all?, insert facts, ((((clarsimp, order?) | order | fast))+)?)
              qed (safe?, simp_all?, insert facts, (fastforce+)?)
            qed (safe?, simp_all?, insert facts, (fastforce+)?)
          qed (safe?, simp_all?, insert facts, (fastforce+)?)
        qed (safe?, simp_all?, insert facts, (fastforce+)?)
      qed (safe?, simp_all?, insert facts, (fastforce+)?)
    qed
  }
  note niagree = this
  { fix i1 i2 j
    assume "?concs i1 j & ?concs i2 j"
    note_unified facts = this
    have "i1 = i2" using facts by simp
  }
  note conc_inj = this
  show ?thesis
    by (fast intro!: iagree_to_niagree elim!: niagree conc_inj)
qed

end