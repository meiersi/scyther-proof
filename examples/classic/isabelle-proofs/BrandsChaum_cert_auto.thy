theory "BrandsChaum_cert_auto"
imports
  "ESPLogic"
begin

(* section:  Distance bounding following Brands, Chaum  *)

(* text: 

We model the distance bounding protocol following Brands and Chaum

  Stefan Brands and David Chaum. Distance-Bounding Protocols. EUROCRYPT '93     
  Lecture Notes in Computer Science 765, pp. 344--359, Springer, 1993.

Since the Dolev-Yao model has no notion of time, we can only show that
the challenge-response steps have to happen in the right order.

 *)

role P
where "P =
  [ Send ''1'' <| sAV ''P'', PEnc ( sN ''m'' ) ( sN ''k'' ) |>
  , Recv ''2'' ( sMV ''a'' )
  , Send ''3'' ( PHash <| sMV ''a'', sN ''m'' |> )
  , Send ''4'' <| sN ''m'', sN ''k'',
                  PEnc <| sMV ''a'', PHash <| sMV ''a'', sN ''m'' |> |> ( sSK ''P'' )
               |>
  ]"

role V
where "V =
  [ Recv ''1'' <| sMV ''P'', sMV ''c'' |>
  , Send ''2'' ( sN ''a'' )
  , Recv ''3'' ( sMV ''b'' )
  , Recv ''4'' <| sMV ''m'', sMV ''k'',
                  PEnc <| sN ''a'', sMV ''b'' |> ( PAsymSK ( sMV ''P'' ) )
               |>
  , MatchEq ''5'' ( MVar ''c'' ) ( PEnc ( sMV ''m'' ) ( sMV ''k'' ) )
  , MatchEq ''6'' ( MVar ''b'' ) ( PHash <| sN ''a'', sMV ''m'' |> )
  ]"

protocol BrandsChaum
where "BrandsChaum = { P, V }"

locale restricted_BrandsChaum_state = BrandsChaum_state

type_invariant BrandsChaum_msc_typing for BrandsChaum
where "BrandsChaum_msc_typing = mk_typing
  [ ((V, ''P''), (KnownT V_1))
  , ((P, ''a''), (KnownT P_2))
  , ((V, ''b''), (KnownT V_3))
  , ((V, ''c''), (KnownT V_1))
  , ((V, ''k''), (KnownT V_4))
  , ((V, ''m''), (KnownT V_4))
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
    case (V_4_m t r s tid0)
    then interpret state: BrandsChaum_msc_typing_state t r s
      by unfold_locales auto
    note_prefix_closed (state) facts = V_4_m
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
          RLKR(s(MV ''P'' tid0)) ~: reveals t & ( tid0, V_6 ) : steps t);
     concs =
       (% tid0 tid1.
          roleMap r tid1 = Some P &
          s(MV ''P'' tid0) = s(AV ''P'' tid1) &
          s(MV ''m'' tid0) = LN ''m'' tid1 &
          s(MV ''k'' tid0) = LN ''k'' tid1 &
          LN ''a'' tid0 = s(MV ''a'' tid1) &
          predOrd t (St( tid1, P_1 )) (St( tid0, V_2 )) &
          predOrd t (St( tid0, V_2 )) (St( tid1, P_3 )) &
          predOrd t (St( tid1, P_3 )) (St( tid0, V_3 )))
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
                       Enc {| LN ''a'' tid0, Hash {| LN ''a'' tid0, s(MV ''m'' tid0) |} |}
                           ( SK ( s(MV ''P'' tid0) ) ) ")
        case fake note_unified facts = this facts
        thus ?thesis by (auto dest!: ltk_secrecy)
      next
        case (P_4_enc tid1) note_unified facts = this facts
        thus ?thesis proof(sources! " LN ''a'' tid0 ")
          case V_2_a note_unified facts = this facts
          thus ?thesis proof(sources! " LN ''m'' tid1 ")
            case P_1_m note_unified facts = this facts
            thus ?thesis proof(sources! " LN ''k'' tid1 ")
              case P_4_k note_unified facts = this facts
              thus ?thesis proof(sources! "
                               Enc ( LN ''m'' tid1 ) ( s(MV ''k'' tid0) ) ")
                case (P_1_enc tid2) note_unified facts = this facts
                thus ?thesis proof(sources! " Hash {| LN ''a'' tid0, LN ''m'' tid1 |} ")
                  case fake note_unified facts = this facts
                  thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
                next
                  case (P_3_hash tid2) note_unified facts = this facts
                  thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
                next
                  case (P_4_hash tid2) note_unified facts = this facts
                  thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
                qed (safe?, simp_all?, insert facts, (fastforce+)?)
              qed (safe?, simp_all?, insert facts, ((((clarsimp, order?) | order | fast))+)?)
            qed (safe?, simp_all?, insert facts, (fastforce+)?)
          next
            case P_4_m note_unified facts = this facts
            thus ?thesis proof(sources! "
                             Enc ( LN ''m'' tid1 ) ( s(MV ''k'' tid0) ) ")
              case (P_1_enc tid2) note_unified facts = this facts
              thus ?thesis proof(sources! " Hash {| LN ''a'' tid0, LN ''m'' tid1 |} ")
                case fake note_unified facts = this facts
                thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
              next
                case (P_3_hash tid2) note_unified facts = this facts
                thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
              next
                case (P_4_hash tid2) note_unified facts = this facts
                thus ?thesis by (fastforce intro: event_predOrdI split: if_splits)
              qed (safe?, simp_all?, insert facts, (fastforce+)?)
            qed (safe?, simp_all?, insert facts, ((((clarsimp, order?) | order | fast))+)?)
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