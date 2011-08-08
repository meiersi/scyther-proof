theory "TLS_cert_auto"
imports
  "../ESPLogic"
begin

(* section:  TLS Handshake  *)

(* text: 
  Modeled after Paulson's TLS model in Isabelle/src/HOL/Auth/TLS.thy. Notable
  differences are:

    1. We use explicit global constants to differentiate between different
       encryptions instead of implicit typing.

    2. We abstract certificates even further to the trivial form of completely
       predistributed certificates pk(A) with their private key pk(A) for any
       agent A. The reason for this abstraction is that we need to generalize
       weak atomicity further before we can support receiving composed terms in
       a variable.

       [TODO: Remove this simplification, as weak-atomicity is now generalized.]

    3. We model session keys directly as hashes of the relevant information.
       Due to our support for composed keys, we do not need any custom
       axiomatization as Paulson did.

 *)

role C
where "C =
  [ Send ''1'' <| sAV ''C'', sN ''nc'', sN ''sid'', sN ''pc'' |>
  , Recv ''2'' <| sMV ''ns'', sN ''sid'', sMV ''ps'' |>
  , Send ''3'' <| PEnc <| sC ''TT0'', sN ''pms'' |> ( sPK ''S'' ),
                  PEnc <| sC ''TT1'',
                          PHash <| sC ''TT2'', sMV ''ns'', sAV ''S'', sN ''pms'' |>
                       |>
                       ( sSK ''C'' ),
                  PEnc <| sC ''TT3'', sN ''sid'',
                          PHash <| sC ''TT4'', sC ''PRF'', sN ''pms'', sN ''nc'', sMV ''ns'' |>,
                          sN ''nc'', sN ''pc'', sAV ''C'', sMV ''ns'', sMV ''ps'', sAV ''S''
                       |>
                       ( PHash <| sC ''clientKey'', sN ''nc'', sMV ''ns'',
                                  PHash <| sC ''TT4'', sC ''PRF'', sN ''pms'', sN ''nc'', sMV ''ns'' |>
                               |>
                       )
               |>
  , Recv ''4'' ( PEnc <| sC ''TT3'', sN ''sid'',
                         PHash <| sC ''TT4'', sC ''PRF'', sN ''pms'', sN ''nc'', sMV ''ns'' |>,
                         sN ''nc'', sN ''pc'', sAV ''C'', sMV ''ns'', sMV ''ps'', sAV ''S''
                      |>
                      ( PHash <| sC ''serverKey'', sN ''nc'', sMV ''ns'',
                                 PHash <| sC ''TT4'', sC ''PRF'', sN ''pms'', sN ''nc'', sMV ''ns'' |>
                              |>
                      )
               )
  ]"

role S
where "S =
  [ Recv ''1'' <| sMV ''C'', sMV ''nc'', sMV ''sid'', sMV ''pc'' |>
  , Send ''2'' <| sN ''ns'', sMV ''sid'', sN ''ps'' |>
  , Recv ''3'' <| PEnc <| sC ''TT0'', sMV ''pms'' |> ( sPK ''S'' ),
                  PEnc <| sC ''TT1'',
                          PHash <| sC ''TT2'', sN ''ns'', sAV ''S'', sMV ''pms'' |>
                       |>
                       ( PAsymSK ( sMV ''C'' ) ),
                  PEnc <| sC ''TT3'', sMV ''sid'',
                          PHash <| sC ''TT4'', sC ''PRF'', sMV ''pms'', sMV ''nc'', sN ''ns'' |>,
                          sMV ''nc'', sMV ''pc'', sMV ''C'', sN ''ns'', sN ''ps'', sAV ''S''
                       |>
                       ( PHash <| sC ''clientKey'', sMV ''nc'', sN ''ns'',
                                  PHash <| sC ''TT4'', sC ''PRF'', sMV ''pms'', sMV ''nc'', sN ''ns'' |>
                               |>
                       )
               |>
  , Send ''4'' ( PEnc <| sC ''TT3'', sMV ''sid'',
                         PHash <| sC ''TT4'', sC ''PRF'', sMV ''pms'', sMV ''nc'', sN ''ns'' |>,
                         sMV ''nc'', sMV ''pc'', sMV ''C'', sN ''ns'', sN ''ps'', sAV ''S''
                      |>
                      ( PHash <| sC ''serverKey'', sMV ''nc'', sN ''ns'',
                                 PHash <| sC ''TT4'', sC ''PRF'', sMV ''pms'', sMV ''nc'', sN ''ns'' |>
                              |>
                      )
               )
  ]"

protocol TLS
where "TLS = { C, S }"

locale restricted_TLS_state = TLS_state

type_invariant TLS_msc_typing for TLS
where "TLS_msc_typing = mk_typing
  [ ((S, ''C''), (KnownT S_1))
  , ((S, ''nc''), (KnownT S_1))
  , ((C, ''ns''), (KnownT C_2))
  , ((S, ''pc''), (KnownT S_1))
  , ((S, ''pms''), (SumT (KnownT S_3) (NonceT C ''pms'')))
  , ((C, ''ps''), (KnownT C_2))
  , ((S, ''sid''), (KnownT S_1))
  ]"

sublocale TLS_state < TLS_msc_typing_state
proof -
  have "(t,r,s) : approx TLS_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF TLS_msc_typing.monoTyp, completeness_cases_rule])
    case (C_2_ns t r s tid0) note facts = this
    then interpret state: TLS_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (C_2_ps t r s tid0) note facts = this
    then interpret state: TLS_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (S_1_C t r s tid0) note facts = this
    then interpret state: TLS_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (S_1_nc t r s tid0) note facts = this
    then interpret state: TLS_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (S_1_pc t r s tid0) note facts = this
    then interpret state: TLS_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (S_1_sid t r s tid0) note facts = this
    then interpret state: TLS_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastsimp intro: event_predOrdI split: if_splits)
  next
    case (S_3_pms t r s tid0) note facts = this
    then interpret state: TLS_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''TT0'', s(MV ''pms'' tid0) |} ( PK ( s(AV ''S'' tid0) ) ) ")
    qed (insert facts, ((fastsimp intro: event_predOrdI split: if_splits))+)?
  qed
  thus "TLS_msc_typing_state t r s" by unfold_locales auto
qed

text{* Prove secrecy of long-term keys. *}
context TLS_state begin

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

lemma (in restricted_TLS_state) C_pms_sec:
  assumes facts:
    "roleMap r tid0 = Some C"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "LN ''pms'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''pms'' tid0 ")
  case C_3_pms note_unified facts = this facts
  thus ?thesis by (fastsimp dest!: ltk_secrecy)
qed (insert facts, fastsimp+)?

lemma (in restricted_TLS_state) C_PRF_sec:
  assumes facts:
    "roleMap r tid0 = Some C"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' tid0, LN ''nc'' tid0,
             s(MV ''ns'' tid0)
          |} : knows t"
  shows "False"
using facts proof(sources! "
                Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' tid0, LN ''nc'' tid0,
                        s(MV ''ns'' tid0)
                     |} ")
  case fake note_unified facts = this facts
  thus ?thesis by (fastsimp dest: C_pms_sec intro: event_predOrdI)
next
  case (C_3_hash_1 tid1) note_unified facts = this facts
  thus ?thesis proof(sources! "
                   Hash {| LC ''clientKey'', LN ''nc'' tid0, s(MV ''ns'' tid0),
                           Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' tid0, LN ''nc'' tid0,
                                   s(MV ''ns'' tid0)
                                |}
                        |} ")
  qed (insert facts, (((clarsimp, order?) | order))+)?
next
  case (S_4_hash tid1) note_unified facts = this facts
  thus ?thesis proof(sources! "
                   Hash {| LC ''serverKey'', LN ''nc'' tid0, LN ''ns'' tid1,
                           Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' tid0, LN ''nc'' tid0,
                                   LN ''ns'' tid1
                                |}
                        |} ")
  qed (insert facts, (((clarsimp, order?) | order))+)?
qed (insert facts, fastsimp+)?

lemma (in restricted_TLS_state) C_clientKey_sec:
  assumes facts:
    "roleMap r tid0 = Some C"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "Hash {| LC ''clientKey'', LN ''nc'' tid0, s(MV ''ns'' tid0),
             Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' tid0, LN ''nc'' tid0,
                     s(MV ''ns'' tid0)
                  |}
          |} : knows t"
  shows "False"
using facts proof(sources! "
                Hash {| LC ''clientKey'', LN ''nc'' tid0, s(MV ''ns'' tid0),
                        Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' tid0, LN ''nc'' tid0,
                                s(MV ''ns'' tid0)
                             |}
                     |} ")
  case fake note_unified facts = this facts
  thus ?thesis by (fastsimp dest: C_PRF_sec intro: event_predOrdI)
qed (insert facts, fastsimp+)?

lemma (in restricted_TLS_state) C_serverKey_sec:
  assumes facts:
    "roleMap r tid0 = Some C"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "Hash {| LC ''serverKey'', LN ''nc'' tid0, s(MV ''ns'' tid0),
             Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' tid0, LN ''nc'' tid0,
                     s(MV ''ns'' tid0)
                  |}
          |} : knows t"
  shows "False"
using facts proof(sources! "
                Hash {| LC ''serverKey'', LN ''nc'' tid0, s(MV ''ns'' tid0),
                        Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' tid0, LN ''nc'' tid0,
                                s(MV ''ns'' tid0)
                             |}
                     |} ")
  case fake note_unified facts = this facts
  thus ?thesis by (fastsimp dest: C_PRF_sec intro: event_predOrdI)
qed (insert facts, fastsimp+)?

lemma (in restricted_TLS_state) S_pms_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''C'' tid0)) ~: reveals t"
    "( tid0, S_4 ) : steps t"
    "s(MV ''pms'' tid0) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'',
                          Hash {| LC ''TT2'', LN ''ns'' tid0, s(AV ''S'' tid0), s(MV ''pms'' tid0)
                               |}
                       |}
                       ( SK ( s(MV ''C'' tid0) ) ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest!: ltk_secrecy)
  next
    case (C_3_enc_1 tid1) note_unified facts = this facts
    thus ?thesis by (fastsimp dest: C_pms_sec intro: event_predOrdI)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_TLS_state) S_PRF_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''C'' tid0)) ~: reveals t"
    "( tid0, S_4 ) : steps t"
    "Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' tid0), s(MV ''nc'' tid0),
             LN ''ns'' tid0
          |} : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' tid0), s(MV ''nc'' tid0),
                           LN ''ns'' tid0
                        |} ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest: S_pms_sec intro: event_predOrdI)
  next
    case (C_3_hash_1 tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Hash {| LC ''clientKey'', LN ''nc'' tid1, LN ''ns'' tid0,
                             Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' tid1, LN ''nc'' tid1,
                                     LN ''ns'' tid0
                                  |}
                          |} ")
    qed (insert facts, (((clarsimp, order?) | order))+)?
  next
    case (S_4_hash tid1) note_unified facts = this facts
    thus ?thesis proof(sources! "
                     Hash {| LC ''serverKey'', s(MV ''nc'' tid0), LN ''ns'' tid0,
                             Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' tid0), s(MV ''nc'' tid0),
                                     LN ''ns'' tid0
                                  |}
                          |} ")
    qed (insert facts, (((clarsimp, order?) | order))+)?
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_TLS_state) S_clientKey_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''C'' tid0)) ~: reveals t"
    "( tid0, S_4 ) : steps t"
    "Hash {| LC ''clientKey'', s(MV ''nc'' tid0), LN ''ns'' tid0,
             Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' tid0), s(MV ''nc'' tid0),
                     LN ''ns'' tid0
                  |}
          |} : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Hash {| LC ''clientKey'', s(MV ''nc'' tid0), LN ''ns'' tid0,
                           Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' tid0), s(MV ''nc'' tid0),
                                   LN ''ns'' tid0
                                |}
                        |} ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest: S_PRF_sec intro: event_predOrdI)
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_TLS_state) S_serverKey_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "RLKR(s(AV ''S'' tid0)) ~: reveals t"
    "RLKR(s(MV ''C'' tid0)) ~: reveals t"
    "( tid0, S_4 ) : steps t"
    "Hash {| LC ''serverKey'', s(MV ''nc'' tid0), LN ''ns'' tid0,
             Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' tid0), s(MV ''nc'' tid0),
                     LN ''ns'' tid0
                  |}
          |} : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Hash {| LC ''serverKey'', s(MV ''nc'' tid0), LN ''ns'' tid0,
                           Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' tid0), s(MV ''nc'' tid0),
                                   LN ''ns'' tid0
                                |}
                        |} ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest: S_PRF_sec intro: event_predOrdI)
  qed (insert facts, fastsimp+)?
qed

(* subsection:  Authentication Properties  *)

(* text: 
  First, we prove two first send properties in order to simplify proof search
  for the authentication properties.
 *)

lemma (in restricted_TLS_state) nc_first_send:
  assumes facts:
    "roleMap r tid1 = Some C"
    "LN ''nc'' tid1 : knows t"
  shows "predOrd t (St( tid1, C_1 )) (Ln(LN ''nc'' tid1))"
using facts proof(sources! " LN ''nc'' tid1 ")
  case C_1_nc note_unified facts = this facts
  thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
next
  case C_3_nc note_unified facts = this facts
  thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
qed (insert facts, fastsimp+)?

lemma (in restricted_TLS_state) ns_first_send:
  assumes facts:
    "roleMap r tid1 = Some S"
    "LN ''ns'' tid1 : knows t"
  shows "predOrd t (St( tid1, S_2 )) (Ln(LN ''ns'' tid1))"
using facts proof(sources! " LN ''ns'' tid1 ")
  case S_2_ns note_unified facts = this facts
  thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
next
  case S_4_ns note_unified facts = this facts
  thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
qed (insert facts, fastsimp+)?

lemma (in restricted_TLS_state) C_ni_synch:
  assumes facts:
    "roleMap r tid1 = Some C"
    "RLKR(s(AV ''C'' tid1)) ~: reveals t"
    "RLKR(s(AV ''S'' tid1)) ~: reveals t"
    "( tid1, C_4 ) : steps t"
  shows
    "(?  tid2.
        roleMap r tid2 = Some S &
        s(AV ''C'' tid1) = s(MV ''C'' tid2) &
        s(AV ''S'' tid1) = s(AV ''S'' tid2) &
        LN ''nc'' tid1 = s(MV ''nc'' tid2) &
        s(MV ''ns'' tid1) = LN ''ns'' tid2 &
        LN ''pc'' tid1 = s(MV ''pc'' tid2) &
        s(MV ''ps'' tid1) = LN ''ps'' tid2 &
        LN ''sid'' tid1 = s(MV ''sid'' tid2) &
        LN ''pms'' tid1 = s(MV ''pms'' tid2) &
        predOrd t (St( tid1, C_1 )) (St( tid2, S_1 )) &
        predOrd t (St( tid2, S_1 )) (St( tid2, S_2 )) &
        predOrd t (St( tid2, S_2 )) (St( tid1, C_2 )) &
        predOrd t (St( tid1, C_2 )) (St( tid1, C_3 )) &
        predOrd t (St( tid1, C_3 )) (St( tid2, S_3 )) &
        predOrd t (St( tid2, S_3 )) (St( tid2, S_4 )) &
        predOrd t (St( tid2, S_4 )) (St( tid1, C_4 )))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT3'', LN ''sid'' tid1,
                          Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' tid1, LN ''nc'' tid1,
                                  s(MV ''ns'' tid1)
                               |},
                          LN ''nc'' tid1, LN ''pc'' tid1, s(AV ''C'' tid1), s(MV ''ns'' tid1),
                          s(MV ''ps'' tid1), s(AV ''S'' tid1)
                       |}
                       ( Hash {| LC ''serverKey'', LN ''nc'' tid1, s(MV ''ns'' tid1),
                                 Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' tid1, LN ''nc'' tid1,
                                         s(MV ''ns'' tid1)
                                      |}
                              |}
                       ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest: C_PRF_sec intro: event_predOrdI)
  next
    case (S_4_enc tid2) note_unified facts = this facts
    have f1: "roleMap r tid1 = Some C" using facts by (auto intro: event_predOrdI)
    have f2: "LN ''nc'' tid1 : knows t" using facts by (auto intro: event_predOrdI)
    note facts = facts nc_first_send[OF f1 f2, simplified]
    have f1: "roleMap r tid2 = Some S" using facts by (auto intro: event_predOrdI)
    have f2: "LN ''ns'' tid2 : knows t" using facts by (auto intro: event_predOrdI)
    note facts = facts ns_first_send[OF f1 f2, simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT0'', LN ''pms'' tid1 |} ( PK ( s(AV ''S'' tid1) ) ) ")
      case fake note_unified facts = this facts
      thus ?thesis by (fastsimp dest: C_pms_sec intro: event_predOrdI)
    next
      case (C_3_enc tid3) note_unified facts = this facts
      thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
    qed (insert facts, fastsimp+)?
  qed (insert facts, fastsimp+)?
qed

lemma (in restricted_TLS_state) S_ni_synch:
  assumes facts:
    "roleMap r tid2 = Some S"
    "RLKR(s(AV ''S'' tid2)) ~: reveals t"
    "RLKR(s(MV ''C'' tid2)) ~: reveals t"
    "( tid2, S_4 ) : steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some C &
        s(AV ''C'' tid1) = s(MV ''C'' tid2) &
        s(AV ''S'' tid1) = s(AV ''S'' tid2) &
        LN ''nc'' tid1 = s(MV ''nc'' tid2) &
        s(MV ''ns'' tid1) = LN ''ns'' tid2 &
        LN ''pc'' tid1 = s(MV ''pc'' tid2) &
        s(MV ''ps'' tid1) = LN ''ps'' tid2 &
        LN ''sid'' tid1 = s(MV ''sid'' tid2) &
        LN ''pms'' tid1 = s(MV ''pms'' tid2) &
        predOrd t (St( tid1, C_1 )) (St( tid2, S_1 )) &
        predOrd t (St( tid2, S_1 )) (St( tid2, S_2 )) &
        predOrd t (St( tid2, S_2 )) (St( tid1, C_2 )) &
        predOrd t (St( tid1, C_2 )) (St( tid1, C_3 )) &
        predOrd t (St( tid1, C_3 )) (St( tid2, S_3 )) &
        predOrd t (St( tid2, S_3 )) (St( tid2, S_4 )))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT3'', s(MV ''sid'' tid2),
                          Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' tid2), s(MV ''nc'' tid2),
                                  LN ''ns'' tid2
                               |},
                          s(MV ''nc'' tid2), s(MV ''pc'' tid2), s(MV ''C'' tid2), LN ''ns'' tid2,
                          LN ''ps'' tid2, s(AV ''S'' tid2)
                       |}
                       ( Hash {| LC ''clientKey'', s(MV ''nc'' tid2), LN ''ns'' tid2,
                                 Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' tid2), s(MV ''nc'' tid2),
                                         LN ''ns'' tid2
                                      |}
                              |}
                       ) ")
    case fake note_unified facts = this facts
    thus ?thesis by (fastsimp dest: S_PRF_sec intro: event_predOrdI)
  next
    case (C_3_enc_2 tid3) note_unified facts = this facts
    have f1: "roleMap r tid3 = Some C" using facts by (auto intro: event_predOrdI)
    have f2: "LN ''nc'' tid3 : knows t" using facts by (auto intro: event_predOrdI)
    note facts = facts nc_first_send[OF f1 f2, simplified]
    have f1: "roleMap r tid2 = Some S" using facts by (auto intro: event_predOrdI)
    have f2: "LN ''ns'' tid2 : knows t" using facts by (auto intro: event_predOrdI)
    note facts = facts ns_first_send[OF f1 f2, simplified]
    thus ?thesis by (fastsimp intro: event_predOrdI split: if_splits)
  qed (insert facts, fastsimp+)?
qed

end