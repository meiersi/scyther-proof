theory "tls-simplified_cert_auto"
imports
  "../ESPLogic"
begin

role C
where "C =
  [ Recv ''1'' ( sLMV ''ns'' )
  , Send ''2'' {| Enc {| sLC ''TT1'', sLN ''pms'' |} ( sPK ''S'' ),
                  Enc ( Hash {| sLC ''TT2'', sLMV ''ns'', sLAV ''S'', sLN ''pms'' |}
                      )
                      ( sSK ''C'' ),
                  Enc {| sLAV ''S'', sLAV ''C'', sLMV ''ns'', sLN ''pms'' |}
                      ( Hash {| sLN ''pms'', sLMV ''ns'' |} )
               |}
  , Recv ''3'' ( Enc {| sLAV ''C'', sLAV ''S'', sLMV ''ns'',
                        sLN ''pms''
                     |}
                     ( Hash {| sLN ''pms'', sLMV ''ns'' |} )
               )
  , Send ''4'' ( Enc {| sLC ''TT4'', sLN ''Payload'' |}
                     ( Hash {| sLN ''pms'', sLMV ''ns'' |} )
               )
  ]"

role S
where "S =
  [ Send ''1'' ( sLN ''ns'' )
  , Recv ''2'' {| Enc {| sLC ''TT1'', sLMV ''pms'' |} ( sPK ''S'' ),
                  Enc ( Hash {| sLC ''TT2'', sLN ''ns'', sLAV ''S'', sLMV ''pms'' |}
                      )
                      ( sSK ''C'' ),
                  Enc {| sLAV ''S'', sLAV ''C'', sLN ''ns'', sLMV ''pms'' |}
                      ( Hash {| sLMV ''pms'', sLN ''ns'' |} )
               |}
  , Send ''3'' ( Enc {| sLAV ''C'', sLAV ''S'', sLN ''ns'',
                        sLMV ''pms''
                     |}
                     ( Hash {| sLMV ''pms'', sLN ''ns'' |} )
               )
  , Recv ''4'' ( Enc {| sLC ''TT4'', sLMV ''Payload'' |}
                     ( Hash {| sLMV ''pms'', sLN ''ns'' |} )
               )
  ]"

protocol TLS_simple
where "TLS_simple = { C, S }"

locale atomic_TLS_simple_state = atomic_state TLS_simple
locale TLS_simple_state = reachable_state TLS_simple

lemma (in atomic_TLS_simple_state) auto_C_sk_S:
  assumes facts:
    "roleMap r tid0 = Some C"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "SK ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! " SK ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_TLS_simple_state) auto_S_sk_C:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''C'' tid0|) ~: Compromised"
    "SK ( s(|AV ''C'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! " SK ( s(|AV ''C'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_TLS_simple_state) auto_C_sec_pms:
  assumes facts:
    "roleMap r tid0 = Some C"
    "s(|AV ''C'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, C_2) : steps t"
    "LN ''pms'' tid0 : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! " LN ''pms'' tid0 ")
    case C_2_pms note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_C_sk_S intro: event_predOrdI)
  next
    case C_2_pms_1 note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Hash {| LN ''pms'' tid0, s(|MV ''ns'' tid0|) |} ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_3_pms tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Hash {| LN ''pms'' tid0, LN ''ns'' tid1 |} ")
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_TLS_simple_state) auto_S_sec_pms:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''C'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, S_2) : steps t"
    "s(|MV ''pms'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc ( Hash {| LC ''TT2'', LN ''ns'' tid0, s(|AV ''S'' tid0|),
                                 s(|MV ''pms'' tid0|)
                              |}
                       )
                       ( SK ( s(|AV ''C'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_S_sk_C intro: event_predOrdI)
  next
    case (C_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_C_sec_pms intro: event_predOrdI)
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_TLS_simple_state) auto_C_sec_Payload:
  assumes facts:
    "roleMap r tid0 = Some C"
    "s(|AV ''C'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, C_4) : steps t"
    "LN ''Payload'' tid0 : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! " LN ''Payload'' tid0 ")
    case C_4_Payload note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Hash {| LN ''pms'' tid0, s(|MV ''ns'' tid0|) |} ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: auto_C_sec_pms intro: event_predOrdI)
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case (S_3_pms tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', LN ''Payload'' tid0 |}
                         ( PK ( s(|AV ''S'' tid1|) ) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_TLS_simple_state) auto_S_sec_Payload:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''C'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, S_4) : steps t"
    "s(|MV ''Payload'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc ( Hash {| LC ''TT2'', LN ''ns'' tid0, s(|AV ''S'' tid0|),
                                 s(|MV ''pms'' tid0|)
                              |}
                       )
                       ( SK ( s(|AV ''C'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_S_sk_C intro: event_predOrdI)
  next
    case (C_2_enc tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT4'', s(|MV ''Payload'' tid0|) |}
                         ( Hash {| LN ''pms'' tid1, LN ''ns'' tid0 |} ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Hash {| LN ''pms'' tid1, LN ''ns'' tid0 |} ")
        case fake note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: auto_C_sec_pms intro: event_predOrdI)
      qed (insert facts, ((clarsimp, order?))+)?
    next
      case C_4_enc note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: auto_C_sec_Payload intro: event_predOrdI)
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in TLS_simple_state) weak_atomicity:
  "complete (t,r,s) atomicAnn"
proof (cases rule: complete_atomicAnnI[completeness_cases_rule])
  case (S_2_pms t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state TLS_simple t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT1'', ?s'(|MV ''pms'' tid0|) |}
          ( PK ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (S_4_Payload t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state TLS_simple t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT4'', ?s'(|MV ''Payload'' tid0|) |}
          ( Hash {| ?s'(|MV ''pms'' tid0|), LN ''ns'' tid0 |} ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
qed

lemma (in atomic_TLS_simple_state) C_pms_sec:
  assumes facts:
    "roleMap r tid0 = Some C"
    "s(|AV ''C'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, C_4) : steps t"
    "LN ''pms'' tid0 : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis by (fastsimp dest: auto_C_sec_pms intro: event_predOrdI)
qed

lemma (in atomic_TLS_simple_state) S_pms_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''C'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, S_4) : steps t"
    "s(|MV ''pms'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis by (fastsimp dest: auto_S_sec_pms intro: event_predOrdI)
qed

lemma (in atomic_TLS_simple_state) C_Payload_sec:
  assumes facts:
    "roleMap r tid0 = Some C"
    "s(|AV ''C'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, C_4) : steps t"
    "LN ''Payload'' tid0 : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis by (fastsimp dest: auto_C_sec_Payload intro: event_predOrdI)
qed

lemma (in atomic_TLS_simple_state) S_Payload_sec:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''C'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, S_4) : steps t"
    "s(|MV ''Payload'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis by (fastsimp dest: auto_S_sec_Payload intro: event_predOrdI)
qed

lemma (in atomic_TLS_simple_state) S_ni_synch:
  assumes facts:
    "roleMap r tid2 = Some S"
    "s(|AV ''C'' tid2|) ~: Compromised"
    "s(|AV ''S'' tid2|) ~: Compromised"
    "(tid2, S_4) : steps t"
  shows
    "? tid1.
       roleMap r tid1 = Some C &
       s(|AV ''C'' tid2|) = s(|AV ''C'' tid1|) &
       s(|AV ''S'' tid2|) = s(|AV ''S'' tid1|) &
       s(|MV ''Payload'' tid2|) = LN ''Payload'' tid1 &
       s(|MV ''ns'' tid1|) = LN ''ns'' tid2 &
       s(|MV ''pms'' tid2|) = LN ''pms'' tid1"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc ( Hash {| LC ''TT2'', LN ''ns'' tid2, s(|AV ''S'' tid2|),
                                 s(|MV ''pms'' tid2|)
                              |}
                       )
                       ( SK ( s(|AV ''C'' tid2|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_S_sk_C intro: event_predOrdI)
  next
    case (C_2_enc tid3) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT4'', s(|MV ''Payload'' tid2|) |}
                         ( Hash {| LN ''pms'' tid3, LN ''ns'' tid2 |} ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: auto_S_sec_Payload intro: event_predOrdI)
    next
      case C_4_enc note facts = facts this[simplified]
      thus ?thesis by force
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

end