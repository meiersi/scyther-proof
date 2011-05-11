theory "Yahalom2_cert_auto"
imports
  "../ESPLogic"
begin

role I
where "I =
  [ Send ''1'' {| sLAV ''I'', sLN ''ni'' |}
  , Recv ''3'' {| sLMV ''nr'',
                  Enc {| sLC ''TT31'', sLAV ''R'', sLMV ''kir'', sLN ''ni'' |}
                      ( sK ''I'' ''S'' ),
                  sLMV ''Ticket''
               |}
  , Send ''4'' {| sLMV ''Ticket'',
                  Enc {| sLC ''TT4'', sLMV ''nr'' |} ( sLMV ''kir'' )
               |}
  ]"

role R
where "R =
  [ Recv ''1'' {| sLAV ''I'', sLMV ''ni'' |}
  , Send ''2'' {| sLAV ''R'', sLN ''nr'',
                  Enc {| sLC ''TT1'', sLAV ''I'', sLMV ''ni'' |} ( sK ''R'' ''S'' )
               |}
  , Recv ''4'' {| Enc {| sLC ''TT32'', sLAV ''I'', sLMV ''kir'',
                         sLN ''nr''
                      |}
                      ( sK ''R'' ''S'' ),
                  Enc {| sLC ''TT4'', sLN ''nr'' |} ( sLMV ''kir'' )
               |}
  ]"

role S
where "S =
  [ Recv ''2'' {| sLAV ''R'', sLMV ''nr'',
                  Enc {| sLC ''TT1'', sLAV ''I'', sLMV ''ni'' |} ( sK ''R'' ''S'' )
               |}
  , Send ''3'' {| sLMV ''nr'',
                  Enc {| sLC ''TT31'', sLAV ''R'', sLN ''kir'', sLMV ''ni'' |}
                      ( sK ''I'' ''S'' ),
                  Enc {| sLC ''TT32'', sLAV ''I'', sLN ''kir'', sLMV ''nr'' |}
                      ( sK ''R'' ''S'' )
               |}
  ]"

protocol yahalom_paulson
where "yahalom_paulson = { I, R, S }"

locale atomic_yahalom_paulson_state = atomic_state yahalom_paulson
locale yahalom_paulson_state = reachable_state yahalom_paulson

lemma (in atomic_yahalom_paulson_state) auto_ni:
  assumes facts:
    "roleMap r tid0 = Some I"
    "LN ''ni'' tid0 : knows t"
  shows "predOrd t (St(tid0, I_1)) (Ln(LN ''ni'' tid0))"
using facts proof(sources! " LN ''ni'' tid0 ")
  case I_1_ni note facts = facts this[simplified]
  thus ?thesis by force
next
  case (S_3_ni tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|AV ''I'' tid1|), LN ''ni'' tid0 |}
                       ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_yahalom_paulson_state) auto_nr:
  assumes facts:
    "roleMap r tid0 = Some R"
    "LN ''nr'' tid0 : knows t"
  shows "predOrd t (St(tid0, R_2)) (Ln(LN ''nr'' tid0))"
using facts proof(sources! " LN ''nr'' tid0 ")
  case R_2_nr note facts = facts this[simplified]
  thus ?thesis by force
next
  case (S_3_ni tid1) note facts = facts this[simplified]
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT1'', s(|AV ''I'' tid1|), LN ''nr'' tid0 |}
                       ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_yahalom_paulson_state) auto_I_k_I_S:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_yahalom_paulson_state) auto_I_k_R_S:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_yahalom_paulson_state) auto_R_k_R_S:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_yahalom_paulson_state) auto_S_k_I_S:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_yahalom_paulson_state) auto_S_k_R_S:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! "
                K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_yahalom_paulson_state) auto_S_sec_kir:
  assumes facts:
    "roleMap r tid0 = Some S"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, S_3) : steps t"
    "LN ''kir'' tid0 : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! " LN ''kir'' tid0 ")
    case S_3_kir note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_S_k_I_S intro: event_predOrdI)
  next
    case (S_3_ni tid1) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', s(|AV ''I'' tid1|), LN ''kir'' tid0 |}
                         ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
    qed (insert facts, ((clarsimp, order?))+)?
  next
    case S_3_kir_1 note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_S_k_R_S intro: event_predOrdI)
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_yahalom_paulson_state) auto_I_sec_kir:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, I_3) : steps t"
    "s(|MV ''kir'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT31'', s(|AV ''R'' tid0|), s(|MV ''kir'' tid0|),
                          LN ''ni'' tid0
                       |}
                       ( K ( s(|AV ''I'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_I_k_I_S intro: event_predOrdI)
  next
    case (S_3_enc tid1) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_S_sec_kir intro: event_predOrdI)
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_yahalom_paulson_state) auto_R_sec_kir:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, R_4) : steps t"
    "s(|MV ''kir'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT32'', s(|AV ''I'' tid0|), s(|MV ''kir'' tid0|),
                          LN ''nr'' tid0
                       |}
                       ( K ( s(|AV ''R'' tid0|) ) ( s(|AV ''S'' tid0|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_R_k_R_S intro: event_predOrdI)
  next
    case (S_3_enc tid1) note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_S_sec_kir intro: event_predOrdI)
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in yahalom_paulson_state) weak_atomicity:
  "complete (t,r,s) atomicAnn"
proof (cases rule: complete_atomicAnnI[completeness_cases_rule])
  case (I_3_Ticket t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state yahalom_paulson t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  by (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps)
next
  case (I_3_kir t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state yahalom_paulson t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT31'', ?s'(|AV ''R'' tid0|), ?s'(|MV ''kir'' tid0|),
             LN ''ni'' tid0
          |}
          ( K ( ?s'(|AV ''I'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (I_3_nr t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state yahalom_paulson t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  by (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps)
next
  case (R_1_ni t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state yahalom_paulson t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  by (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps)
next
  case (R_4_kir t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state yahalom_paulson t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT32'', ?s'(|AV ''I'' tid0|), ?s'(|MV ''kir'' tid0|),
             LN ''nr'' tid0
          |}
          ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (S_2_ni t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state yahalom_paulson t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| LC ''TT1'', ?s'(|AV ''I'' tid0|), ?s'(|MV ''ni'' tid0|) |}
          ( K ( ?s'(|AV ''R'' tid0|) ) ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((clarsimp, order?) | (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
next
  case (S_2_nr t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state yahalom_paulson t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  by (fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps)
qed

lemma (in atomic_yahalom_paulson_state) I_kir_sec:
  assumes facts:
    "roleMap r tid0 = Some I"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, I_3) : steps t"
    "s(|MV ''kir'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis by (fastsimp dest: auto_I_sec_kir intro: event_predOrdI)
qed

lemma (in atomic_yahalom_paulson_state) R_kir_sec:
  assumes facts:
    "roleMap r tid0 = Some R"
    "s(|AV ''I'' tid0|) ~: Compromised"
    "s(|AV ''R'' tid0|) ~: Compromised"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "(tid0, R_4) : steps t"
    "s(|MV ''kir'' tid0|) : knows t"
  shows "False"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis by (fastsimp dest: auto_R_sec_kir intro: event_predOrdI)
qed

lemma (in atomic_yahalom_paulson_state) I_ni_synch:
  assumes facts:
    "roleMap r tid1 = Some I"
    "s(|AV ''I'' tid1|) ~: Compromised"
    "s(|AV ''R'' tid1|) ~: Compromised"
    "s(|AV ''S'' tid1|) ~: Compromised"
    "(tid1, I_3) : steps t"
  shows
    "? tid2 tid3.
       roleMap r tid2 = Some R &
       roleMap r tid3 = Some S &
       s(|AV ''I'' tid2|) = s(|AV ''I'' tid1|) &
       s(|AV ''I'' tid3|) = s(|AV ''I'' tid1|) &
       s(|AV ''R'' tid2|) = s(|AV ''R'' tid1|) &
       s(|AV ''R'' tid3|) = s(|AV ''R'' tid1|) &
       s(|MV ''kir'' tid1|) = LN ''kir'' tid3 &
       s(|MV ''ni'' tid2|) = LN ''ni'' tid1 &
       s(|MV ''ni'' tid3|) = LN ''ni'' tid1 &
       predOrd t (St(tid1, I_1)) (St(tid2, R_1)) &
       predOrd t (St(tid2, R_2)) (St(tid3, S_2)) &
       predOrd t (St(tid2, R_1)) (St(tid2, R_2)) &
       predOrd t (St(tid3, S_3)) (St(tid1, I_3)) &
       predOrd t (St(tid3, S_2)) (St(tid3, S_3))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT31'', s(|AV ''R'' tid1|), s(|MV ''kir'' tid1|),
                          LN ''ni'' tid1
                       |}
                       ( K ( s(|AV ''I'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_I_k_I_S intro: event_predOrdI)
  next
    case (S_3_enc tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT1'', s(|AV ''I'' tid1|), LN ''ni'' tid1 |}
                         ( K ( s(|AV ''R'' tid1|) ) ( s(|AV ''S'' tid1|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: auto_I_k_R_S intro: event_predOrdI)
    next
      case (R_2_enc tid3) note facts = facts this[simplified]
      have f1: "roleMap r tid1 = Some I" using facts by (auto intro: event_predOrdI)
      have f2: "LN ''ni'' tid1 : knows t" using facts by (auto intro: event_predOrdI)
      note facts = facts auto_ni[OF f1 f2, simplified]
      thus ?thesis by force
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_yahalom_paulson_state) R_ni_synch:
  assumes facts:
    "roleMap r tid2 = Some R"
    "s(|AV ''I'' tid2|) ~: Compromised"
    "s(|AV ''R'' tid2|) ~: Compromised"
    "s(|AV ''S'' tid2|) ~: Compromised"
    "(tid2, R_4) : steps t"
  shows
    "? tid1 tid3.
       roleMap r tid1 = Some I &
       roleMap r tid3 = Some S &
       s(|AV ''I'' tid2|) = s(|AV ''I'' tid1|) &
       s(|AV ''I'' tid3|) = s(|AV ''I'' tid1|) &
       s(|AV ''R'' tid2|) = s(|AV ''R'' tid1|) &
       s(|AV ''R'' tid3|) = s(|AV ''R'' tid1|) &
       s(|MV ''kir'' tid1|) = LN ''kir'' tid3 &
       s(|MV ''kir'' tid2|) = LN ''kir'' tid3 &
       s(|MV ''nr'' tid1|) = LN ''nr'' tid2 &
       s(|MV ''nr'' tid3|) = LN ''nr'' tid2 &
       predOrd t (St(tid1, I_4)) (St(tid2, R_4)) &
       predOrd t (St(tid1, I_3)) (St(tid1, I_4)) &
       predOrd t (St(tid2, R_2)) (St(tid3, S_2)) &
       predOrd t (St(tid2, R_1)) (St(tid2, R_2)) &
       predOrd t (St(tid3, S_3)) (St(tid1, I_3)) &
       predOrd t (St(tid3, S_2)) (St(tid3, S_3))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Enc {| LC ''TT32'', s(|AV ''I'' tid2|), s(|MV ''kir'' tid2|),
                          LN ''nr'' tid2
                       |}
                       ( K ( s(|AV ''R'' tid2|) ) ( s(|AV ''S'' tid2|) ) ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis by (fastsimp dest: auto_R_k_R_S intro: event_predOrdI)
  next
    case (S_3_enc tid3) note facts = facts this[simplified]
    have f1: "roleMap r tid2 = Some R" using facts by (auto intro: event_predOrdI)
    have f2: "LN ''nr'' tid2 : knows t" using facts by (auto intro: event_predOrdI)
    note facts = facts auto_nr[OF f1 f2, simplified]
    thus ?thesis proof(sources! "
                     Enc {| LC ''TT4'', LN ''nr'' tid2 |} ( LN ''kir'' tid3 ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis by (fastsimp dest: auto_S_sec_kir intro: event_predOrdI)
    next
      case (I_4_enc tid4) note facts = facts this[simplified]
      thus ?thesis proof(sources! "
                       Enc {| LC ''TT31'', s(|AV ''R'' tid4|), LN ''kir'' tid3,
                              LN ''ni'' tid4
                           |}
                           ( K ( s(|AV ''I'' tid4|) ) ( s(|AV ''S'' tid4|) ) ) ")
        case fake note facts = facts this[simplified]
        thus ?thesis by (fastsimp dest: auto_S_sec_kir intro: event_predOrdI)
      next
        case S_3_enc note facts = facts this[simplified]
        thus ?thesis by force
      qed (insert facts, ((clarsimp, order?))+)?
    qed (insert facts, ((clarsimp, order?))+)?
  qed (insert facts, ((clarsimp, order?))+)?
qed

end