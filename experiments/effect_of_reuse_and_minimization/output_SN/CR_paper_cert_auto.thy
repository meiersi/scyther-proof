theory CR_paper_cert_auto
imports
  "../ESPLogic"
begin

role C
where "C =
  [ Send ''1'' ( Enc ( sLN ''n'' ) ( sPK ''S'' ) )
  , Recv ''2'' ( Hash ( sLN ''n'' ) )
  ]"

role S
where "S =
  [ Recv ''1'' ( Enc ( sLNV ''n'' ) ( sPK ''S'' ) )
  , Send ''2'' ( Hash ( sLNV ''n'' ) )
  ]"

protocol CR
where "CR = { C, S }"

locale atomic_CR_state = atomic_state CR
locale CR_state = reachable_state CR

lemma (in atomic_CR_state) C_sk_S_secrecy:
  assumes facts:
    "roleMap r tid0 = Some C"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "SK ( s(|AV ''S'' tid0|) ) : knows t"
  shows "False"
using facts proof(sources! " SK ( s(|AV ''S'' tid0|) ) ")
qed (insert facts, ((clarsimp, order?))+)?

lemma (in atomic_CR_state) C_n_secrecy:
  assumes facts:
    "roleMap r tid0 = Some C"
    "s(|AV ''S'' tid0|) ~: Compromised"
    "LN ''n'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''n'' tid0 ")
  case C_1_n note facts = facts this[simplified]
  thus ?thesis proof(sources! " SK ( s(|AV ''S'' tid0|) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_CR_state) C_ni_synch:
  assumes facts:
    "roleMap r tid1 = Some C"
    "s(|AV ''S'' tid1|) ~: Compromised"
    "(tid1, C_2) : steps t"
  shows
    "? tid2.
       roleMap r tid2 = Some S &
       s(|AV ''S'' tid2|) = s(|AV ''S'' tid1|) &
       s(|NV ''n'' tid2|) = LN ''n'' tid1 &
       predOrd t (St(tid1, C_1)) (St(tid2, S_1)) &
       predOrd t (St(tid2, S_2)) (St(tid1, C_2)) &
       predOrd t (St(tid2, S_1)) (St(tid2, S_2))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! " Hash ( LN ''n'' tid1 ) ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''n'' tid1 ")
      case C_1_n note facts = facts this[simplified]
      thus ?thesis proof(sources! " SK ( s(|AV ''S'' tid1|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    qed
  next
    case (S_2_hash tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc ( LN ''n'' tid1 ) ( PK ( s(|AV ''S'' tid2|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''n'' tid1 ")
        case C_1_n note facts = facts this[simplified]
        thus ?thesis proof(sources! " SK ( s(|AV ''S'' tid1|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed
    next
      case C_1_enc note facts = facts this[simplified]
      thus ?thesis by force
    qed
  qed
qed

lemma (in CR_state) weak_atomicity:
  "complete (t,r,s) atomicAnn"
proof (cases rule: complete_atomicAnnI[completeness_cases_rule])
  case (S_1_n t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state CR t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc ( ?s'(|NV ''n'' tid0|) ) ( PK ( ?s'(|AV ''S'' tid0|) ) ) ")
  qed (insert facts, ((fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
qed

role C2
where "C2 =
  [ Send ''1'' ( Enc {| sLAV ''C2'', sLN ''n'' |} ( sPK ''S2'' ) )
  , Recv ''2'' ( Hash {| sLAV ''C2'', sLN ''n'' |} )
  ]"

role S2
where "S2 =
  [ Recv ''1'' ( Enc {| sLAV ''C2'', sLNV ''n'' |} ( sPK ''S2'' ) )
  , Send ''2'' ( Hash {| sLAV ''C2'', sLNV ''n'' |} )
  ]"

protocol CR2
where "CR2 = { C2, S2 }"

locale atomic_CR2_state = atomic_state CR2
locale CR2_state = reachable_state CR2

lemma (in CR2_state) weak_atomicity:
  "complete (t,r,s) atomicAnn"
proof (cases rule: complete_atomicAnnI[completeness_cases_rule])
  case (S2_1_n t r s tid0 \<alpha>) note facts = this
  then interpret state: atomic_state CR2 t r s
    by unfold_locales assumption+
  let ?s' = "extendS s \<alpha>"
  show ?case using facts
  proof(sources! "
      Enc {| ?s'(|AV ''C2'' tid0|), ?s'(|NV ''n'' tid0|) |}
          ( PK ( ?s'(|AV ''S2'' tid0|) ) ) ")
  qed (insert facts, ((fastsimp simp: atomicAnn_def dest: state.extract_knows_hyps))+)?
qed

lemma (in atomic_CR2_state) C_n_secrecy:
  assumes facts:
    "roleMap r tid0 = Some C2"
    "s(|AV ''S2'' tid0|) ~: Compromised"
    "LN ''n'' tid0 : knows t"
  shows "False"
using facts proof(sources! " LN ''n'' tid0 ")
  case C2_1_n note facts = facts this[simplified]
  thus ?thesis proof(sources! " SK ( s(|AV ''S2'' tid0|) ) ")
  qed (insert facts, ((clarsimp, order?))+)?
qed

lemma (in atomic_CR2_state) C_ni_synch:
  assumes facts:
    "roleMap r tid1 = Some C2"
    "s(|AV ''S2'' tid1|) ~: Compromised"
    "(tid1, C2_2) : steps t"
  shows
    "? tid2.
       roleMap r tid2 = Some S2 &
       s(|AV ''C2'' tid2|) = s(|AV ''C2'' tid1|) &
       s(|AV ''S2'' tid2|) = s(|AV ''S2'' tid1|) &
       s(|NV ''n'' tid2|) = LN ''n'' tid1 &
       predOrd t (St(tid1, C2_1)) (St(tid2, S2_1)) &
       predOrd t (St(tid2, S2_2)) (St(tid1, C2_2)) &
       predOrd t (St(tid2, S2_1)) (St(tid2, S2_2))"
proof -
  note_prefix_closed facts = facts note facts = this
  thus ?thesis proof(sources! "
                   Hash {| s(|AV ''C2'' tid1|), LN ''n'' tid1 |} ")
    case fake note facts = facts this[simplified]
    thus ?thesis proof(sources! " LN ''n'' tid1 ")
      case C2_1_n note facts = facts this[simplified]
      thus ?thesis proof(sources! " SK ( s(|AV ''S2'' tid1|) ) ")
      qed (insert facts, ((clarsimp, order?))+)?
    qed
  next
    case (S2_2_hash tid2) note facts = facts this[simplified]
    thus ?thesis proof(sources! "
                     Enc {| s(|AV ''C2'' tid1|), LN ''n'' tid1 |}
                         ( PK ( s(|AV ''S2'' tid2|) ) ) ")
      case fake note facts = facts this[simplified]
      thus ?thesis proof(sources! " LN ''n'' tid1 ")
        case C2_1_n note facts = facts this[simplified]
        thus ?thesis proof(sources! " SK ( s(|AV ''S2'' tid1|) ) ")
        qed (insert facts, ((clarsimp, order?))+)?
      qed
    next
      case C2_1_enc note facts = facts this[simplified]
      thus ?thesis by force
    qed
  qed
qed

end