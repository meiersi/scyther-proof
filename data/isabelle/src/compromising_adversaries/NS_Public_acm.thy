(*****************************************************************************
 * ESPL --- an embedded security protocol logic
 *          http://people.inf.ethz.ch/meiersi/espl/
 *
 *   Copyright (c) 2009-2011, Simon Meier, ETH Zurich, Switzerland
 *
 * Extension to compromising adversaries:
 *
 *   Copyright (c) 2010-2011, Martin Schaub, ETH Zurich, Switzerland
 *
 * All rights reserved. See file LICENCE for more information.
 ******************************************************************************)

theory "NS_Public_acm"
imports
  "../ESPLogic"
begin

section{* Security Proofs for a typed version of NSL *}

subsection{* Protocol Specificiation *}

role I
where "I =
  [ 
    Send ''1'' ( PEnc <| sC ''1'', sN ''ni'', sAV ''I'' |>
                      ( sPK ''R'' ))

  , Recv ''2'' ( PEnc <| sC ''2'', sN ''ni'', sMV ''nr'', sAV ''R''
                      |>
                      ( sPK ''I'' ))
  , Send ''3'' ( PEnc <| sC ''3'', sMV ''nr'' |> ( sPK ''R'' ) )
  , Note ''4'' SessKey (PHash (<| sN ''ni'', sMV ''nr'' |>))
  ]"

role R
where "R =
  [
    Recv ''1'' ( PEnc <| sC ''1'', sMV ''ni'', sAV ''I'' |>
                      ( sPK ''R'' ) )
  , Send ''2'' ( PEnc <| sC ''2'', sMV ''ni'', sN ''nr'', sAV ''R''
                      |>
                      ( sPK ''I'' ) )
  , Recv ''3'' ( PEnc <| sC ''3'', sN ''nr'' |> ( sPK ''R'' ))
  , Note ''4'' SessKey (PHash (<| sMV ''ni'', sN ''nr'' |>))
  ]"

protocol ns_public
where "ns_public = { I, R }"

(* TODO remove *)
declare (in ns_public_state) I_4_def[simp]
declare (in ns_public_state) R_4_def[simp]


subsection {* Typing Definition *}
type_invariant auto_msc_typing for ns_public
where "auto_msc_typing = mk_typing
  [ ((R, ''ni''), (SumT (KnownT R_1) (NonceT I ''ni'')))
  , ((I, ''nr''), (SumT (KnownT I_2) (NonceT R ''nr'')))
  ]"

sublocale ns_public_state < auto_msc_typing_state
proof -
  have "(t,r,s) : approx auto_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF auto_msc_typing.monoTyp, completeness_cases_rule])
    case (I_2_nr t r s tid0) 
    note facts = this
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''2'', LN ''ni'' tid0, s(MV ''nr'' tid0),
               s(AV ''R'' tid0)
            |}
            ( PK ( s(AV ''I'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits) | (fastforce intro: event_predOrdI split: if_splits))+)?
  next
    case (R_1_ni t r s tid0)
    note facts = this
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''1'', s(MV ''ni'' tid0), s(AV ''I'' tid0) |}
            ( PK ( s(AV ''R'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits) | (fastforce intro: event_predOrdI split: if_splits))+)?
  qed
  thus "auto_msc_typing_state t r s" by unfold_locales auto
qed

subsection{* Partnering Definition *}

definition
 ns_public_trusted :: "partnering"
where
  "ns_public_trusted q = 
    Id \<union>
    mk_partnering I R 
         {(sN ''ni'',  sMV ''ni'', R_1),
          (sMV ''nr'', sN  ''nr'', R_2),
          (sAV ''I'',  sAV ''I'',  R_1),
          (sAV ''R'',  sAV ''R'',  R_1)} q \<union> 
    mk_partnering R I 
         {(sMV ''ni'', sN  ''ni'', I_1),
          (sN  ''nr'', sMV ''nr'', I_2),
          (sAV ''I'',  sAV ''I'',  I_1),
          (sAV ''R'',  sAV ''R'',  I_1)} q"


lemmas (in ns_public_state) ns_public_trusted_conv = 
  setEqImpTupleIn[OF ns_public_trusted_def, of _ _ "(t,r,s)", simplified]

lemmas (in ns_public_state) ns_public_trustedI[intro!] = ns_public_trusted_conv[THEN iffD2,simplified mk_partnering_conv,simplified]

subsection{* Adversary Compromise Model Definitions *}

definition (in ns_public_state) ADVall :: "tid \<Rightarrow> state set"
where
"ADVall i = acm {LKRothers i, StR i ns_public_trusted, SkR i ns_public_trusted, RNR}"

locale ns_public_state_ADVall =  ns_public_state +
  fixes test :: tid
  assumes compromiseModel [simp,intro!]: "(t,r,s) \<in> ADVall test"
begin
  lemmas allowed_reveals = acm_to_caps[OF compromiseModel[simplified ADVall_def], simplified]
end

section{* Security Proofs *}

subsection{* Origin Proofs *}
lemma (in ns_public_state) I_ni_origin [rule_format]:
  assumes facts:
    "roleMap r test = Some I"
  shows
    "LN ''ni'' test \<in> knows t \<longrightarrow>
     RLKR (s(AV ''I'' test)) \<in> reveals t \<or> 
     RLKR (s(AV ''R'' test)) \<in> reveals t"
   (is "?knows \<longrightarrow> ?origins")
proof
  assume "?knows"
  note_prefix_closed facts = facts this
  thus ?origins
  proof(sources " LN ''ni'' test ")
    case I_1_ni thus ?thesis 
      by(sources "SK (s (AV ''R'' test))")  (auto intro: compr_predOrdI)
  next
    case (R_2_ni tid1) 
    thus ?thesis
    proof(sources "Enc {| LC ''1'', LN ''ni'' test, s(AV ''I'' tid1) |} ( PK ( s(AV ''R'' tid1) ) ) ")
      case I_1_enc
      thus ?thesis
        by(sources "SK (s (AV ''I'' test))") (auto intro: compr_predOrdI)
    qed
  qed
qed

lemma (in ns_public_state) R_nr_origin [rule_format]:
  assumes facts:
    "roleMap r test = Some R"
  shows
    "LN ''nr'' test \<in> knows t \<longrightarrow> 
     RLKR (s(AV ''I'' test)) \<in> reveals t \<or> 
     RLKR (s(AV ''R'' test)) \<in> reveals t"
  (is "?knows \<longrightarrow> ?origins")
proof 
  assume "?knows"
  thus "?origins" using facts
  proof(sources " LN ''nr'' test ")
    case (I_3_nr tid1)
    thus ?thesis
    proof(sources "Enc {| LC ''2'', LN ''ni'' tid1, LN ''nr'' test, s(AV ''R'' tid1) |}( PK ( s(AV ''I'' tid1) ) ) ")
      case R_2_enc
      thus ?thesis
      by(sources "SK (s (AV ''R'' tid1))") (auto intro: compr_predOrdI)
    qed
  next
    case R_2_nr
    thus ?thesis
      by(sources "SK (s (AV ''I'' test))") (auto intro: compr_predOrdI)
  qed
qed

lemma (in ns_public_state) I_nr_origin [rule_format]:
  assumes facts:
    "roleMap r test = Some I"
    "( test, I_2) \<in> steps t"
  shows
    "s(MV ''nr'' test) \<in> knows t \<longrightarrow>
     RLKR (s(AV ''I'' test)) \<in> reveals t \<or> 
     RLKR (s(AV ''R'' test)) \<in> reveals t"
  (is "?knows \<longrightarrow> ?origins")
proof
  assume "?knows"
  note_prefix_closed facts = facts this
  thus ?origins
  proof(sources 
      "Enc {| LC ''2'', LN ''ni'' test, s(MV ''nr'' test), s(AV ''R'' test)|} ( PK ( s(AV ''I'' test) ) ) ")
    case fake
    thus ?thesis
      by(fastforce dest: I_ni_origin intro: event_predOrdI)
  next
    case (R_2_enc tid1')
    thus ?thesis
      by(auto dest: R_nr_origin intro: event_predOrdI) 
  qed
qed

lemma (in ns_public_state) R_ni_origin [rule_format]:
  assumes facts:
    "roleMap r test = Some R"
    "( test, R_3 ) \<in> steps t"
  shows 
    "s(MV ''ni'' test) \<in> knows t \<longrightarrow> 
     RLKR (s(AV ''I'' test)) \<in> reveals t \<or>
     RLKR (s(AV ''R'' test)) \<in> reveals t"
  (is "?knows \<longrightarrow> ?origins")
proof
  assume "?knows"
  note_prefix_closed facts = facts this
  thus "?origins" 
  proof(sources "Enc {| LC ''3'', LN ''nr'' test |} ( PK ( s(AV ''R'' test) ) ) ")
    case fake
    thus ?thesis 
      by (fastforce dest: R_nr_origin intro: event_predOrdI)
  next
    case (I_3_enc tid1) 
    thus ?thesis
    proof(sources "Enc {| LC ''2'', LN ''ni'' tid1, LN ''nr'' test, s(AV ''R'' test)|}( PK ( s(AV ''I'' tid1) ) ) ")
      case fake 
      thus ?thesis
        by(fastforce dest: R_nr_origin intro: event_predOrdI) 
    next
      case R_2_enc
      thus ?thesis 
        by (fastforce dest: I_ni_origin intro: event_predOrdI) 
    qed
  qed
qed

lemma (in ns_public_state) I_sessKey_origin [rule_format]:
assumes facts:
    "roleMap r test = Some I"
    "( test, I_2 ) \<in> steps t"
  shows 
    "Hash \<lbrace> LN ''ni'' test, s(MV ''nr'' test)  \<rbrace> \<in> knows t \<longrightarrow> 
     RLKR (s(AV ''I'' test)) \<in> reveals t \<or>
     RLKR (s(AV ''R'' test)) \<in> reveals t \<or> 
     (\<exists> tid1. (test,tid1) \<in> ns_public_trusted (t,r,s) \<and> RCompr SessKey tid1 \<in> reveals t)"
  (is "?knows \<longrightarrow> ?origins")
proof
  assume "?knows"
  note_prefix_closed facts = facts this
  thus "?origins"
  proof(sources "Hash \<lbrace>LN ''ni'' test, s (MV ''nr'' test)\<rbrace>")
    case fake
    thus ?thesis
      by(fastforce dest: I_ni_origin intro: event_predOrdI)
  next
    case I_4_hash
    thus ?thesis
      by (auto intro: compr_predOrdI)
  next
    case (R_4_hash tid1)
    thus ?thesis
    proof(sources "Enc \<lbrace>LC ''2'', LN ''ni'' test, LN ''nr'' tid1, s (AV ''R'' test)\<rbrace>
       (PK (s (AV ''I'' test)))")
      case fake
      thus ?thesis
        by(fastforce dest: I_ni_origin intro: event_predOrdI)
    next
      case R_2_enc
      thus ?thesis
        by (auto intro: compr_predOrdI)
    qed
  qed
qed

lemma (in ns_public_state) R_sessKey_origin [rule_format]:
assumes facts:
    "roleMap r test = Some R"
    "( test, R_3 ) \<in> steps t"
  shows 
    "Hash \<lbrace> s(MV ''ni'' test), LN ''nr'' test \<rbrace> \<in> knows t \<longrightarrow> 
     RLKR (s(AV ''I'' test)) \<in> reveals t \<or>
     RLKR (s(AV ''R'' test)) \<in> reveals t \<or> 
     (\<exists> tid1. (test,tid1) \<in> ns_public_trusted (t,r,s) \<and> RCompr SessKey tid1 \<in> reveals t)"
  (is "?knows \<longrightarrow> ?origins")
proof
  assume "?knows"
  note_prefix_closed facts = facts this
  thus "?origins"
  proof(sources "Hash \<lbrace>s (MV ''ni'' test), LN ''nr'' test\<rbrace>")
    case fake
    thus ?thesis
      by(fastforce dest: R_nr_origin intro: event_predOrdI)
  next
    case R_4_hash
    thus ?thesis
      by (auto intro: compr_predOrdI)
  next
    case (I_4_hash tid1)
    thus ?thesis
    proof(sources "Enc \<lbrace>LC ''2'', LN ''ni'' tid1, LN ''nr'' test, s (AV ''R'' tid1)\<rbrace>
       (PK (s (AV ''I'' tid1)))")
      case fake
      thus ?thesis
        by(fastforce dest: R_nr_origin intro: event_predOrdI)
    next
      case R_2_enc
      thus ?thesis
        by (auto intro: compr_predOrdI)
    qed
  qed
qed


subsection{* Secrecy Proofs *}

lemma (in ns_public_state_ADVall) I_ni_secrecy:
  assumes facts:
    "roleMap r test = Some I"
    "LN ''ni'' test \<in> knows t"
  shows "False"
using facts
by(insert I_ni_origin, fastforce dest!: allowed_reveals)

lemma (in ns_public_state_ADVall) R_nr_secrecy:
  assumes facts:
    "roleMap r test = Some R"
    "LN ''nr'' test \<in> knows t"
  shows "False"
using facts
by(insert R_nr_origin, fastforce dest!: allowed_reveals)

lemma (in ns_public_state_ADVall) I_nr_secrecy:
  assumes facts:
    "roleMap r test = Some I"
    "( test, I_2 ) \<in> steps t"
    "s(MV ''nr'' test) \<in>  knows t"
  shows "False"
using facts
by(insert I_nr_origin, fastforce dest!: allowed_reveals)


lemma (in ns_public_state_ADVall) R_ni_secrecy:
  assumes facts:
    "roleMap r test = Some R"
    "( test, R_3 ) \<in> steps t"
    "s(MV ''ni'' test) \<in> knows t"
  shows "False"
using facts
by(insert R_ni_origin, fastforce dest!: allowed_reveals)

lemma (in ns_public_state_ADVall) I_sessKey_secrecy:
  assumes facts:
    "roleMap r test = Some I"
    "( test, I_2 ) \<in> steps t"
    "Hash \<lbrace> LN ''ni'' test, s(MV ''nr'' test)  \<rbrace> \<in> knows t"
  shows "False"
using facts
apply - 
apply(frule I_sessKey_origin, safe)
apply(drule allowed_reveals, clarsimp)+
done

lemma (in ns_public_state_ADVall) R_sessKey_secrecy:
  assumes facts:
    "roleMap r test = Some R"
    "( test, R_3 ) \<in> steps t"
    "Hash \<lbrace> s(MV ''ni'' test), LN ''nr'' test \<rbrace> \<in> knows t"
  shows "False"
using facts
apply - 
apply(frule R_sessKey_origin, safe)
apply(drule allowed_reveals, clarsimp)+
done


subsection{* Authentication Proofs *}

lemma (in ns_public_state_ADVall) I_ni_synch:
  assumes facts:
    "roleMap r test = Some I"
    "( test, I_3 ) \<in> steps t"
  shows
    "(?  tid2.
        roleMap r tid2 = Some R &
        s(AV ''I'' test) = s(AV ''I'' tid2) &
        s(AV ''R'' test) = s(AV ''R'' tid2) &
        LN ''ni'' test = s(MV ''ni'' tid2) &
        s(MV ''nr'' test) = LN ''nr'' tid2 &
        St( test, I_1 ) \<prec> St( tid2, R_1 ) &
        St( tid2, R_1 ) \<prec> St( tid2, R_2 ) &
        St( tid2, R_2 ) \<prec> St( test, I_2 ) &
        St( test, I_2 ) \<prec> St( test, I_3 ))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis
  proof(sources "Enc {| LC ''2'', LN ''ni'' test, s(MV ''nr'' test),s(AV ''R'' test)|}( PK ( s(AV ''I'' test) ) ) ")
    case fake
    thus ?thesis  by (auto dest: I_ni_secrecy intro: event_predOrdI)
  next
    case (R_2_enc tid2) 
    thus ?thesis
    proof(sources "Enc {| LC ''1'', LN ''ni'' test, s(AV ''I'' test) |}( PK ( s(AV ''R'' test) ) ) ")
      case fake 
      thus ?thesis  by (auto dest: I_ni_secrecy intro: event_predOrdI)
    next
      case I_1_enc
      thus ?thesis
        by(fastforce)
    qed
  qed
qed

lemma (in ns_public_state_ADVall) R_ni_synch:
  assumes facts:
    "roleMap r test = Some R"
    "( test, R_3 ) \<in> steps t"
  shows
    "(?  tid2.
        roleMap r tid2 = Some I &
        s(AV ''I'' test) = s(AV ''I'' tid2) &
        s(AV ''R'' test) = s(AV ''R'' tid2) &
        s(MV ''ni'' test) = LN ''ni'' tid2 &
        LN ''nr'' test = s(MV ''nr'' tid2) &
        St( tid2, I_1 ) \<prec> St( test, R_1) &
        St( test, R_1 ) \<prec> St( test, R_2) &
        St( test, R_2 ) \<prec> St( tid2, I_2 ) &
        St( tid2, I_2 ) \<prec> St( tid2, I_3 ) &
        St( tid2, I_3 ) \<prec> St( test, R_3 ))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis
  proof(sources "Enc {| LC ''1'', s(MV ''ni'' test), s(AV ''I'' test) |}( PK ( s(AV ''R'' test) ) ) ")
    case (I_1_enc tid2) 
    thus ?thesis
    proof(sources "Enc {| LC ''3'', LN ''nr'' test |} ( PK ( s(AV ''R'' test) ) ) ")
      case fake
      thus ?thesis by (auto dest: R_nr_secrecy intro: event_predOrdI) 
    next
      case (I_3_enc tid3) 
      thus ?thesis 
      proof(sources "Enc {| LC ''2'', LN ''ni'' tid3, LN ''nr'' test, s(AV ''R'' test)|}( PK ( s(AV ''I'' tid3) ) ) ")
        case fake
        thus ?thesis by (auto dest: R_nr_secrecy intro: event_predOrdI)
      next
        case R_2_enc
        thus ?thesis by (auto intro: event_predOrdI)
      qed
    qed
  next
    case fake
    thus ?thesis
      by (auto dest: R_ni_secrecy intro: event_predOrdI)
  qed
qed


end
