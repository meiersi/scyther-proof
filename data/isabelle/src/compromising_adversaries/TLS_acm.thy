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

theory "TLS_acm"
imports
  "../ESPLogic"
begin

section{* Security Proofs for the TLS protocol *}

subsection{* Protocol Specificiation *}

role C
where "C =
  [ 
    Note ''0'' RandGen <| sN ''nc'',  sN ''sid'', sN ''pc'' |>
  , Note ''1'' State <| sN ''nc'', sN ''sid'', sN ''pc'' |>
  , Send ''2'' <| sAV ''C'', sN ''nc'', sN ''sid'', sN ''pc'' |> 
  , Note ''3'' State <| sN ''nc'', sN ''sid'', sN ''pc'' |>
  , Recv ''4'' <| sMV ''ns'', sN ''sid'', sMV ''ps'' |>
  , Note ''5'' State <| sN ''nc'', sN ''sid'', sN ''pc'', sN ''pms'', sMV ''ns'', sMV ''ps'' |>
  , Send ''6'' <| PEnc <| sC ''TT0'', sN ''pms'' |> ( sPK ''S'' ),
                  PEnc <| sC ''TT1'',
                          PHash <| sC ''TT2'', sMV ''ns'', sAV ''S'', sN ''pms'' |>
                       |>
                       ( sSK ''C'' ),
                  PEnc <| sC ''TT3'', sN ''sid'',
                          PHash <| sC ''TT4'', sC ''PRF'', sN ''pms'', sN ''nc'', sMV ''ns''
                                |>,
                          sN ''nc'', sN ''pc'', sAV ''C'', sMV ''ns'', sMV ''ps'', sAV ''S''
                       |>
                       ( PHash <| sC ''clientKey'', sN ''nc'', sMV ''ns'',
                                  PHash <| sC ''TT4'', sC ''PRF'', sN ''pms'', sN ''nc'', sMV ''ns''
                                        |>
                               |>
                       )
                 |>
  , Note ''7'' State <| sN ''nc'', sN ''sid'', sN ''pc'', sN ''pms'', sMV ''ns'', sMV ''ps'' |>
  , Recv ''8'' ( PEnc <| sC ''TT3'', sN ''sid'',
                         PHash <| sC ''TT4'', sC ''PRF'', sN ''pms'', sN ''nc'', sMV ''ns''
                               |>,
                         sN ''nc'', sN ''pc'', sAV ''C'', sMV ''ns'', sMV ''ps'', sAV ''S''
                      |>
                      ( PHash <| sC ''serverKey'', sN ''nc'', sMV ''ns'',
                                 PHash <| sC ''TT4'', sC ''PRF'', sN ''pms'', sN ''nc'', sMV ''ns''
                                       |>
                              |>
                      )
               )
  , Note ''9'' SessKey  <| PHash <| sC ''serverKey'', sN ''nc'', sMV ''ns'',
                                 PHash <| sC ''TT4'', sC ''PRF'', sN ''pms'', sN ''nc'', sMV ''ns''
                                       |>
                              |>,
                           
                           PHash <| sC ''clientKey'', sN ''nc'', sMV ''ns'',
                                  PHash <| sC ''TT4'', sC ''PRF'', sN ''pms'', sN ''nc'', sMV ''ns''
                                        |>
                               |>
                         |>
  ]"

role S
where "S =
  [
    Recv ''1'' <| sAV ''C'', sMV ''nc'', sMV ''sid'', sMV ''pc'' |>
  , Note ''0'' RandGen  <| sN ''ns'', sN ''ps'' |>
  , Note ''2'' State <| sN ''ns'', sMV ''sid'', sN ''ps'', sMV ''nc'', sMV ''sid'', sMV ''pc'' |>
  , Send ''3'' <| sN ''ns'', sMV ''sid'', sN ''ps'' |>
  , Note ''4'' State <| sN ''ns'', sMV ''sid'', sN ''ps'', sMV ''nc'', sMV ''sid'', sMV ''pc'' |>
  , Recv ''5'' <| PEnc <| sC ''TT0'', sMV ''pms'' |> ( sPK ''S'' ),
                  PEnc <| sC ''TT1'',
                          PHash <| sC ''TT2'', sN ''ns'', sAV ''S'', sMV ''pms'' |>
                       |>
                       ( sSK ''C'' ),
                  PEnc <| sC ''TT3'', sMV ''sid'',
                          PHash <| sC ''TT4'', sC ''PRF'', sMV ''pms'', sMV ''nc'', sN ''ns''
                                |>,
                          sMV ''nc'', sMV ''pc'', sAV ''C'', sN ''ns'', sN ''ps'', sAV ''S''
                       |>
                       ( PHash <| sC ''clientKey'', sMV ''nc'', sN ''ns'',
                                  PHash <| sC ''TT4'', sC ''PRF'', sMV ''pms'', sMV ''nc'',
                                           sN ''ns''
                                        |>
                               |>
                       )
               |>
  , Note ''6'' State <| sMV ''pms'', sN ''ns'', sMV ''sid'', sN ''ps'', sMV ''nc'', sMV ''sid'', sMV ''pc'' |>
  , Send ''7'' ( PEnc <| sC ''TT3'', sMV ''sid'',
                         PHash <| sC ''TT4'', sC ''PRF'', sMV ''pms'', sMV ''nc'', sN ''ns''
                               |>,
                         sMV ''nc'', sMV ''pc'', sAV ''C'', sN ''ns'', sN ''ps'', sAV ''S''
                      |>
                      ( PHash <| sC ''serverKey'', sMV ''nc'', sN ''ns'',
                                 PHash <| sC ''TT4'', sC ''PRF'', sMV ''pms'', sMV ''nc'', sN ''ns''
                                       |>
                              |>
                      )
               )
  , Note ''8'' SessKey <| PHash <| sC ''serverKey'', sMV ''nc'', sN ''ns'',
                                 PHash <| sC ''TT4'', sC ''PRF'', sMV ''pms'', sMV ''nc'', sN ''ns''
                                       |>
                              |>,
                          PHash <| sC ''clientKey'', sMV ''nc'', sN ''ns'',
                                  PHash <| sC ''TT4'', sC ''PRF'', sMV ''pms'', sMV ''nc'',
                                           sN ''ns''
                                        |>
                               |>
                        |>
                         
  ]"

protocol TLS
where "TLS = { C, S }"

subsection {* Typing Definition *}
type_invariant auto_msc_typing for TLS
where "auto_msc_typing = mk_typing
  [ ((S, ''nc''), (KnownT S_1))
  , ((C, ''ns''), (KnownT C_4))
  , ((S, ''pc''), (KnownT S_1))
  , ((S, ''pms''), (SumT (KnownT S_5) (NonceT C ''pms'')))
  , ((C, ''ps''), (KnownT C_4))
  , ((S, ''sid''), (KnownT S_1))
  ]"

sublocale TLS_state < auto_msc_typing_state
proof -
  have "(t,r,s) : approx auto_msc_typing"
  proof(cases rule: reachable_in_approxI_ext
        [OF auto_msc_typing.monoTyp, completeness_cases_rule])
    case (C_4_ns t r s tid0) note facts = this
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (C_4_ps t r s tid0) note facts = this
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (S_1_nc t r s tid0) note facts = this
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (S_1_pc t r s tid0) note facts = this
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (S_1_sid t r s tid0) note facts = this
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    by (fastforce intro: event_predOrdI split: if_splits)
  next
    case (S_5_pms t r s tid0) note facts = this
    then interpret state: auto_msc_typing_state t r s
      by unfold_locales auto
    show ?case using facts
    proof(sources! "
        Enc {| LC ''TT0'', s(MV ''pms'' tid0) |}
            ( PK ( s(AV ''S'' tid0) ) ) ")
    qed (insert facts, ((fastforce intro: event_predOrdI split: if_splits) | (fastforce intro: event_predOrdI split: if_splits))+)?
  qed
  thus "auto_msc_typing_state t r s" by unfold_locales auto
qed


(* TODO remove *)
declare (in TLS_state) C_1_def[simp]
declare (in TLS_state) C_3_def[simp]
declare (in TLS_state) C_5_def[simp]
declare (in TLS_state) C_7_def[simp]
declare (in TLS_state) C_9_def[simp]
declare (in TLS_state) S_2_def[simp]
declare (in TLS_state) S_4_def[simp]
declare (in TLS_state) S_6_def[simp]
declare (in TLS_state) S_8_def[simp]
declare (in TLS_state) C_0_def[simp]
declare (in TLS_state) S_0_def[simp]

subsection{* Partnering Definition *}

text{* 
Strongest possible partnering definition:
- Direction C to S is trivial, since all possible variables of either C or S are used.
- For direction S to C it is only a subset of variables:
  Assume a thread tid1 sends C,nc,sid,pc and the adversary already knows nc'\<noteq>nc, ps'\<noteq>ps, pc'\<noteq>pc and sid'\<noteq>sid. Then the test thread receives C,nc'sid',pc' and sends ns,sid',ps. Now the partnering in both directions is broken. However the adversary can bring thread tid1 to receive ns,sid,pc', state compromise him to receive pms and then use the signed message send in the next client step to trick the test thread of accepting pms. All other messages from C_6 can be faked if pms is known!.
*}

definition
  TLS_trusted :: "partnering"
where
  "TLS_trusted q = 
    Id \<union> 
    mk_partnering C S 
         {(sN  ''pc'',  sMV ''pc'', S_1),
          (sN  ''nc'',  sMV ''nc'', S_1),
          (sN  ''sid'', sMV ''sid'',S_1),
          (sAV ''C'',   sAV ''C'',  S_1),
          (sAV ''S'',   sAV ''S'',  S_1),
          (sMV ''ns'',  sN  ''ns'', S_3),
          (sMV ''ps'',  sN  ''ps'', S_3),
          (sN  ''pms'', sMV ''pms'',S_5)} q \<union>
    mk_partnering S C 
         {(sAV ''C'',   sAV ''C'',  C_2),
          (sAV ''S'',   sAV ''S'',  C_2),
          (sN  ''ns'',  sMV ''ns'', C_4),
          (sMV ''pms'', sN  ''pms'',C_6)} q"


lemmas (in TLS_state) TLS_trusted_conv = 
  setEqImpTupleIn[OF TLS_trusted_def, of _ _ "(t,r,s)",simplified]

lemmas (in TLS_state) TLS_trustedI[intro!] = TLS_trusted_conv[THEN iffD2,simplified mk_partnering_conv,simplified]


subsection{* Adversary Compromise Model Definitions *}
text {*
Random number generator compromises are not possible. On one hand pms cannot be revealed any way, otherwise all values could be faked. On the other hand, the strong authentication properties don't hold any more. The reason is that the adversary might just get nc and ns before they are sent.
*}

definition (in TLS_state) ADVnotRNR :: "tid \<Rightarrow> state set"
where
"ADVnotRNR i = acm {LKRothers i, StR i TLS_trusted, SkR i TLS_trusted}"

locale TLS_state_ADVnotRNR = TLS_state +
  fixes test :: tid
  assumes compromiseModel [intro!]: "(t,r,s) \<in> ADVnotRNR test"
begin
  lemmas allowed_reveals = acm_to_caps[OF compromiseModel[simplified ADVnotRNR_def], simplified]
end


definition (in TLS_state) ADVall :: "tid \<Rightarrow> state set"
where
"ADVall i = acm {LKRothers i, StR i TLS_trusted, SkR i TLS_trusted, RNR}"

locale TLS_state_ADVall = TLS_state +
  fixes test :: tid
  assumes compromiseModel [intro!]: "(t,r,s) \<in> ADVall test"
begin
  lemmas allowed_reveals = acm_to_caps[OF compromiseModel[simplified ADVall_def], simplified]
end

definition (in TLS_state) ADVallActor :: "tid \<Rightarrow> varid \<Rightarrow> state set"
where
"ADVallActor i me = acm {LKRothers i, StR i TLS_trusted, SkR i TLS_trusted, RNR, LKRactor i me}"

locale TLS_state_ADVallActorC = TLS_state +
  fixes test :: tid
  assumes compromiseModel [intro!]: "(t,r,s) \<in> ADVallActor test (AVar ''C'')"
begin
  lemmas allowed_reveals = acm_to_caps[OF compromiseModel[simplified ADVallActor_def], simplified]
end

locale TLS_state_ADVallActorS = TLS_state +
  fixes test :: tid
  assumes compromiseModel [intro!]: "(t,r,s) \<in> ADVallActor test (AVar ''S'')"
begin
  lemmas allowed_reveals = acm_to_caps[OF compromiseModel[simplified ADVallActor_def], simplified]
end

section{* Security Proofs *}


subsection{* Origin Proofs *}
lemma (in TLS_state) C_pms_origin [rule_format]:
  assumes facts:
    "roleMap r test = Some C"
  shows
    "LN ''pms'' test \<in> knows t \<longrightarrow>
     RLKR (s(AV ''S'' test)) \<in> reveals t \<or> 
     (\<exists> tid1. (test,tid1) \<in> TLS_trusted (t,r,s) \<and> RCompr State tid1 \<in> reveals t) \<or> 
     (\<exists> tid1. (test,tid1) \<in> TLS_trusted (t,r,s) \<and> RCompr SessKey tid1 \<in> reveals t)" 
  (is "?knows \<longrightarrow> ?origins")
proof 
  assume ?knows
  thus ?origins using facts
  proof(sources " LN ''pms'' test ")
    case C_6_pms 
    thus ?thesis 
    by (sources "SK (s (AV ''S'' test))") (auto intro: compr_predOrdI)
  next
    case C_5_pms
    thus ?thesis
      by(auto intro: compr_predOrdI)
  next
    case C_7_pms
    thus ?thesis
      by(auto intro: compr_predOrdI)
  next
    case (S_6_pms tid1)
    thus ?thesis
    (* Proof Idea: If the adversary has learned pms from S_6_pms, then how could he send the messages in S_5 *)
    proof(sources "Enc \<lbrace>LC ''TT1'', Hash \<lbrace>LC ''TT2'', LN ''ns'' tid1, s (AV ''S'' tid1), LN ''pms'' test\<rbrace>\<rbrace>
       (SK (s (AV ''C'' tid1)))")
      case fake
      thus ?thesis
      proof(sources "Hash \<lbrace>LC ''TT2'', LN ''ns'' tid1, s (AV ''S'' tid1), LN ''pms'' test\<rbrace>")
        case C_6_hash
        thus ?thesis
        proof(sources "Enc \<lbrace>LC ''TT3'', s (MV ''sid'' tid1),
            Hash \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, s (MV ''nc'' tid1), LN ''ns'' tid1\<rbrace>,
            s (MV ''nc'' tid1), s (MV ''pc'' tid1), s (AV ''C'' tid1), LN ''ns'' tid1,
            LN ''ps'' tid1, s (AV ''S'' tid1)\<rbrace>
       (Hash \<lbrace>LC ''clientKey'', s (MV ''nc'' tid1), LN ''ns'' tid1,
               Hash \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, s (MV ''nc'' tid1),
                      LN ''ns'' tid1\<rbrace>\<rbrace>)")
          case fake
          thus ?thesis
          proof(sources "Hash \<lbrace>LC ''clientKey'', s (MV ''nc'' tid1), LN ''ns'' tid1,
                Hash \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, s (MV ''nc'' tid1),
                       LN ''ns'' tid1\<rbrace>\<rbrace>")
            case fake
            thus ?thesis 
            by(sources "Hash \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, s (MV ''nc'' tid1),
                      LN ''ns'' tid1\<rbrace>")
          next
            case C_9_hash_1
            thus ?thesis
              by (auto intro: compr_predOrdI)
          qed
        qed
      qed
    next
      case C_6_enc_1
      thus ?thesis
      proof(sources "Enc \<lbrace>LC ''TT3'', s (MV ''sid'' tid1),
            Hash \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, s (MV ''nc'' tid1), LN ''ns'' tid1\<rbrace>, s (MV ''nc'' tid1),
            s (MV ''pc'' tid1), s (AV ''C'' tid1), LN ''ns'' tid1, LN ''ps'' tid1, s (AV ''S'' tid1)\<rbrace>
       (Hash \<lbrace>LC ''clientKey'', s (MV ''nc'' tid1), LN ''ns'' tid1,
               Hash \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, s (MV ''nc'' tid1), LN ''ns'' tid1\<rbrace>\<rbrace>)")
        case fake
        thus ?thesis
        proof(sources "Hash \<lbrace>LC ''clientKey'', s (MV ''nc'' tid1), LN ''ns'' tid1,
               Hash \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, s (MV ''nc'' tid1), LN ''ns'' tid1\<rbrace>\<rbrace>")
          case fake
          thus ?thesis
          by(sources "Hash \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, s (MV ''nc'' tid1), LN ''ns'' tid1\<rbrace>")       next
          case C_9_hash_1
          thus ?thesis
            by (auto intro: compr_predOrdI)
        qed
       next
         case C_6_enc_2
         thus ?thesis
           by (auto intro: compr_predOrdI)
       qed
    qed
  qed
qed



lemma (in TLS_state) C_PRF_origin [rule_format]:
  assumes facts:
    "roleMap r test = Some C"
  shows
    "Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test, s(MV ''ns'' test)|} \<in> knows t \<longrightarrow>
    RLKR (s(AV ''S'' test)) \<in> reveals t \<or> 
    (\<exists> tid1. (test,tid1) \<in> TLS_trusted (t,r,s) \<and>  RCompr State tid1 \<in> reveals t) \<or> 
    (\<exists> tid1. (test,tid1) \<in> TLS_trusted (t,r,s) \<and> RCompr SessKey tid1 \<in> reveals t)" 
  (is "?knows \<longrightarrow> ?origins")
proof
  assume ?knows
  thus ?origins using facts 
  proof(sources "Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test, s(MV ''ns'' test)|} ")
    case fake
    thus ?thesis
      by (auto dest: C_pms_origin intro: event_predOrdI)
  next
    case C_6_hash_1
    thus ?thesis
    proof(sources "Hash {| LC ''clientKey'', LN ''nc'' test, s(MV ''ns'' test),
                   Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,s(MV ''ns'' test)|}|} ")
      case C_9_hash_1
      thus ?thesis
        by (auto intro: compr_predOrdI)
    next
      case (S_8_hash_1 tid1)
      thus ?thesis
      proof(sources "Enc \<lbrace>LC ''TT3'', s (MV ''sid'' tid1),
            Hash
             \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,
               LN ''ns'' tid1\<rbrace>,
            LN ''nc'' test, s (MV ''pc'' tid1), s (AV ''C'' tid1),
            LN ''ns'' tid1, LN ''ps'' tid1, s (AV ''S'' tid1)\<rbrace>
       (Hash
         \<lbrace>LC ''clientKey'', LN ''nc'' test, LN ''ns'' tid1,
           Hash
            \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,
              LN ''ns'' tid1\<rbrace>\<rbrace>)")
        case C_6_enc_2
        thus ?thesis 
          by (auto intro: compr_predOrdI)
      qed
    qed          
  next
    case (S_7_hash tid1)
    thus ?thesis
    proof(sources "Hash {| LC ''serverKey'', LN ''nc'' test, LN ''ns'' tid1,
                           Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,LN ''ns'' tid1|}|} ")
      case C_9_hash
      thus ?thesis
        by (auto intro: compr_predOrdI)
    next
      case S_8_hash
      thus ?thesis
      proof(sources "Enc \<lbrace>LC ''TT3'', s (MV ''sid'' tid1),
            Hash
             \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,
               LN ''ns'' tid1\<rbrace>,
            LN ''nc'' test, s (MV ''pc'' tid1), s (AV ''C'' tid1),
            LN ''ns'' tid1, LN ''ps'' tid1, s (AV ''S'' tid1)\<rbrace>
       (Hash
         \<lbrace>LC ''clientKey'', LN ''nc'' test, LN ''ns'' tid1,
           Hash
            \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,
              LN ''ns'' tid1\<rbrace>\<rbrace>)")
        case C_6_enc_2
        thus ?thesis
          by (auto intro: compr_predOrdI)
      qed
    qed
  qed
qed


lemma (in TLS_state) C_clientKey_origin [rule_format]:
  assumes facts:
    "roleMap r test = Some C"
   shows
    "Hash {| LC ''clientKey'', LN ''nc'' test, s(MV ''ns'' test),
             Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test, s(MV ''ns'' test) |}|} \<in> knows t
     \<longrightarrow> RLKR (s(AV ''S'' test)) \<in> reveals t \<or> 
    (\<exists> tid1. (test,tid1) \<in> TLS_trusted (t,r,s) \<and>  RCompr State tid1 \<in> reveals t) \<or> 
    (\<exists> tid1. (test,tid1) \<in> TLS_trusted (t,r,s) \<and> RCompr SessKey tid1 \<in> reveals t)"
   (is "?knows \<longrightarrow> ?origins")
proof
  assume ?knows
  thus ?origins using facts
  proof(sources "Hash {| LC ''clientKey'', LN ''nc'' test, s(MV ''ns'' test),
                        Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,s(MV ''ns'' test)|}|} ")
    case fake
    thus ?thesis
      by (auto dest: C_PRF_origin intro: event_predOrdI)
  next
    case C_9_hash_1
    thus ?thesis
      by (auto intro: compr_predOrdI)
  next
    case (S_8_hash_1 tid1)
    thus ?thesis
    proof(sources "Enc \<lbrace>LC ''TT3'', s (MV ''sid'' tid1),
            Hash
             \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,
               LN ''ns'' tid1\<rbrace>,
            LN ''nc'' test, s (MV ''pc'' tid1), s (AV ''C'' tid1),
            LN ''ns'' tid1, LN ''ps'' tid1, s (AV ''S'' tid1)\<rbrace>
       (Hash
         \<lbrace>LC ''clientKey'', LN ''nc'' test, LN ''ns'' tid1,
           Hash
            \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,
              LN ''ns'' tid1\<rbrace>\<rbrace>)")
      case C_6_enc_2
      thus ?thesis
        by (auto intro: compr_predOrdI)
    qed
  qed
qed


lemma (in TLS_state) C_serverKey_origin [rule_format]:
  assumes facts:
    "roleMap r test = Some C"
  shows
    "Hash {| LC ''serverKey'', LN ''nc'' test, s(MV ''ns'' test),
             Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test, s(MV ''ns'' test)|}|} \<in> knows t
     \<longrightarrow> RLKR (s(AV ''S'' test)) \<in> reveals t \<or> 
    (\<exists> tid1. (test,tid1) \<in> TLS_trusted (t,r,s) \<and>  RCompr State tid1 \<in> reveals t) \<or> 
    (\<exists> tid1. (test,tid1) \<in> TLS_trusted (t,r,s) \<and> RCompr SessKey tid1 \<in> reveals t)"
  (is "?knows \<longrightarrow> ?origins")
proof
  assume ?knows
  thus ?origins using facts
  proof(sources "Hash {| LC ''serverKey'', LN ''nc'' test, s(MV ''ns'' test),
                        Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test, s(MV ''ns'' test)|}|} ")
    case fake
    thus ?thesis
      by (auto dest: C_PRF_origin intro: event_predOrdI)
  next
    case C_9_hash
    thus ?thesis
      by (auto intro: compr_predOrdI)
  next
    case (S_8_hash tid1)
    thus ?thesis
    proof(sources "Enc \<lbrace>LC ''TT3'', s (MV ''sid'' tid1),
            Hash
             \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,
               LN ''ns'' tid1\<rbrace>,
            LN ''nc'' test, s (MV ''pc'' tid1), s (AV ''C'' tid1),
            LN ''ns'' tid1, LN ''ps'' tid1, s (AV ''S'' tid1)\<rbrace>
       (Hash
         \<lbrace>LC ''clientKey'', LN ''nc'' test, LN ''ns'' tid1,
           Hash
            \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,
              LN ''ns'' tid1\<rbrace>\<rbrace>)")
      case fake
      thus ?thesis
        by(auto intro: event_predOrdI dest!: C_clientKey_origin)
    next
      case C_6_enc_2
      thus ?thesis
        by (auto intro: compr_predOrdI)
    qed
  qed
qed




lemma (in TLS_state) S_pms_origin [rule_format]:
  assumes facts:
    "roleMap r test = Some S"
    "( test, S_5 ) \<in> steps t"
  shows
    "s(MV ''pms'' test) \<in> knows t \<longrightarrow>
     RLKR (s(AV ''S'' test)) \<in> reveals t \<or> 
     RLKR (s(AV ''C'' test)) \<in> reveals t \<or> 
     (\<exists> tid1. (test,tid1) \<in> TLS_trusted (t,r,s) \<and> RCompr State tid1 \<in> reveals t) \<or> 
     (\<exists> tid1. (test,tid1) \<in> TLS_trusted (t,r,s) \<and> RCompr SessKey tid1 \<in> reveals t)"
  (is "?knows \<longrightarrow> ?origins")
proof
  assume ?knows
  note_prefix_closed facts = facts this
  thus ?origins
  proof(sources "Enc {| LC ''TT1'',Hash {| LC ''TT2'', LN ''ns'' test, s(AV ''S'' test), s(MV ''pms'' test)|}|}
                 ( SK ( s(AV ''C'' test) ) ) ")
    case fake
    thus ?thesis
      by(sources "SK (s (AV ''C'' test))")  (auto intro: compr_predOrdI)
  next
    case (C_6_enc_1 tid1)
    thus ?thesis
    proof(sources "LN ''pms'' tid1")
      case C_6_pms
      thus ?thesis
        by(sources "SK (s (AV ''S'' test))") (auto intro: compr_predOrdI)
    next
      case C_5_pms
      thus ?thesis
        by (auto intro: compr_predOrdI)
    next
      case C_7_pms
      thus ?thesis
        by (auto intro: compr_predOrdI)
    next
      case (S_6_pms tid2)
      note_unified facts = this
      thus ?thesis
      proof(sources "Enc \<lbrace>LC ''TT1'', Hash \<lbrace>LC ''TT2'', LN ''ns'' tid2, s (AV ''S'' tid2), LN ''pms'' tid1\<rbrace>\<rbrace>
       (SK (s (AV ''C'' tid2)))")
        case fake
        thus ?thesis
        by (sources "Hash \<lbrace>LC ''TT2'', LN ''ns'' tid2, s (AV ''S'' tid2), LN ''pms'' tid1\<rbrace>")
     next
       case C_6_enc_1
       note_unified facts = facts this
       thus ?thesis
         by (auto intro: compr_predOrdI)
     qed
   qed
 qed
qed


lemma (in TLS_state) S_PRF_origin [rule_format]:
  assumes facts:
    "roleMap r test = Some S"
    "( test, S_5 ) \<in> steps t"
  shows 
    "Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test), s(MV ''nc'' test), LN ''ns'' test|} \<in> knows t \<longrightarrow>
    RLKR (s(AV ''S'' test)) \<in> reveals t \<or> 
    RLKR (s(AV ''C'' test)) \<in> reveals t \<or> 
    (\<exists> tid1. (test,tid1) \<in> TLS_trusted (t,r,s) \<and> RCompr State tid1 \<in> reveals t) \<or> 
    (\<exists> tid1. (test,tid1) \<in> TLS_trusted (t,r,s) \<and> RCompr SessKey tid1 \<in> reveals t)"
  (is "?knows \<longrightarrow> ?origins")
proof
  assume ?knows
  note_prefix_closed facts = facts this
  thus ?origins
  proof(sources "Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test),s(MV ''nc'' test), LN ''ns'' test|} ")
    case (C_6_hash_1 tid1)
    thus ?thesis
    proof(sources "Hash {| LC ''clientKey'', LN ''nc'' tid1, LN ''ns'' test,
                   Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' tid1, LN ''nc'' tid1, LN ''ns'' test|} |} ")
      case C_9_hash_1
      thus ?thesis 
      proof(sources "Enc \<lbrace>LC ''TT1'',
            Hash
             \<lbrace>LC ''TT2'', LN ''ns'' test, s (AV ''S'' test),
               LN ''pms'' tid1\<rbrace>\<rbrace>
       (SK (s (AV ''C'' test)))")
        case fake
        thus ?thesis
          by(sources "SK (s (AV ''C'' test))")  (auto intro: compr_predOrdI)
      next
        case C_6_enc_1
        thus ?thesis
          by (auto intro: compr_predOrdI)
      qed
    next
      case S_8_hash_1
      thus ?thesis
        by (auto intro: compr_predOrdI)
    qed
  next
    case S_7_hash
    thus ?thesis
    proof(sources "Hash {| LC ''serverKey'', s(MV ''nc'' test), LN ''ns'' test,
                   Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test), s(MV ''nc'' test), LN ''ns'' test |}|} ")
      case (C_9_hash tid1)
      thus ?thesis
      proof(sources "Enc \<lbrace>LC ''TT1'', Hash \<lbrace>LC ''TT2'', LN ''ns'' test, s (AV ''S'' test), LN ''pms'' tid1\<rbrace>\<rbrace>
       (SK (s (AV ''C'' test)))")
        case fake
        thus ?thesis
          by(sources "SK (s (AV ''C'' test))")  (auto intro: compr_predOrdI)
      next
        case C_6_enc_1
        thus ?thesis
          by (auto intro: compr_predOrdI)
      qed
    next
      case S_8_hash
      thus ?thesis
        by (auto intro: compr_predOrdI)
    qed
  next
    case fake
    thus ?thesis
      by (auto dest: S_pms_origin intro: event_predOrdI)
  qed
qed


lemma (in TLS_state) S_clientKey_origin [rule_format]:
  assumes facts:
    "roleMap r test = Some S"
    "( test, S_5 ) \<in>  steps t"
  shows
    "Hash {| LC ''clientKey'', s(MV ''nc'' test), LN ''ns'' test,
             Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test),s(MV ''nc'' test), LN ''ns'' test |}|} \<in> knows t
     \<longrightarrow>
     RLKR (s(AV ''S'' test)) \<in>  reveals t \<or> 
     RLKR (s(AV ''C'' test)) \<in>  reveals t \<or> 
     (\<exists> tid1. (test,tid1) \<in> TLS_trusted (t,r,s) \<and> RCompr State tid1 \<in> reveals t) \<or> 
     (\<exists> tid1. (test,tid1) \<in> TLS_trusted (t,r,s) \<and> RCompr SessKey tid1 \<in> reveals t)"
  (is "?knows \<longrightarrow> ?origins")
proof
  assume ?knows
  note_prefix_closed facts = facts this
  thus ?origins
  proof(sources "Hash {| LC ''clientKey'', s(MV ''nc'' test), LN ''ns'' test,
                 Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test),s(MV ''nc'' test), LN ''ns'' test|}|} ")
    case fake
    thus ?thesis
      by (auto dest: S_PRF_origin intro: event_predOrdI)
  next
    case (C_9_hash_1 tid1)
    thus ?thesis
    proof(sources "Enc \<lbrace>LC ''TT1'', Hash \<lbrace>LC ''TT2'', LN ''ns'' test, s (AV ''S'' test), LN ''pms'' tid1\<rbrace>\<rbrace>
       (SK (s (AV ''C'' test)))")
      case fake
      thus ?thesis
          by(sources "SK (s (AV ''C'' test))")  (auto intro: compr_predOrdI)
    next
      case C_6_enc_1
      thus ?thesis
        by (auto intro: compr_predOrdI)
    qed
  next
    case S_8_hash_1
    thus ?thesis
      by (auto intro: compr_predOrdI)
  qed
qed


lemma (in TLS_state) S_serverKey_origin [rule_format]:
  assumes facts:
    "roleMap r test = Some S"
    "( test, S_5 ) \<in> steps t"
  shows 
    "Hash {| LC ''serverKey'', s(MV ''nc'' test), LN ''ns'' test,
     Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test),s(MV ''nc'' test), LN ''ns'' test |}|} \<in> knows t
     \<longrightarrow>
     RLKR (s(AV ''S'' test)) \<in> reveals t \<or> 
     RLKR (s(AV ''C'' test)) \<in> reveals t \<or> 
     (\<exists> tid1. (test,tid1) \<in> TLS_trusted (t,r,s) \<and>  RCompr State tid1 \<in> reveals t) \<or> 
     (\<exists> tid1. (test,tid1) \<in> TLS_trusted (t,r,s) \<and> RCompr SessKey tid1 \<in> reveals t)"
  (is "?knows \<longrightarrow> ?origins")
proof
  assume ?knows
  note_prefix_closed facts = facts this
  thus ?origins
  proof(sources "Hash {| LC ''serverKey'', s(MV ''nc'' test), LN ''ns'' test,
                 Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test),s(MV ''nc'' test), LN ''ns'' test|} |} ")
    case fake
    thus ?thesis
      by (auto dest: S_PRF_origin intro: event_predOrdI)
  next
    case (C_9_hash tid1)
    thus ?thesis
    proof(sources "Enc \<lbrace>LC ''TT1'', Hash \<lbrace>LC ''TT2'', LN ''ns'' test, s (AV ''S'' test), LN ''pms'' tid1\<rbrace>\<rbrace>
       (SK (s (AV ''C'' test)))")
      case fake
      thus ?thesis
          by(sources "SK (s (AV ''C'' test))")  (auto intro: compr_predOrdI)
    next
      case C_6_enc_1
      thus ?thesis
        by (auto intro: compr_predOrdI)
    qed
  next
    case S_8_hash
    thus ?thesis
      by (auto intro: compr_predOrdI)
  qed
qed

subsection{* Secrecy Proofs *}

lemma (in TLS_state_ADVall) C_pms_sec:
  assumes facts:
    "roleMap r test = Some C"
    "LN ''pms'' test \<in> knows t"
  shows "False"
using facts
apply -
apply(frule C_pms_origin, assumption)
by(auto dest: allowed_reveals)

lemma (in TLS_state_ADVall) C_PRF_sec:
  assumes facts:
    "roleMap r test = Some C"
    "Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test, s(MV ''ns'' test) |} \<in> knows t"
  shows "False"
using facts
apply -
apply(frule C_PRF_origin, assumption)
by(auto dest: allowed_reveals)

lemma (in TLS_state_ADVall) C_clientKey_sec:
  assumes facts:
    "roleMap r test = Some C"
    "Hash {| LC ''clientKey'', LN ''nc'' test, s(MV ''ns'' test),
             Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test, s(MV ''ns'' test)|}|} \<in> knows t"
  shows "False"
using facts
apply -
apply(frule C_clientKey_origin, assumption)
by(auto dest: allowed_reveals)

lemma (in TLS_state_ADVall) C_serverKey_sec:
  assumes facts:
    "roleMap r test = Some C"
    "Hash {| LC ''serverKey'', LN ''nc'' test, s(MV ''ns'' test),
             Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,
                     s(MV ''ns'' test)
                  |}
          |} : knows t"
  shows "False"
using facts 
apply -
apply(frule C_serverKey_origin, assumption)
by(auto dest: allowed_reveals)

lemma (in TLS_state_ADVall) S_pms_sec:
  assumes facts:
    "roleMap r test = Some S"
    "( test, S_5 ) \<in>  steps t"
    "s(MV ''pms'' test) \<in> knows t"
  shows "False"
using facts
apply -
apply(frule S_pms_origin, assumption)
by(auto dest: allowed_reveals)

lemma (in TLS_state_ADVall) S_PRF_sec:
  assumes facts:
    "roleMap r test = Some S"
    "( test, S_5 ) \<in> steps t"
    "Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test),
             s(MV ''nc'' test), LN ''ns'' test
          |} \<in> knows t"
  shows "False"
using facts
apply -
apply(frule S_PRF_origin, assumption)
by(auto dest: allowed_reveals)

lemma (in TLS_state_ADVall) S_clientKey_sec:
  assumes facts:
    "roleMap r test = Some S"
    "( test, S_5 ) \<in> steps t"
    "Hash {| LC ''clientKey'', s(MV ''nc'' test), LN ''ns'' test,
             Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test),
                     s(MV ''nc'' test), LN ''ns'' test
                  |}
          |} \<in> knows t"
  shows "False"
using facts
apply -
apply(frule S_clientKey_origin, assumption)
by(auto dest: allowed_reveals)

lemma (in TLS_state_ADVnotRNR) C_pms_sec:
  assumes facts:
    "roleMap r test = Some C"
    "LN ''pms'' test \<in> knows t"
  shows "False"
using facts
apply -
apply(frule C_pms_origin, assumption)
by(auto dest: allowed_reveals C_pms_origin) 

lemma (in TLS_state_ADVnotRNR) C_PRF_sec:
  assumes facts:
    "roleMap r test = Some C"
    "Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test, s(MV ''ns'' test) |} \<in> knows t"
  shows "False"
using facts
apply -
apply(frule C_PRF_origin, assumption)
by(auto dest: allowed_reveals)

lemma (in TLS_state_ADVnotRNR) C_clientKey_sec:
  assumes facts:
    "roleMap r test = Some C"
    "Hash {| LC ''clientKey'', LN ''nc'' test, s(MV ''ns'' test),
             Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test, s(MV ''ns'' test)|}|} \<in> knows t"
  shows "False"
using facts
apply -
apply(frule C_clientKey_origin, assumption)
by(auto dest: allowed_reveals)

lemma (in TLS_state_ADVnotRNR) C_serverKey_sec:
  assumes facts:
    "roleMap r test = Some C"
    "Hash {| LC ''serverKey'', LN ''nc'' test, s(MV ''ns'' test),
             Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,
                     s(MV ''ns'' test)
                  |}
          |} : knows t"
  shows "False"
using facts 
apply -
apply(frule C_serverKey_origin, assumption)
by(auto dest: allowed_reveals)

lemma (in TLS_state_ADVnotRNR) S_pms_sec:
  assumes facts:
    "roleMap r test = Some S"
    "( test, S_5 ) \<in>  steps t"
    "s(MV ''pms'' test) \<in> knows t"
  shows "False"
using facts
apply -
apply(frule S_pms_origin, assumption)
by(auto dest: allowed_reveals)

lemma (in TLS_state_ADVnotRNR) S_PRF_sec:
  assumes facts:
    "roleMap r test = Some S"
    "( test, S_5 ) \<in> steps t"
    "Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test),
             s(MV ''nc'' test), LN ''ns'' test
          |} \<in> knows t"
  shows "False"
using facts
apply -
apply(frule S_PRF_origin, assumption)
by(auto dest: allowed_reveals)

lemma (in TLS_state_ADVnotRNR) S_clientKey_sec:
  assumes facts:
    "roleMap r test = Some S"
    "( test, S_5 ) \<in> steps t"
    "Hash {| LC ''clientKey'', s(MV ''nc'' test), LN ''ns'' test,
             Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test),
                     s(MV ''nc'' test), LN ''ns'' test
                  |}
          |} \<in> knows t"
  shows "False"
using facts
apply -
apply(frule S_clientKey_origin, assumption)
by(auto dest: allowed_reveals)

lemma (in TLS_state_ADVnotRNR) S_serverKey_sec:
  assumes facts:
    "roleMap r test = Some S"
    "( test, S_5 ) \<in> steps t"
    "Hash {| LC ''serverKey'', s(MV ''nc'' test), LN ''ns'' test,
             Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test),
                     s(MV ''nc'' test), LN ''ns'' test
                  |}
          |} \<in> knows t"
  shows "False"
using facts
apply -
apply(frule S_serverKey_origin, assumption)
by(auto dest: allowed_reveals)

subsection{* Authentication Proofs *}


lemma (in TLS_state_ADVallActorC) C_ni_synch:
  assumes facts:
    "roleMap r test = Some C"
    "( test, C_8 ) \<in> steps t"
  shows
    "(?  tid2.
        roleMap r tid2 = Some S &
        s(AV ''C'' test) = s(AV ''C'' tid2) &
        s(AV ''S'' test) = s(AV ''S'' tid2) &
        LN ''nc'' test = s(MV ''nc'' tid2) &
        s(MV ''ns'' test) = LN ''ns'' tid2 &
        LN ''pc'' test = s(MV ''pc'' tid2) &
        s(MV ''ps'' test) = LN ''ps'' tid2 &
        LN ''sid'' test = s(MV ''sid'' tid2) &
        LN ''pms'' test = s(MV ''pms'' tid2) &
        (St( tid2, S_1 )) \<prec> (St( tid2, S_3 )) &
        (St( test, C_4 )) \<prec> (St( test, C_6 )) &
        (St( test, C_6 )) \<prec> (St( tid2, S_5 )) &
        (St( tid2, S_5 )) \<prec> (St( tid2, S_7 )) &
        (St( tid2, S_7 )) \<prec> (St( test, C_8 )))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources "
                   Enc {| LC ''TT3'', LN ''sid'' test,
                          Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,
                                  s(MV ''ns'' test)
                               |},
                          LN ''nc'' test, LN ''pc'' test, s(AV ''C'' test),
                          s(MV ''ns'' test), s(MV ''ps'' test), s(AV ''S'' test)
                       |}
                       ( Hash {| LC ''serverKey'', LN ''nc'' test, s(MV ''ns'' test),
                                 Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,
                                         s(MV ''ns'' test)
                                      |}
                              |}
                       ) ")
    case fake
    note_unified facts = facts this
    moreover {
      assume "RLKR (s (AV ''S'' test)) \<in> reveals t"
      hence "False" using facts
        by(auto dest!: allowed_reveals)
    }
    moreover {
      assume "\<exists>tid1. (test, tid1) \<in> TLS_trusted (t, r, s) \<and> RCompr State tid1 \<in> reveals t"
      hence "False" by (auto dest: allowed_reveals)
    }
    moreover {
      assume "(\<exists>tid1. (test, tid1) \<in> TLS_trusted (t, r, s) \<and> RCompr SessKey tid1 \<in> reveals t)"
      hence "False" by (auto dest: allowed_reveals)
    }
    ultimately show ?thesis
      apply -
      apply (drule event_predOrdI, drule C_serverKey_origin, assumption)
      by (auto)
  next
    case (S_7_enc tid2)
    thus ?thesis
    proof(sources "Enc {| LC ''TT0'', LN ''pms'' test |}( PK ( s(AV ''S'' test) ) ) ")
      case fake
      note_unified facts = facts this
      moreover {
        assume "RLKR (s (AV ''S'' test)) \<in> reveals t"
        hence "False" using facts
          by(auto dest!: allowed_reveals)
      }
      moreover {
        assume "\<exists>tid1. (test, tid1) \<in> TLS_trusted (t, r, s) \<and> RCompr State tid1 \<in> reveals t"
        hence "False" by (auto dest: allowed_reveals)
      }
      moreover {
        assume "(\<exists>tid1. (test, tid1) \<in> TLS_trusted (t, r, s) \<and> RCompr SessKey tid1 \<in> reveals t)"
        hence "False" by (auto dest: allowed_reveals)
      }
      ultimately show ?thesis
        apply -
        apply (drule event_predOrdI, drule C_pms_origin, assumption)
        by (auto)
    next
      case C_6_enc
      thus ?thesis by auto
    qed
  qed
qed

text {*
The variable agreement cannot be stronger. The reason is that only those listed below are 
protected by the signature of C. Hence the adversary could fake the rest if he decrypts the TT1 message
with the pms in it.
*}
lemma (in TLS_state_ADVallActorS) S_ni_synch:
  assumes facts:
    "roleMap r test = Some S"
    "( test, S_7 ) \<in>  steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some C &
        s(AV ''C'' tid1) = s(AV ''C'' test) &
        s(AV ''S'' tid1) = s(AV ''S'' test) &
        s(MV ''ns'' tid1) = LN ''ns'' test &
        LN ''pms'' tid1 = s(MV ''pms'' test) &
        (St( test, S_1 )) \<prec> (St( test, S_3 )) &
        (St( tid1, C_4 )) \<prec> (St( tid1, C_6 )) &
        (St( tid1, C_6 )) \<prec> (St( test, S_5 )) &
        (St( test, S_5 )) \<prec> (St( test, S_7 )))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis
  proof(sources "Enc \<lbrace>LC ''TT1'',
             Hash
              \<lbrace>LC ''TT2'', LN ''ns'' test, s (AV ''S'' test),
                s (MV ''pms'' test)\<rbrace>\<rbrace>
        (SK (s (AV ''C'' test)))")
    case fake
    thus ?thesis
    proof(sources "SK (s (AV ''C'' test))")
    qed (force dest: compr_predOrdI allowed_reveals)
  next
    case (C_6_enc_1 tid1)
    thus ?thesis
    proof(sources "Enc {| LC ''TT3'', s(MV ''sid'' test),
                          Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test),
                                  s(MV ''nc'' test), LN ''ns'' test
                               |},
                          s(MV ''nc'' test), s(MV ''pc'' test), s(AV ''C'' test),
                          LN ''ns'' test, LN ''ps'' test, s(AV ''S'' test)
                       |}
                       ( Hash {| LC ''clientKey'', s(MV ''nc'' test), LN ''ns'' test,
                                 Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test),
                                         s(MV ''nc'' test), LN ''ns'' test
                                      |}
                              |}
                       ) ")
      case fake
      thus ?thesis
        by auto
    next
      case C_6_enc_2
      thus ?thesis
        by auto
    qed
  qed
qed

lemma (in TLS_state_ADVnotRNR) C_ni_synch:
  assumes facts:
    "roleMap r test = Some C"
    "( test, C_8 ) \<in> steps t"
  shows
    "(?  tid2.
        roleMap r tid2 = Some S &
        s(AV ''C'' test) = s(AV ''C'' tid2) &
        s(AV ''S'' test) = s(AV ''S'' tid2) &
        LN ''nc'' test = s(MV ''nc'' tid2) &
        s(MV ''ns'' test) = LN ''ns'' tid2 &
        LN ''pc'' test = s(MV ''pc'' tid2) &
        s(MV ''ps'' test) = LN ''ps'' tid2 &
        LN ''sid'' test = s(MV ''sid'' tid2) &
        LN ''pms'' test = s(MV ''pms'' tid2) &
        (St( test, C_2 )) \<prec> (St( tid2, S_1 )) &
        (St( tid2, S_1 )) \<prec> (St( tid2, S_3 )) &
        (St( tid2, S_3 )) \<prec> (St( test, C_4 )) &
        (St( test, C_4 )) \<prec> (St( test, C_6 )) &
        (St( test, C_6 )) \<prec> (St( tid2, S_5 )) &
        (St( tid2, S_5 )) \<prec> (St( tid2, S_7 )) &
        (St( tid2, S_7 )) \<prec> (St( test, C_8 )))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources "
                   Enc {| LC ''TT3'', LN ''sid'' test,
                          Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,
                                  s(MV ''ns'' test)
                               |},
                          LN ''nc'' test, LN ''pc'' test, s(AV ''C'' test),
                          s(MV ''ns'' test), s(MV ''ps'' test), s(AV ''S'' test)
                       |}
                       ( Hash {| LC ''serverKey'', LN ''nc'' test, s(MV ''ns'' test),
                                 Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,
                                         s(MV ''ns'' test)
                                      |}
                              |}
                       ) ")
    case fake
    thus ?thesis 
      by (auto dest: C_PRF_sec intro: event_predOrdI)
  next
    case (S_7_enc tid2)
    thus ?thesis
    proof(sources "Enc {| LC ''TT0'', LN ''pms'' test |}( PK ( s(AV ''S'' test) ) ) ")
      case fake
      thus ?thesis 
        by (auto dest: C_pms_sec intro: event_predOrdI)
    next
      case C_6_enc
      thus ?thesis
      proof(sources "LN ''nc'' test")
        case C_2_nc
        thus ?thesis
        proof(sources "LN ''ns'' tid2")
          case S_3_ns
          thus ?thesis by force
        qed (force dest: allowed_reveals compr_predOrdI)+
      next
        case C_6_nc
        thus ?thesis
        by(sources "Hash \<lbrace>LC ''clientKey'', LN ''nc'' test, LN ''ns'' tid2,
                Hash \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test, LN ''ns'' tid2\<rbrace>\<rbrace>")
      qed (force dest: allowed_reveals compr_predOrdI)+
    qed
  qed
qed

lemma (in TLS_state_ADVnotRNR) S_ni_synch:
  assumes facts:
    "roleMap r test = Some S"
    "( test, S_7 ) \<in>  steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some C &
        s(AV ''C'' tid1) = s(AV ''C'' test) &
        s(AV ''S'' tid1) = s(AV ''S'' test) &
        LN ''nc'' tid1 = s(MV ''nc'' test) &
        s(MV ''ns'' tid1) = LN ''ns'' test &
        LN ''pc'' tid1 = s(MV ''pc'' test) &
        s(MV ''ps'' tid1) = LN ''ps'' test &
        LN ''sid'' tid1 = s(MV ''sid'' test) &
        LN ''pms'' tid1 = s(MV ''pms'' test) &
        (St( tid1, C_2 )) \<prec> (St( test, S_1 )) &
        (St( test, S_1 )) \<prec> (St( test, S_3 )) &
        (St( test, S_3 )) \<prec> (St( tid1, C_4 )) &
        (St( tid1, C_4 )) \<prec> (St( tid1, C_6 )) &
        (St( tid1, C_6 )) \<prec> (St( test, S_5 )) &
        (St( test, S_5 )) \<prec> (St( test, S_7 )))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources "
                   Enc {| LC ''TT3'', s(MV ''sid'' test),
                          Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test),
                                  s(MV ''nc'' test), LN ''ns'' test
                               |},
                          s(MV ''nc'' test), s(MV ''pc'' test), s(AV ''C'' test),
                          LN ''ns'' test, LN ''ps'' test, s(AV ''S'' test)
                       |}
                       ( Hash {| LC ''clientKey'', s(MV ''nc'' test), LN ''ns'' test,
                                 Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test),
                                         s(MV ''nc'' test), LN ''ns'' test
                                      |}
                              |}
                       ) ")
    case fake 
    thus ?thesis 
      by (auto dest: S_PRF_sec intro: event_predOrdI) 
  next
    case (C_6_enc_2 tid3)
    thus ?thesis
    proof(sources "LN ''ns'' test")
      case S_3_ns
      thus ?thesis
      proof(sources "LN ''nc'' tid3")
        case C_2_nc
        thus ?thesis
          by force
      qed (force dest: allowed_reveals compr_predOrdI)+
    qed (force dest: allowed_reveals compr_predOrdI)+
  qed
qed


lemma (in TLS_state_ADVall) C_ni_synch:
  assumes facts:
    "roleMap r test = Some C"
    "( test, C_8 ) \<in> steps t"
  shows
    "(?  tid2.
        roleMap r tid2 = Some S &
        s(AV ''C'' test) = s(AV ''C'' tid2) &
        s(AV ''S'' test) = s(AV ''S'' tid2) &
        LN ''nc'' test = s(MV ''nc'' tid2) &
        s(MV ''ns'' test) = LN ''ns'' tid2 &
        LN ''pc'' test = s(MV ''pc'' tid2) &
        s(MV ''ps'' test) = LN ''ps'' tid2 &
        LN ''sid'' test = s(MV ''sid'' tid2) &
        LN ''pms'' test = s(MV ''pms'' tid2) &
        (St( tid2, S_1 )) \<prec> (St( tid2, S_3 )) &
        (St( test, C_4 )) \<prec> (St( test, C_6 )) &
        (St( test, C_6 )) \<prec> (St( tid2, S_5 )) &
        (St( tid2, S_5 )) \<prec> (St( tid2, S_7 )) &
        (St( tid2, S_7 )) \<prec> (St( test, C_8 )))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources "
                   Enc {| LC ''TT3'', LN ''sid'' test,
                          Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,
                                  s(MV ''ns'' test)
                               |},
                          LN ''nc'' test, LN ''pc'' test, s(AV ''C'' test),
                          s(MV ''ns'' test), s(MV ''ps'' test), s(AV ''S'' test)
                       |}
                       ( Hash {| LC ''serverKey'', LN ''nc'' test, s(MV ''ns'' test),
                                 Hash {| LC ''TT4'', LC ''PRF'', LN ''pms'' test, LN ''nc'' test,
                                         s(MV ''ns'' test)
                                      |}
                              |}
                       ) ")
    case fake
    thus ?thesis 
      by (auto dest: C_PRF_sec intro: event_predOrdI)
  next
    case (S_7_enc tid2)
    thus ?thesis
    proof(sources "Enc {| LC ''TT0'', LN ''pms'' test |}( PK ( s(AV ''S'' test) ) ) ")
      case fake
      thus ?thesis 
        by (auto dest: C_pms_sec intro: event_predOrdI)
    next
      case C_6_enc
      thus ?thesis by auto
    qed
  qed
qed

lemma (in TLS_state_ADVall) S_ni_synch:
  assumes facts:
    "roleMap r test = Some S"
    "( test, S_7 ) \<in>  steps t"
  shows
    "(?  tid1.
        roleMap r tid1 = Some C &
        s(AV ''C'' tid1) = s(AV ''C'' test) &
        s(AV ''S'' tid1) = s(AV ''S'' test) &
        LN ''nc'' tid1 = s(MV ''nc'' test) &
        s(MV ''ns'' tid1) = LN ''ns'' test &
        LN ''pc'' tid1 = s(MV ''pc'' test) &
        s(MV ''ps'' tid1) = LN ''ps'' test &
        LN ''sid'' tid1 = s(MV ''sid'' test) &
        LN ''pms'' tid1 = s(MV ''pms'' test) &
        (St( test, S_1 )) \<prec> (St( test, S_3 )) &
        (St( tid1, C_4 )) \<prec> (St( tid1, C_6 )) &
        (St( tid1, C_6 )) \<prec> (St( test, S_5 )) &
        (St( test, S_5 )) \<prec> (St( test, S_7 )))"
proof -
  note_prefix_closed facts = facts
  thus ?thesis proof(sources "
                   Enc {| LC ''TT3'', s(MV ''sid'' test),
                          Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test),
                                  s(MV ''nc'' test), LN ''ns'' test
                               |},
                          s(MV ''nc'' test), s(MV ''pc'' test), s(AV ''C'' test),
                          LN ''ns'' test, LN ''ps'' test, s(AV ''S'' test)
                       |}
                       ( Hash {| LC ''clientKey'', s(MV ''nc'' test), LN ''ns'' test,
                                 Hash {| LC ''TT4'', LC ''PRF'', s(MV ''pms'' test),
                                         s(MV ''nc'' test), LN ''ns'' test
                                      |}
                              |}
                       ) ")
    case fake 
    thus ?thesis 
      by (auto dest: S_PRF_sec intro: event_predOrdI) 
  next
    case (C_6_enc_2 tid3)
    thus ?thesis by auto
  qed
qed



section{* Use lemmas from a different Role *}

definition
  TLS_partners :: "partnering"
where
  "TLS_partners q = 
    mk_partnering C S 
         {(sAV ''C'',   sAV ''C'',  S_1),
          (sAV ''S'',   sAV ''S'',  S_1),
          (sMV ''ns'',  sN  ''ns'', S_3),
          (sN  ''pms'', sMV ''pms'',S_5)} q \<union>
    mk_partnering S C 
         {(sAV ''C'',   sAV ''C'',  C_2),
          (sAV ''S'',   sAV ''S'',  C_2),
          (sN  ''ns'',  sMV ''ns'', C_4),
          (sMV ''pms'', sN  ''pms'',C_6)} q"


lemmas (in TLS_state) TLS_partners_conv = 
  setEqImpTupleIn[OF TLS_partners_def, of _ _ "(t,r,s)",simplified]

lemmas (in TLS_state) TLS_partnersI[intro!] = TLS_partners_conv[THEN iffD2,simplified mk_partnering_conv,simplified]



declare (in TLS_state) S_6_def[simp del]
lemma (in TLS_state) TLS_partners_revealsExist:
  assumes facts:
    "roleMap r i = Some C"
    "roleMap r test = Some S"
    "(test,S_3) \<in> steps t"
    "(i,test) \<in> TLS_partners (t,r,s)"
    "(i,tid1) \<in> TLS_partners (t,r,s) \<and> (tid1, S_6) \<in> steps t"
  shows
    "test = tid1"
proof -
  from facts
  have "roleMap r tid1 = Some S"
    by (fastforce dest: mk_partneringRole simp add: TLS_partners_conv)
  note_prefix_closed facts = facts this
  thus ?thesis
  proof -
    from facts
    have "(i, tid1) \<in> mk_partnering TLS_acm.C S
        {(sLAV ''C'', sLAV ''C'', S_1), (sLAV ''S'', sLAV ''S'', S_1),
         (sLMV ''ns'', sLN ''ns'', S_3), (sLN ''pms'', sLMV ''pms'', S_5)}
        (t, r, s)"
      by (fastforce simp add: TLS_partners_conv dest: mk_partneringRole)
    moreover
    from facts 
    have "(i, test) \<in> mk_partnering TLS_acm.C S
        {(sLAV ''C'', sLAV ''C'', S_1), (sLAV ''S'', sLAV ''S'', S_1),
         (sLMV ''ns'', sLN ''ns'', S_3), (sLN ''pms'', sLMV ''pms'', S_5)}
        (t, r, s)"
      by (fastforce simp add: TLS_partners_conv dest: mk_partneringRole)
    ultimately
    show ?thesis
      using facts
      apply -
      apply(drule_tac ?st = "S_3" in uniquePartner)
      by(blast intro: event_predOrdI)+
  qed     
qed
declare (in TLS_state) S_6_def[simp]

lemma (in TLS_state) C_pms_origin_reuse [rule_format]:
  assumes facts:
    "roleMap r test = Some C"
  shows
    "LN ''pms'' test \<in> knows t \<longrightarrow>
     RLKR (s(AV ''S'' test)) \<in> reveals t \<or> 
     (test, Note ''5'' State C_5_pt) \<in> steps t \<or>
     (test, Note ''7'' State C_7_pt) \<in> steps t \<or>
     (test, Note ''9'' SessKey C_9_pt) \<in> steps t \<or>
     (\<exists> tid1. (test,tid1) \<in> TLS_partners (t,r,s) \<and> (tid1, Note ''6'' State S_6_pt) \<in> steps t)"
  (is "?knows \<longrightarrow> ?origins")
proof 
  assume ?knows
  thus ?origins using facts
  proof(sources " LN ''pms'' test ")
    case C_6_pms 
    thus ?thesis 
    by (sources "SK (s (AV ''S'' test))") (auto intro: compr_predOrdI)
  next
    case C_5_pms
    thus ?thesis
      by(auto intro: event_predOrdI)
  next
    case C_7_pms
    thus ?thesis
      by(auto intro: event_predOrdI)
  next
    case (S_6_pms tid1)
    thus ?thesis
    (* Proof Idea: If the adversary has learned pms from S_6_pms, then how could he send the messages in S_5 *)
    proof(sources "Enc \<lbrace>LC ''TT1'', Hash \<lbrace>LC ''TT2'', LN ''ns'' tid1, s (AV ''S'' tid1), LN ''pms'' test\<rbrace>\<rbrace>
       (SK (s (AV ''C'' tid1)))")
      case fake
      thus ?thesis
      proof(sources "Hash \<lbrace>LC ''TT2'', LN ''ns'' tid1, s (AV ''S'' tid1), LN ''pms'' test\<rbrace>")
        case C_6_hash
        thus ?thesis
        proof(sources "Enc \<lbrace>LC ''TT3'', s (MV ''sid'' tid1),
            Hash \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, s (MV ''nc'' tid1), LN ''ns'' tid1\<rbrace>,
            s (MV ''nc'' tid1), s (MV ''pc'' tid1), s (AV ''C'' tid1), LN ''ns'' tid1,
            LN ''ps'' tid1, s (AV ''S'' tid1)\<rbrace>
       (Hash \<lbrace>LC ''clientKey'', s (MV ''nc'' tid1), LN ''ns'' tid1,
               Hash \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, s (MV ''nc'' tid1),
                      LN ''ns'' tid1\<rbrace>\<rbrace>)")
          case fake
          thus ?thesis
          proof(sources "Hash \<lbrace>LC ''clientKey'', s (MV ''nc'' tid1), LN ''ns'' tid1,
                Hash \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, s (MV ''nc'' tid1),
                       LN ''ns'' tid1\<rbrace>\<rbrace>")
            case fake
            thus ?thesis 
            by(sources "Hash \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, s (MV ''nc'' tid1),
                      LN ''ns'' tid1\<rbrace>")
          next
            case C_9_hash_1
            thus ?thesis
              by (auto intro: event_predOrdI)
          qed
        qed
      qed
    next
      case C_6_enc_1
      thus ?thesis
      proof(sources "Enc \<lbrace>LC ''TT3'', s (MV ''sid'' tid1),
            Hash \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, s (MV ''nc'' tid1), LN ''ns'' tid1\<rbrace>, s (MV ''nc'' tid1),
            s (MV ''pc'' tid1), s (AV ''C'' tid1), LN ''ns'' tid1, LN ''ps'' tid1, s (AV ''S'' tid1)\<rbrace>
       (Hash \<lbrace>LC ''clientKey'', s (MV ''nc'' tid1), LN ''ns'' tid1,
               Hash \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, s (MV ''nc'' tid1), LN ''ns'' tid1\<rbrace>\<rbrace>)")
        case fake
        thus ?thesis
        proof(sources "Hash \<lbrace>LC ''clientKey'', s (MV ''nc'' tid1), LN ''ns'' tid1,
               Hash \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, s (MV ''nc'' tid1), LN ''ns'' tid1\<rbrace>\<rbrace>")
          case fake
          thus ?thesis
          by(sources "Hash \<lbrace>LC ''TT4'', LC ''PRF'', LN ''pms'' test, s (MV ''nc'' tid1), LN ''ns'' tid1\<rbrace>")       next
          case C_9_hash_1
          thus ?thesis
            by (auto intro: event_predOrdI)
        qed
       next
         case C_6_enc_2
         thus ?thesis
           by (auto intro: event_predOrdI)
       qed
    qed
  qed
qed


lemma (in TLS_state) S_pms_origin_reuse [rule_format]:
  assumes facts:
    "roleMap r test = Some S"
    "( test, S_5 ) \<in> steps t"
  shows
    "s(MV ''pms'' test) \<in> knows t \<longrightarrow>
     RLKR (s(AV ''S'' test)) \<in> reveals t \<or> 
     RLKR (s(AV ''C'' test)) \<in> reveals t \<or> 
     (\<exists> tid1. (test,tid1) \<in> TLS_partners (t,r,s) \<and> 
             (
              (tid1, Note ''5'' State C_5_pt) \<in> steps t \<or>
              (tid1, Note ''7'' State C_7_pt) \<in> steps t \<or>
              (tid1, Note ''9'' SessKey C_9_pt) \<in> steps t  
             )) \<or>
     (test, Note ''6'' State S_6_pt) \<in> steps t"
  (is "?knows \<longrightarrow> ?origins")
proof
  assume ?knows
  note_prefix_closed facts = facts this
  thus ?origins
  proof(sources "Enc {| LC ''TT1'',Hash {| LC ''TT2'', LN ''ns'' test, s(AV ''S'' test), s(MV ''pms'' test)|}|}
                 ( SK ( s(AV ''C'' test) ) ) ")
    case fake
    thus ?thesis
      by(sources "SK (s (AV ''C'' test))")  (auto intro: compr_predOrdI)
  next
    case (C_6_enc_1 tid1)
    note_unified facts = facts this

    hence "(test,tid1) \<in> TLS_partners (t,r,s)"
      by fastforce
    note_unified facts = facts this
    moreover 
    {
      assume "RLKR (s (AV ''S'' tid1)) \<in> reveals t"
      hence "?thesis" using facts by fastforce
    }
    moreover{
      assume "(tid1, Note ''5'' State C_5_pt) \<in> steps t"
      hence "?thesis" using facts by blast
    }
    moreover {
      assume "(tid1, Note ''7'' State C_7_pt) \<in> steps t"
      hence "?thesis" using facts by blast
    }
    moreover {
      assume "(tid1, Note ''9'' SessKey C_9_pt) \<in> steps t"
      hence "?thesis" using facts by blast
    }
    moreover {
      assume "\<exists>tid1a. (tid1, tid1a) \<in> TLS_partners (t, r, s) \<and> (tid1a, Note ''6'' State S_6_pt) \<in> steps t"
      note_unified facts = facts this
      obtain tid1a where
        partCompr: "(tid1, tid1a) \<in> TLS_partners (t, r, s) \<and> (tid1a, Note ''6'' State S_6_pt) \<in> steps t"
        using facts by fastforce
      hence  "test = tid1a" using facts
        apply -
        apply(rule TLS_partners_revealsExist,assumption,assumption,rule event_predOrdI, assumption)          
        by fastforce+
      hence "?thesis"
        using facts partCompr
        by fastforce
    }
    ultimately
    show ?thesis using facts
      apply -
      apply(frule event_predOrdI, frule C_pms_origin_reuse, assumption)
      by fastforce
  qed
qed
end
