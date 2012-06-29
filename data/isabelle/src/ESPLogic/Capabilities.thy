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
theory Capabilities
imports
  ExplicitModel
  InferenceRules
begin

chapter{* Compromising Adversary Capability *}

section{* Partnering *}
types partnering = "state \<Rightarrow> (tid \<times> tid) set"


definition unionPart :: "partnering \<Rightarrow> partnering \<Rightarrow> partnering" (infix "UNP" 65)
where
  "unionPart P1 P2 q = P1 q \<union> P2 q" 

notation (xsymbols)
  unionPart (infix "\<union>\<^isub>P" 65)

lemma union_unionPart_conv:
  "(a \<in> ((P1 \<union>\<^isub>P P2) q)) = (a \<in> (P1 q \<union> P2 q))"
by (fastsimp simp add: unionPart_def)


definition mk_partnering :: "role \<Rightarrow> role \<Rightarrow> (pattern \<times> pattern \<times> rolestep) set \<Rightarrow> partnering"
where
  "mk_partnering R1 R2 conds q = (case q of (t,r,s) \<Rightarrow>
       {(i,j) | i j. roleMap r i = Some R1 \<and> roleMap r j = Some R2 \<and> 
                     (\<forall> (p1,p2,st) \<in> conds. (j,st) \<in> steps t \<longrightarrow> (inst s i p1) = (inst s j p2)) })"

lemma mk_partnering_conv:
 "((i,j) \<in> mk_partnering R1 R2 conds (t,r,s)) = 
   (roleMap r i = Some R1 \<and> roleMap r j = Some R2 \<and> 
   (\<forall> (p1,p2,st) \<in> conds. (j,st) \<in> steps t \<longrightarrow> (inst s i p1) = (inst s j p2)))"
by (fastsimp simp add: mk_partnering_def)

lemma setEqImpTupleIn: "(X = Y) \<Longrightarrow> ((i,j) \<in> X) = ((i,j) \<in> Y)"
by fastsimp

lemma uniquePartner: 
  assumes facts:
    "(i,j) \<in> mk_partnering R1 R2 conds (t,r,s)"
    "(pt1,pt2,st) \<in> conds"
    "(j,st) \<in> steps t"
    "pt2 = PFresh n"
  shows
    "\<forall> j'. (i,j') \<in> mk_partnering R1 R2 conds (t,r,s) \<and> (j',st) \<in> steps t \<longrightarrow> j' = j"
proof -
  have "inst s i pt1 = inst s j pt2"
    using facts by (fastsimp simp add: mk_partnering_conv)
  moreover 
  hence "\<forall> j'. j' \<noteq> j \<longrightarrow> inst s j pt2 \<noteq> inst s j' pt2"
    using facts by fastsimp
  ultimately 
  have "\<forall> j'. j' \<noteq> j \<longrightarrow> inst s i pt1 \<noteq> inst s j' pt2"
    by fastsimp
  hence "\<forall> j'. (j' \<noteq> j \<and> (j',st) \<in> steps t) \<longrightarrow>  (i,j') \<notin> mk_partnering R1 R2 conds (t,r,s)"
    using facts by (fastsimp simp add: mk_partnering_conv)
  thus ?thesis
    by auto
qed

lemma mk_partneringRole:
  assumes facts:
  "(i,j) \<in> mk_partnering R1 R2 conds (t,r,s)"
  shows
   "roleMap r i = Some R1 \<and> roleMap r j = Some R2"
using facts
by (fastsimp simp add: mk_partnering_conv)

section{* Capabilities *}

types capability = "state \<Rightarrow> reveal set"

subsection{* Helper Functions *}
definition interCap :: "capability \<Rightarrow> capability \<Rightarrow> capability" (infix "INC" 65)
where
  "interCap C1 C2 = (\<lambda> q. C1 q \<inter> C2 q)"

notation (xsymbols)
  interCap  (infix "\<inter>\<^isub>C" 65)

definition unionCap :: "capability \<Rightarrow> capability \<Rightarrow> capability" (infix "UNC" 65)
where
  "unionCap C1 C2 = (\<lambda> q. C1 q \<union> C2 q)" 

notation (xsymbols)
  unionCap  (infix "\<union>\<^isub>C" 65)

lemma union_unionCap_conv:
  "(a \<in> ((C1 \<union>\<^isub>C C2) q)) = (a \<in> (C1 q \<union> C2 q))"
by (fastsimp simp add: unionCap_def)

lemma inter_interCap_conv:
  "(a \<in> ((C1 \<inter>\<^isub>C C2) q)) = (a \<in> (C1 q \<inter> C2 q))"
by (fastsimp simp add: interCap_def)


subsection{* Adversary-Compromise Model *}

definition acm :: "capability set \<Rightarrow> state set"
where
  "acm caps =  { (t,r,s) | t r s. \<forall> reveal \<in> reveals t. \<exists> cap \<in> caps. reveal \<in> cap (t,r,s) }"

lemma acm_to_caps:
"\<lbrakk> 
  (t,r,s) \<in> acm caps ; 
  reveal \<in> reveals t 
 \<rbrakk> \<Longrightarrow> \<exists> cap \<in> caps. reveal \<in> cap (t,r,s)"
by(fastsimp simp add: acm_def)


lemma acm_monotone:
"\<lbrakk> (t,r,s) \<in> acm caps \<rbrakk> 
 \<Longrightarrow> (t,r,s) \<in> acm (caps \<union> caps')"
by(fastsimp simp add: acm_def)

subsection{* Implementation of Capabilities and Dot-Mapping *}

subsubsection{* Long Term Key Reveals *}
fun LKRprotected :: "tid \<Rightarrow> varid set \<Rightarrow> capability"
where
  "LKRprotected i pAVars (t,r,s) = {RLKR a | a.  \<forall> pAVar \<in> pAVars. s (pAVar, i) \<noteq>  a}"

fun LKRafterStep :: "tid \<Rightarrow> rolestep \<Rightarrow> capability"
where
  "LKRafterStep i step (t,r,s) = {RLKR a | a. predOrd t (St (i,step)) (LKR a)}"

fun LKRbeforeStep :: "tid \<Rightarrow> rolestep \<Rightarrow> capability"
where
  "LKRbeforeStep i step (t,r,s) = {RLKR a | a. predOrd t (LKR a) (St (i, step))}"

fun LKRactor :: "tid \<Rightarrow> varid \<Rightarrow> capability"
where
  "LKRactor i actor (t,r,s) = {RLKR (s (actor, i))} \<inter> 
                              {a. \<exists> R. roleMap r i = Some R \<and> a \<in> LKRprotected i ((aVars R) - {actor}) (t,r,s)}"

fun LKRpeers :: "tid \<Rightarrow> varid \<Rightarrow> capability"
where
  "LKRpeers i actor (t,r,s) = {a. \<exists> R. roleMap r i = Some R \<and> a \<in> LKRprotected i (aVars R - {actor}) (t,r,s)}"

fun LKRothers :: "tid \<Rightarrow> capability"
where
  "LKRothers i (t,r,s) = {a. \<exists> R. roleMap r i = Some R \<and> a \<in> LKRprotected i (aVars R) (t,r,s)}"

fun LKRafter :: "tid \<Rightarrow> capability"
where 
  "LKRafter i (t,r,s) = {a. \<exists> R st. roleMap r i = Some R \<and> lastComStep R = Some st \<and> a \<in> LKRafterStep i st (t,r,s)}"

fun LKRbefore :: "tid \<Rightarrow> capability"
where 
  "LKRbefore i (t,r,s) = {a. \<exists> R st. roleMap r i = Some R \<and> firstComStep R = Some st \<and> a \<in> LKRbeforeStep i st (t,r,s)}"

fun LKRduring :: "tid \<Rightarrow> capability"
where
  "LKRduring i q = {a. a \<notin> LKRafter i q \<and> a \<notin> LKRbefore i q}"

text{* The partnering definition used in this capability must ensure, that 
       if two threads are partners, they their transcript match, i.e. they 
       have matching histories. That means all variables must be included! *}
fun LKRafterCorrect :: "tid \<Rightarrow> partnering \<Rightarrow> capability"
where 
  "LKRafterCorrect i ps (t,r,s) = 
    {a. \<exists> R st. roleMap r i = Some R \<and> lastComStep R = Some st \<and> a \<in> LKRafterStep i st (t,r,s) \<and> 
        (\<exists> (i,j) \<in> ps (t,r,s). (\<exists> R' st'. roleMap r j = Some R' \<and> lastComStep R' = Some st' \<and> a \<in> LKRafterStep j st' (t,r,s) ))}"


lemma imposs_lkr_caps[iff]:
  "RCompr a b \<notin> LKRprotected i vars (t,r,s)"
  "RCompr a b \<notin> LKRothers i (t,r,s)"
  "RCompr a b \<notin> LKRactor i c (t,r,s)"
  "RCompr a b \<notin> LKRafter i (t,r,s)"
  "RCompr a b \<notin> LKRafterCorrect i ps(t,r,s)"
by(fastsimp)+


subsubsection{* Compromises *}

definition RNR :: "capability"
where
  "RNR _ = {RCompr RandGen j| j. True}"

definition SKs :: "capability"
where
  "SKs _ = {RCompr SessKey j| j. True}"

definition otherData :: "capability"
where
  "otherData _ = {RCompr State j| j. True}"


definition comprOthers :: "tid \<Rightarrow> partnering \<Rightarrow> capability"
where
  "comprOthers i ps q = {RCompr State j| j. (i,j) \<notin> ps q} \<union>
                        {RCompr SessKey j| j. (i,j) \<notin> ps q} \<union>
                        {RCompr RandGen j| j. (i,j) \<notin> ps q}"

definition comprPartners :: "tid \<Rightarrow> partnering \<Rightarrow> capability"
where
  "comprPartners i ps q = UNIV - comprOthers i ps q"

definition SkR :: "tid \<Rightarrow> partnering \<Rightarrow> capability"
where
  "SkR i ps q = {RCompr SessKey j | j. (i,j) \<notin> ps q \<and> j \<noteq> i}"


definition StR :: "tid \<Rightarrow> partnering \<Rightarrow> capability"
where
  "StR i ps q = {RCompr State j | j. (i,j) \<notin> ps q \<and> j \<noteq> i}"

lemma imposs_compr_caps[iff]:
  "RLKR a \<notin> StR i ps q"
  "RLKR a \<notin> SkR i ps q"
  "RLKR a \<notin> RNR q"
  "RCompr SessKey j \<notin> StR i ps q"
  "RCompr RandGen j \<notin> StR i ps q"
  "RCompr State j \<notin> SkR i ps q"
  "RCompr RandGen j \<notin> SkR i ps q"
  "RCompr State j \<notin> RNR q"
  "RCompr SessKey j \<notin> RNR q"
by(fastsimp simp add: StR_def SkR_def RNR_def)+


lemma SkR_conv[simp]:
  "c \<in> SkR i ps (t,r,s) = (\<exists> j. (c = RCompr SessKey j) \<and> (i,j) \<notin> ps (t,r,s) \<and> j \<noteq> i )"
by(fastsimp simp add: SkR_def)

lemma RNR_conv[simp]:
  "c \<in> RNR (t,r,s) = (\<exists> j. (c = RCompr RandGen j))"
by(fastsimp simp add: RNR_def)

lemma StR_conv[simp]:
  "c \<in> StR i ps (t,r,s) = (\<exists> j. (c = RCompr State j) \<and> (i,j) \<notin> ps (t,r,s) \<and> j \<noteq> i )"
by(fastsimp simp add: StR_def)


lemma (in reachable_state) LKRafterTrans:
  "\<lbrakk>
    roleMap r i = Some R;
    lastComStep R = Some st;
    RLKR a \<in> LKRafter i (t,r,s);
    LKR a \<prec> St (i,st)
   \<rbrakk> \<Longrightarrow> False"
by(fastsimp)

end
