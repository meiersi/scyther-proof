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
theory Protocol
imports 
  DistinctList
begin

section{* Protocol Specifications *}

subsection{* Types and Operations *}

subsubsection{* Patterns *}

types id = string

datatype varid = AVar id | MVar id

datatype pattern = 
    PConst   id
  | PFresh   id
  | PVar     varid
  | PHash    pattern
  | PTup     pattern pattern 
  | PEnc     pattern pattern 
  | PSign    pattern pattern
  | PSymK    pattern pattern 
  | PShrK    "varid set"  (* variables denoting a set of agents sharing a key *)
  | PAsymPK  pattern         
  | PAsymSK  pattern         

(* bi-directional keys between two agents referenced by variables *)
definition sKbd :: "varid \<Rightarrow> varid \<Rightarrow> pattern"
where "sKbd a b = PShrK {a, b}"

text{* Free variables *}
fun FV :: "pattern \<Rightarrow> varid set"
where 
  "FV (PVar v)     = {v}"
| "FV (PHash m)    = FV m"
| "FV (PTup x y)   = FV x \<union> FV y"
| "FV (PEnc m k)   = FV m \<union> FV k"
| "FV (PSign m k)  = FV m \<union> FV k"
| "FV (PSymK a b)  = FV a \<union> FV b"
| "FV (PShrK A)    = A"
| "FV (PAsymPK a)  = FV a"
| "FV (PAsymSK a)  = FV a"
| "FV (_)          = {}"

lemma FV_sKbd [simp]: "FV (sKbd a b) = {a, b}"
  by (auto simp: sKbd_def)


text{* Free message variables *}
fun FMV :: "pattern \<Rightarrow> id set"
where 
  "FMV (PVar (MVar v)) = {v}"
| "FMV (PHash m)       = FMV m"
| "FMV (PTup x y)      = FMV x \<union> FMV y"
| "FMV (PEnc m k)      = FMV m \<union> FMV k"
| "FMV (PSign m k)     = FMV m \<union> FMV k"
| "FMV (PSymK a b)     = FMV a \<union> FMV b"
| "FMV (PShrK A)       = {v. MVar v \<in> A}"
| "FMV (PAsymPK a)     = FMV a"
| "FMV (PAsymSK a)     = FMV a"
| "FMV (_)             = {}"

lemma FMV_sKbd [simp]: 
  "FMV (sKbd a b) = {v. MVar v = a \<or> MVar v = b}"
  by (auto simp: sKbd_def)


fun FAV :: "pattern \<Rightarrow> id set"
where
  "FAV (PVar (AVar a)) = {a}"
| "FAV (PHash m)       = FAV m"
| "FAV (PTup x y)      = FAV x \<union> FAV y"
| "FAV (PEnc m k)      = FAV m \<union> FAV k"
| "FAV (PSign m k)     = FAV m \<union> FAV k"
| "FAV (PSymK a b)     = FAV a \<union> FAV b"
| "FAV (PShrK A)       = {v. AVar v \<in> A}"
| "FAV (PAsymPK a)     = FAV a"
| "FAV (PAsymSK a)     = FAV a"
| "FAV (_)             = {}"

lemma FAV_sKbd [simp]: 
  "FAV (sKbd a b) = {v. AVar v = a \<or> AVar v = b}"
  by (auto simp: sKbd_def)


subsubsection{* Roles *}

text{*
  Roles are non-empty lists of unique send and receive steps 
  such that no long-term keys are used in message texts and all 
  nonce variables are received before they are sent.

  The labels allow to make steps with identical message unique.
  They are currently defaulted to strings, but could be anything.
*}

types lbl = string

datatype notetype = RandGen | State | SessKey

datatype rolestep = Send lbl pattern | Recv lbl pattern | Note lbl notetype pattern

fun stepPat :: "rolestep \<Rightarrow> pattern"
where
  "stepPat (Send lbl msg)    = msg"
| "stepPat (Recv lbl msg)    = msg"
| "stepPat (Note lbl ty msg) = msg"

fun noteType :: "rolestep \<Rightarrow> notetype"
where
  "noteType (Note l ty pt) = ty"

fun sendStep :: "rolestep \<Rightarrow> bool"
where
  "sendStep (Send lbl    msg) = True"
| "sendStep (Recv lbl    msg) = False"
| "sendStep (Note lbl ty msg) = False"

fun noteStep :: "rolestep \<Rightarrow> bool"
where
  "noteStep (Send lbl    msg) = False"
| "noteStep (Recv lbl    msg) = False"
| "noteStep (Note lbl ty msg) = True"


abbreviation recvStep where "recvStep x \<equiv> \<not>sendStep x \<and> \<not> noteStep x"

lemma sendStepD [simp]:
  assumes inStep: "sendStep step"
  shows "\<exists> l pt. step = (Send l pt)"
using inStep
proof(cases step)
qed auto

lemma recvStepD [simp]:
  assumes inStep: "recvStep step"
  shows "\<exists> l pt. step = (Recv l pt)"
using inStep
proof(cases step)
qed auto

lemma noteStepD [simp]:
  assumes inStep: "noteStep step"
  shows "\<exists> l ty pt. step = (Note l ty pt)"
using inStep
proof(cases step)
qed auto


types "role" = "rolestep list"

fun recv_before :: "id set \<Rightarrow> role \<Rightarrow> bool"
where
  "recv_before bound []                = True"
| "recv_before bound (Recv _ msg # xs) = 
     recv_before (bound \<union> FMV msg) xs"
| "recv_before bound (Note _ _ msg # xs) =
     ((\<forall> v. v \<in> FMV msg \<longrightarrow> v \<in> bound) \<and>  recv_before bound xs)"
| "recv_before bound (Send _ msg # xs) =
     ((\<forall> v. v \<in> FMV msg \<longrightarrow> v \<in> bound) \<and>  recv_before bound xs)"


locale wf_role =
  distinct_list R for R :: "role" +
  assumes recv_msgVar_first [iff]: "recv_before {} R"

  
subsubsection{* Protocols *}

types proto = "role set"

locale wf_proto =
  fixes P :: proto
  assumes wf_roles: "R \<in> P \<Longrightarrow> wf_role R"


subsection{* Properties *}

subsubsection{* Well-Formed Roles *}

lemma recv_before_sent_distinct_Send_FV:
  "\<lbrakk>  recv_before V (R@ Send lbl pt # R'); 
      distinct (R @ Send lbl pt # R');
      v \<in> FMV pt; v \<notin> V 
   \<rbrakk> \<Longrightarrow>
   \<exists> lbl' pt'. Recv lbl' pt' \<in> set R \<and> v \<in> FMV pt'"
proof(induct R arbitrary: V)
  case (Cons step R) note IH = this show ?case
    proof(cases step)
      case (Send lbl pt) thus ?thesis using IH by auto
    next
      case (Recv lbl pt) thus ?thesis using IH by (auto, fast)
    next
      case (Note lbl ty pt) thus ?thesis using IH by auto
    qed
qed simp

lemma recv_before_note_distinct_Note_FV:
  "\<lbrakk>  recv_before V (R@ Note lbl ty pt # R'); 
      distinct (R @ Note lbl ty pt # R');
      v \<in> FMV pt; v \<notin> V 
   \<rbrakk> \<Longrightarrow>
   \<exists> lbl' pt'. Recv lbl' pt' \<in> set R \<and> v \<in> FMV pt'"
proof(induct R arbitrary: V)
  case (Cons Note R) 
  note IH = this show ?case
    proof(cases Note)
      case (Send lbl pt) thus ?thesis using IH by auto
    next
      case (Recv lbl pt) thus ?thesis using IH by (auto, fast)
    next
      case (Note lbl ty pt) thus ?thesis using IH by auto
    qed
qed simp


lemma (in wf_role) Send_FV:
  assumes Send: "Send lbl pt \<in> set R" (is "?send \<in> set R")
      and FV:   "v \<in> FMV pt"
  shows "\<exists> lbl' pt'. listOrd R (Recv lbl' pt') (Send lbl pt) \<and> v \<in> FMV pt'" 
using Send 
proof -
  let ?send = "Send lbl pt"
    and "\<exists> lbl' pt'. ?received lbl' pt'" = ?thesis
  assume "?send \<in> set R" then
  obtain ys zs 
    where split: "R = ys @ ?send # zs" by (blast dest!: split_list)
  moreover have "distinct R" and "recv_before {} R" by auto
  ultimately obtain lbl' pt' where "Recv lbl' pt' \<in> set ys" 
                                and "v \<in> FMV pt'"
             by (fastsimp dest!: recv_before_sent_distinct_Send_FV intro!: FV)
  hence "?received lbl' pt'" using split by auto
  thus ?thesis by blast
qed


lemma (in wf_role) Note_FV:
  assumes Note: "Note lbl ty pt \<in> set R" (is "?note \<in> set R")
      and FV:   "v \<in> FMV pt"
  shows "\<exists> lbl' pt'. listOrd R (Recv lbl' pt') (Note lbl ty pt) \<and> v \<in> FMV pt'" 
using Note
proof -
  let ?send = "Note lbl ty pt"
    and "\<exists> lbl' pt'. ?received lbl' pt'" = ?thesis
  assume "?note \<in> set R" then
  obtain ys zs 
    where split: "R = ys @ ?note # zs" by (blast dest!: split_list)
  moreover have "distinct R" and "recv_before {} R" by auto
  ultimately obtain lbl' pt' where "Recv lbl' pt' \<in> set ys" 
                                and "v \<in> FMV pt'"
             by (fastsimp dest!: recv_before_note_distinct_Note_FV intro!: FV)
  hence "?received lbl' pt'" using split by auto
  thus ?thesis by blast
qed

lemma FV_FAV_conv[iff]:
  "(a \<in> FAV pt) = ((AVar a) \<in> FV pt)"
proof(induct pt)
  case (PVar vid)
  thus ?case
  by(cases vid) auto
qed auto

lemma FV_FMV_conv[iff]:
  "(v \<in> FMV pt) = ((MVar v) \<in> FV pt)"
proof(induct pt)
  case (PVar vid)
  thus ?case
    by(cases vid) auto
qed auto



definition aVars:: "role \<Rightarrow> varid set"
where
  "aVars role = foldr (\<lambda> st se. (AVar ` FAV (stepPat st)) \<union> se) role {}"

lemma aVars_singleton[iff]:
  "AVar a \<notin> aVars []"
by(fastsimp simp add: aVars_def)

lemma aVars_Nil [iff]: "aVars [] = {}"
  by (auto simp: aVars_def)

lemma aVars_Cons [simp]: "aVars (s#xs) = (AVar ` FAV (stepPat s) \<union> aVars xs)"
  by (auto simp: aVars_def)

lemma aVars_FAV_conv:
  "(AVar a \<in> aVars R) = (\<exists> s \<in> set R. \<exists> pt. (stepPat s = pt \<and> a \<in> FAV pt))"
by (induct R rule: foldr.induct) ( fastsimp simp add: aVars_def)+


definition lastComStep :: "role \<rightharpoonup> rolestep"
where
  "lastComStep rs = (case (filter (\<lambda> s. \<not> (noteStep s)) rs) of 
     (x#xs) \<Rightarrow> Some (last (x#xs))
    |([])   \<Rightarrow> None)"

definition firstComStep :: "role \<rightharpoonup> rolestep"
where
  "firstComStep rs = (case (filter (\<lambda> s. \<not> (noteStep s)) rs) of 
     (x#xs) \<Rightarrow> Some x
    |([])   \<Rightarrow> None)"


lemma lastComStep_Nil [iff]: "lastComStep [] = None"
  by (auto simp: lastComStep_def)

lemma lastComStep_Cons [simp]: 
  "lastComStep (x#xs) =
  (let 
    s = lastComStep xs
   in
    if (noteStep x) then
      s
    else
      if (s = None) then
        Some x
      else
        s
  )"
proof (cases "[s\<leftarrow>xs . \<not> noteStep s]")
qed (fastsimp simp add: lastComStep_def)+

lemma firstComStep_Nil [iff]: "firstComStep [] = None"
  by (auto simp: firstComStep_def)

lemma firstComStep_Cons [simp]: "firstComStep (x#xs) =
  ( if (noteStep x) then
      firstComStep xs
    else
      Some x
  )"
proof (cases "[s\<leftarrow>xs . \<not> noteStep s]")
qed (fastsimp simp add: firstComStep_def)+ 




end
