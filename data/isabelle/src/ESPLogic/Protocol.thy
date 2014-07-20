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

type_synonym id = string

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

type_synonym lbl = string

datatype notetype = RandGen | State | SessKey

datatype rolestep = Send lbl pattern
| Recv lbl pattern
| Match lbl bool varid pattern
| Note lbl notetype pattern

text {*
  Free message variables guaranteed to be instantiated after
  a role step.
*}
fun sourced_vars :: "rolestep \<Rightarrow> id set"
where
  "sourced_vars (Recv  lbl        pt) = FMV pt"
| "sourced_vars (Match lbl True v pt) = FMV pt"
| "sourced_vars _ = {}"

text {*
  Free message variables which must have been instantiated
  when performing a role step.
*}
fun used_vars :: "rolestep \<Rightarrow> id set"
where
  "used_vars (Send  lbl      msg) = FMV msg"
| "used_vars (Recv  lbl      pt)  = {}"
| "used_vars (Match lbl eq v pt)  = {m. v = MVar m}"
| "used_vars (Note  lbl ty   msg) = FMV msg"

text {* Free variables of a role step *}
fun FV_rolestep :: "rolestep \<Rightarrow> varid set"
where
  "FV_rolestep (Send  lbl      pt) = FV pt"
| "FV_rolestep (Recv  lbl      pt) = FV pt"
| "FV_rolestep (Match lbl eq v pt) = {v} \<union> FV pt"
| "FV_rolestep (Note  lbl ty   pt) = FV pt"

text {* Free agent variables of a role step *}
fun FAV_rolestep :: "rolestep \<Rightarrow> id set"
where
  "FAV_rolestep (Send  lbl      pt) = FAV pt"
| "FAV_rolestep (Recv  lbl      pt) = FAV pt"
| "FAV_rolestep (Match lbl eq v pt) = {a. v = AVar a} \<union> FAV pt"
| "FAV_rolestep (Note  lbl ty   pt) = FAV pt"

fun stepPat :: "rolestep \<Rightarrow> pattern"
where
  "stepPat (Send  lbl      pt) = pt"
| "stepPat (Recv  lbl      pt) = pt"
| "stepPat (Match lbl eq v pt) = pt"
| "stepPat (Note  lbl ty   pt) = pt"

fun matchVar :: "rolestep \<Rightarrow> varid"
where
  "matchVar (Match l eq v pt) = v"

fun noteType :: "rolestep \<Rightarrow> notetype"
where
  "noteType (Note l ty pt) = ty"

fun sendStep :: "rolestep \<Rightarrow> bool"
where
  "sendStep (Send lbl pt) = True"
| "sendStep _             = False"

fun noteStep :: "rolestep \<Rightarrow> bool"
where
  "noteStep (Note lbl ty pt) = True"
| "noteStep _                = False"

fun recvStep :: "rolestep \<Rightarrow> bool"
where
  "recvStep (Recv lbl pt) = True"
| "recvStep _             = False"

fun matchStep :: "rolestep \<Rightarrow> bool"
where
  "matchStep (Match lbl eq v pt) = True"
| "matchStep _                   = False"

fun matchEqStep :: "rolestep \<Rightarrow> bool"
where
  "matchEqStep (Match lbl True v pt) = True"
| "matchEqStep _                     = False"

fun notMatchStep :: "rolestep \<Rightarrow> bool"
where
  "notMatchStep (Match lbl False v pt) = True"
| "notMatchStep _                      = False"

lemma sendStepD [simp]:
  assumes inStep: "sendStep step"
  shows "\<exists> l pt. step = (Send l pt)"
using inStep
proof(cases step)
qed auto

lemma recvStepD [simp]:
  assumes inStep: "recvStep step"
  shows "\<exists> l v. step = (Recv l v)"
using inStep
proof(cases step)
qed auto

lemma matchStepD [simp]:
  assumes inStep: "matchStep step"
  shows "\<exists> l eq v pt. step = (Match l eq v pt)"
using inStep
proof (cases step)
qed auto

lemma matchEqStepD [simp]:
  assumes inStep: "matchEqStep step"
  shows "\<exists> l v pt. step = (Match l True v pt)"
using inStep
proof (cases step)
  case (Match lbl eq v pt)
  thus ?thesis using inStep by (cases eq, auto)
qed auto

lemma notMatchStepD [simp]:
  assumes inStep: "notMatchStep step"
  shows "\<exists> l v pt. step = (Match l False v pt)"
using inStep
proof (cases step)
  case (Match lbl eq v pt)
  thus ?thesis using inStep by (cases eq, auto)
qed auto

lemma noteStepD [simp]:
  assumes inStep: "noteStep step"
  shows "\<exists> l ty pt. step = (Note l ty pt)"
using inStep
proof(cases step)
qed auto


type_synonym "role" = "rolestep list"

fun source_before_use :: "id set \<Rightarrow> role \<Rightarrow> bool"
where
  "source_before_use bound [] = True"
| "source_before_use bound (step # xs) =
    ((used_vars step \<subseteq> bound)
    \<and> source_before_use (bound \<union> sourced_vars step) xs)"

fun wildcards :: "role \<Rightarrow> rolestep \<Rightarrow> id set"
where
  "wildcards role (Match l False v pt) =
    FMV pt - \<Union> (sourced_vars ` {pred. listOrd role pred (Match l False v pt)})"
| "wildcards role _ = {}"


locale wf_role =
  distinct_list R for R :: "role" +
  assumes source_msgVar_first [iff]: "source_before_use {} R"


subsubsection{* Protocols *}

type_synonym proto = "role set"

locale wf_proto =
  fixes P :: proto
  assumes wf_roles: "R \<in> P \<Longrightarrow> wf_role R"


subsection{* Properties *}

subsubsection{* Well-Formed Roles *}

lemma source_before_use_distinct:
  "\<lbrakk>  source_before_use V (R @ step # R');
      distinct (R @ step # R');
      v \<in> used_vars step; v \<notin> V
   \<rbrakk> \<Longrightarrow>
   (\<exists> step'. step' \<in> set R \<and> v \<in> sourced_vars step')"
proof (induct R arbitrary: V)
  case (Cons step R)
    note IH = this show ?case
    proof (cases step)
      case Send thus ?thesis using IH by fastforce
    next
      case Recv thus ?thesis using IH by fastforce
    next
      case Match thus ?thesis using IH by fastforce
    next
      case Note thus ?thesis using IH by fastforce
    qed
qed auto

lemma (in wf_role) source_use_ord:
  assumes useR: "ustep \<in> set R"
      and useV: "v \<in> used_vars ustep"
    shows "\<exists> sstep. v \<in> sourced_vars sstep \<and> listOrd R sstep ustep" (is "\<exists> sstep. ?source sstep")
using useR
proof -
  assume "ustep \<in> set R"
  then obtain ys zs 
    where split: "R = ys @ ustep # zs" by (blast dest!: split_list)
  moreover have "distinct R" and "source_before_use {} R" by auto
  ultimately obtain sstep where "v \<in> sourced_vars sstep" and "sstep \<in> set ys"
             by (fastforce dest!: source_before_use_distinct intro!: useV)
  hence "?source sstep" using split by fastforce
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

lemma sourced_imp_FV[dest]:
  "v \<in> sourced_vars st \<Longrightarrow> MVar v \<in> FV_rolestep st"
proof (cases st)
  case (Match lbl eq mv pt)
  assume "v \<in> sourced_vars st"
  thus ?thesis using Match by (cases eq, auto)
qed auto

lemma used_imp_FV[dest]:
  "v \<in> used_vars st \<Longrightarrow> MVar v \<in> FV_rolestep st"
proof (cases st)
  case (Match lbl eq mv pt)
  assume "v \<in> used_vars st"
  thus ?thesis using Match by (cases eq, auto)
qed auto

lemma source_note_dest[dest]:
  "\<lbrakk> v \<in> sourced_vars st; noteStep st \<rbrakk> \<Longrightarrow> False"
by (auto dest: noteStepD)

lemma source_not_wildcard[dest]:
  "v \<in> sourced_vars st \<Longrightarrow> v \<notin> wildcards R st"
proof (cases st)
  case (Match lbl eq mv pt)
  assume "v \<in> sourced_vars st"
  thus ?thesis using Match by (cases eq, auto)
qed auto


definition aVars:: "role \<Rightarrow> varid set"
where
  "aVars role = foldr (\<lambda> st se. (AVar ` FAV_rolestep st) \<union> se) role {}"

lemma aVars_singleton[iff]:
  "AVar a \<notin> aVars []"
by(fastforce simp add: aVars_def)

lemma aVars_Nil [iff]: "aVars [] = {}"
  by (auto simp: aVars_def)

lemma aVars_Cons [simp]: "aVars (s#xs) = (AVar ` FAV_rolestep s \<union> aVars xs)"
  by (auto simp: aVars_def)

lemma aVars_FAV_conv:
  "(AVar a \<in> aVars R) = (\<exists> s \<in> set R. a \<in> FAV_rolestep s)"
by (induct R) ( fastforce simp add: aVars_def)+


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
qed (fastforce simp add: lastComStep_def)+

lemma firstComStep_Nil [iff]: "firstComStep [] = None"
  by (auto simp: firstComStep_def)

lemma firstComStep_Cons [simp]: "firstComStep (x#xs) =
  ( if (noteStep x) then
      firstComStep xs
    else
      Some x
  )"
proof (cases "[s\<leftarrow>xs . \<not> noteStep s]")
qed (fastforce simp add: firstComStep_def)+ 


end
