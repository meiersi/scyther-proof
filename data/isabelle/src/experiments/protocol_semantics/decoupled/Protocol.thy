theory Protocol
imports 
  DistinctList
begin

section{* Protocol Specifications *}

subsection{* Types and Operations *}

subsubsection{* Specification Messages *}

text{* 
  We specialize the cryptographic to specification messages by
  providing a type for the literals.
*}

types id = string

datatype varid = AVar id | MVar id

datatype speclit = SConst id 
                 | SVar   varid
                 | SNonce id

datatype pattern = 



types specmsg = "speclit msg"

text{* Free variables *}
fun FV :: "specmsg \<Rightarrow> varid set"
where 
  "FV (Lit (SVar v)) = {v}"
| "FV (Lit _)        = {}"
| "FV (Tup x y)      = FV x \<union> FV y"
| "FV (Enc m k)      = FV m \<union> FV k"
| "FV (Hash m)       = FV m"
| "FV (K a b)        = FV a \<union> FV b"
| "FV (PK a)         = FV a"
| "FV (SK a)         = FV a"


subsubsection{* Roles *}

text{*
  Roles are non-empty lists of unique send and receive steps 
  such that no long-term keys are used in message texts and all 
  nonce variables are received before they are sent.

  The labels allow to make steps with identical message unique.
  They are currently defaulted to strings, but could be anything.
*}

types lbl = string

datatype rolestep = Send lbl specmsg | Recv lbl specmsg

fun stepMsg :: "rolestep \<Rightarrow> specmsg"
where
  "stepMsg (Send lbl msg) = msg"
| "stepMsg (Recv lbl msg) = msg"

fun sendStep :: "rolestep \<Rightarrow> bool"
where
  "sendStep (Send lbl msg) = True"
| "sendStep (Recv lbl msg) = False"

abbreviation recvStep where "recvStep x \<equiv> \<not>sendStep x"

types "role" = "rolestep list"

fun recv_before_send :: "varid set \<Rightarrow> role \<Rightarrow> bool"
where
  "recv_before_send bound []                = True"
| "recv_before_send bound (Recv _ msg # xs) = 
     recv_before_send (bound \<union> FV msg) xs"
| "recv_before_send bound (Send _ msg # xs) =
     ((\<forall> v. MVar v \<in> FV msg \<longrightarrow> MVar v \<in> bound) \<and> 
      recv_before_send bound xs)"

locale wf_role =
  distinct_list R for R :: "role" +
  assumes recv_before_send [iff]: "recv_before_send {} R"

  
subsubsection{* Protocols *}

types proto = "role set"

locale wf_proto =
  fixes P :: proto
  assumes wf_roles: "R \<in> P \<Longrightarrow> wf_role R"


subsection{* Properties *}

subsubsection{* Well-Formed Roles *}

lemma recv_before_sent_distinct_Send_FV:
  "\<lbrakk>  recv_before_send V (R@ Send lbl msg # R'); 
      distinct (R @ Send lbl msg # R');
      MVar v \<in> FV msg; MVar v \<notin> V 
   \<rbrakk> \<Longrightarrow>
   \<exists> lbl' msg'. Recv lbl' msg' \<in> set R \<and> MVar v \<in> FV msg'"
proof(induct R arbitrary: V)
  case (Cons step R) note IH = this show ?case
    proof(cases step)
      case (Send lbl msg) thus ?thesis using IH by auto
    next
      case (Recv lbl msg) thus ?thesis using IH by (auto, fast)
    qed
qed simp


context wf_role
begin


lemma Send_FV:
  assumes Send: "Send lbl msg \<in> set R" (is "?send \<in> set R")
      and FV:   "MVar v \<in> FV msg"
  shows "\<exists> lbl' msg'. listOrd R (Recv lbl' msg') (Send lbl msg) \<and> MVar v \<in> FV msg'" 
using Send 
proof -
  let ?send = "Send lbl msg"
    and "\<exists> lbl' msg'. ?received lbl' msg'" = ?thesis
  assume "?send \<in> set R" then
  obtain ys zs 
    where split: "R = ys @ ?send # zs" by (blast dest!: split_list)
  moreover have "distinct R" and "recv_before_send {} R" by auto
  ultimately obtain lbl' msg' where "Recv lbl' msg' \<in> set ys" 
                                and "MVar v \<in> FV msg'"
             by (fastsimp dest!: recv_before_sent_distinct_Send_FV intro!: FV)
  hence "?received lbl' msg'" using split by auto
  thus ?thesis by blast
qed


end

end