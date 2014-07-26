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
theory ExecMessage
imports
  HOL_ext
  Protocol
begin

subsection{* Execution Messages *}

typedef tid = "UNIV :: nat set" by blast

datatype execlit = EConst   id
                 | EAgent   id
                 | ENonce   id tid
                 | EveNonce id

datatype execmsg = Lit  execlit
                 | Tup  execmsg execmsg
                 | Enc  execmsg execmsg
                 | Hash execmsg
                 | K    execmsg execmsg
                 | KShr "id set"    (* a set of agent sharing this key *)
                 | PK   execmsg
                 | SK   execmsg


text{*Concrete syntax: messages appear as {|A,B,NA|}, etc...*}
syntax
  "@MTuple"      :: "['a, args] => 'a * 'b"       ("(2{|_,/ _|})")

syntax (xsymbols)
  "@MTuple"      :: "['a, args] => 'a * 'b"       ("(2\<lbrace>_,/ _\<rbrace>)")

translations
  "{|x, y, z|}"   == "{|x, {|y, z|}|}"
  "{|x, y|}"      == "(CONST Tup) x y"


text{* 
  A shallow reference to bi-directional keys between two agents.
  Used only in proofs, but not in specifications. Hence, it can
  be ignored for soundness.
*}
definition Agent :: "execmsg set"
where "Agent \<equiv> { Lit (EAgent a) | a. True}"

definition agents :: "execmsg set \<Rightarrow> id set"
where "agents M = {a. Lit (EAgent a) \<in> M}"

definition Kbd :: "execmsg \<Rightarrow> execmsg \<Rightarrow> execmsg"
where "Kbd a b = (if (a \<in> Agent \<and> b \<in> Agent) 
                  then KShr (agents {a, b}) 
                  else undefined)"

lemma Kbd_commute [simp]: 
  "Kbd x y = Kbd y x"
  by (auto simp: Kbd_def agents_def)

lemma size_Kbd [simp]: 
  "\<lbrakk> a \<in> Agent; b \<in> Agent \<rbrakk> \<Longrightarrow> size (Kbd a b) = 0"
  by ( auto simp: Kbd_def)

lemma Kbd_free [simp]:
  "\<lbrakk> a \<in> Agent; b \<in> Agent \<rbrakk> \<Longrightarrow> Kbd a b \<noteq> Lit l"
  "\<lbrakk> a \<in> Agent; b \<in> Agent \<rbrakk> \<Longrightarrow> Kbd a b \<noteq> Tup x y"
  "\<lbrakk> a \<in> Agent; b \<in> Agent \<rbrakk> \<Longrightarrow> Kbd a b \<noteq> Enc x y"
  "\<lbrakk> a \<in> Agent; b \<in> Agent \<rbrakk> \<Longrightarrow> Kbd a b \<noteq> Hash x"
  "\<lbrakk> a \<in> Agent; b \<in> Agent \<rbrakk> \<Longrightarrow> Kbd a b \<noteq> K x y"
  "\<lbrakk> a \<in> Agent; b \<in> Agent \<rbrakk> \<Longrightarrow> Kbd a b \<noteq> PK x"
  "\<lbrakk> a \<in> Agent; b \<in> Agent \<rbrakk> \<Longrightarrow> Kbd a b \<noteq> SK x"
  by (auto simp: Kbd_def)

declare Kbd_free[symmetric, simp]

lemma Kbd_split_inj:
  "\<lbrakk> a \<in> Agent; b \<in> Agent; x \<in> Agent; y \<in> Agent \<rbrakk> \<Longrightarrow>
   (Kbd a b = Kbd x y) = (a = x \<and> b = y \<or> a = y \<and> b = x)"
  apply(clarsimp simp: Kbd_def Agent_def agents_def set_eq_iff) 
  apply(rule iffI)
  apply(rename_tac a b x y)
  apply(safe)
  apply(drule_tac x="a" in spec)
  apply(simp)
  apply(drule_tac x="y" in spec)
  apply(simp)
  apply(drule_tac x="x" in spec)
  apply(simp)
  apply(drule_tac x="b" in spec)
  apply(simp)
  done

lemma Kbd_non_split_inj [simp]:
  "\<lbrakk> a \<in> Agent; b \<in> Agent; x \<in> Agent \<rbrakk>
   \<Longrightarrow> (Kbd a b = Kbd x b) = (a = x)"
  "\<lbrakk> a \<in> Agent; b \<in> Agent; x \<in> Agent \<rbrakk>
   \<Longrightarrow> (Kbd a b = Kbd b x) = (a = x)"
  "\<lbrakk> a \<in> Agent; b \<in> Agent; x \<in> Agent \<rbrakk>
   \<Longrightarrow> (Kbd b a = Kbd x b) = (a = x)"
  "\<lbrakk> a \<in> Agent; b \<in> Agent; x \<in> Agent \<rbrakk>
   \<Longrightarrow> (Kbd b a = Kbd b x) = (a = x)"
  "\<lbrakk> a \<in> Agent; y \<in> Agent; x \<in> Agent \<rbrakk>
   \<Longrightarrow> (Kbd a a = Kbd x y) = (a = y \<and> x = y)"
  "\<lbrakk> a \<in> Agent; b \<in> Agent; x \<in> Agent \<rbrakk>
   \<Longrightarrow> (Kbd a b = Kbd x x) = (a = x \<and> b = x)"
  by (auto simp: Kbd_split_inj)

lemma Kbd_cases [ consumes 1
                , case_names Agent_a Agent_b Agent_x Agent_y noswap swapped]:
  "\<lbrakk> Kbd a b = Kbd x y;
     a \<in> Agent; b \<in> Agent; 
     x \<in> Agent; y \<in> Agent; 
     \<lbrakk> a = x; b = y \<rbrakk> \<Longrightarrow> R; 
     \<lbrakk> a = y; b = x \<rbrakk> \<Longrightarrow> R
   \<rbrakk> \<Longrightarrow> R"
  by (auto simp: Kbd_split_inj)

subsection{* Operations *}

type_synonym store = "varid \<times> tid \<Rightarrow> execmsg"

text{* Key inversion *}
fun inv :: "execmsg \<Rightarrow> execmsg"
where
  "inv (PK m)  = SK m"
| "inv (SK m)  = PK m"
| "inv m       = m"

lemma inv_Kbd [simp]: 
  "\<lbrakk> a \<in> Agent; b \<in> Agent \<rbrakk> \<Longrightarrow> inv (Kbd a b) = Kbd a b"
  by(auto simp: Kbd_def)


text{* Instantiating a pattern *}
fun inst :: "store \<Rightarrow> tid \<Rightarrow> pattern \<Rightarrow> execmsg option"
where
  "inst s i (PConst c)   = Some (Lit (EConst c))"
| "inst s i (PFresh n)   = Some (Lit (ENonce  n i))"
| "inst s i (PVar   v)   = Some (s (v, i))"
| "inst s i (PTup x y)   = opt_map2 Tup (inst s i x) (inst s i y)"
| "inst s i (PEnc m k)   = opt_map2 Enc (inst s i m) (inst s i k)"
| "inst s i (PSign m k)  = 
     opt_map2 Tup (inst s i m) 
         (opt_map2 Enc  (inst s i m) (Option.map inv (inst s i k)))"
| "inst s i (PHash m)    = Option.map Hash (inst s i m)"
| "inst s i (PSymK a b)  = opt_map2   K    (inst s i a) (inst s i b)"
| "inst s i (PAsymPK a)  = Option.map PK   (inst s i a)"
| "inst s i (PAsymSK a)  = Option.map SK   (inst s i a)"
| "inst s i (PShrK V)    = 
     (if   (\<forall> v \<in> V. s (v, i) \<in> Agent)
      then Some (KShr (agents {s (v, i) | v. v \<in> V})) 
      else None)"
| "inst s i (PAny)       = None"

text{* Instantiate a pattern and export wildcards *}
fun any_inst :: "store \<Rightarrow> tid \<Rightarrow> pattern \<Rightarrow> (execmsg, execmsg option) varfun"
where
  "any_inst s i (PConst c)  = Val (Some (Lit (EConst c)))"
| "any_inst s i (PFresh n)  = Val (Some (Lit (ENonce n i)))"
| "any_inst s i (PVar v)    = Val (Some (s (v, i)))"
| "any_inst s i (PTup x y)  = var_lift2 (opt_map2 Tup) (any_inst s i x) (any_inst s i y)"
| "any_inst s i (PEnc m k)  = var_lift2 (opt_map2 Enc) (any_inst s i m) (any_inst s i k)"
| "any_inst s i (PSign m k) = var_lift2
    (\<lambda>m' k'. opt_map2 Tup m' (opt_map2 Enc m' (Option.map inv k')))
    (any_inst s i m) (any_inst s i k)"
| "any_inst s i (PHash m)   = var_map (Option.map Hash) (any_inst s i m)"
| "any_inst s i (PSymK a b) = var_lift2 (opt_map2 K) (any_inst s i a) (any_inst s i b)"
| "any_inst s i (PAsymPK a) = var_map (Option.map PK) (any_inst s i a)"
| "any_inst s i (PAsymSK a) = var_map (Option.map SK) (any_inst s i a)"
| "any_inst s i (PShrK V)   = Val (inst s i (PShrK V))"
| "any_inst s i (PAny)      = Fun (\<lambda>m. Val (Some m))"


text{* We assume that recipients making use of shared keys look them up
       in a table. This lookup only succeeds if agent identities are 
       given.
*}

lemma Some_inst_sKbd [simp]:
  "(Some m = inst s i (sKbd a b)) = 
   (m = Kbd (s (a, i)) (s (b, i)) \<and> 
    s (a, i) \<in> Agent \<and> s (b, i) \<in> Agent
   )"
  by (auto simp: sKbd_def Kbd_def Agent_def agents_def)


fun unpair :: "execmsg \<Rightarrow> execmsg set"
where
  "unpair (Tup x y) = unpair x \<union> unpair y"
| "unpair m         = {m}"


text{* 
  We do not use neither subterms nor parts in our reasoning 
  infrastructure. However it used to formulate a few lemmas
  illustrating the relation between Paulsons' approach and ours.
*}

fun subterms :: "execmsg \<Rightarrow> execmsg set"
where
  "subterms (Lit l)   = {Lit l}"
| "subterms (Tup x y) = insert (Tup x y) (subterms x \<union> subterms y)"
| "subterms (Enc m k) = insert (Enc m k) (subterms m \<union> subterms k)"
| "subterms (Hash m)  = insert (Hash m)  (subterms m)"
| "subterms (K a b)   = insert (K a b)   (subterms a \<union> subterms b)"
| "subterms (PK a)    = insert (PK a)    (subterms a)"
| "subterms (SK a)    = insert (SK a)    (subterms a)"
| "subterms (KShr A)  = insert (KShr A)  {Lit (EAgent a) | a. a \<in> A}"

fun parts :: "execmsg \<Rightarrow> execmsg set"
where
  "parts (Lit l)   = {Lit l}"
| "parts (Tup x y) = insert (Tup x y) (parts x \<union> parts y)"
| "parts (Enc m k) = insert (Enc m k) (parts m)"
| "parts (Hash m)  = {Hash m}"
| "parts (K a b)   = {K a b}"
| "parts (PK a)    = {PK a}"
| "parts (SK a)    = {SK a}"
| "parts (KShr A)  = {KShr A}"


fun pairParts :: "execmsg \<Rightarrow> execmsg set"
where
  "pairParts (Tup x y) = 
      insert (Tup x y) (pairParts x \<union> pairParts y)"
| "pairParts m = {m}"

lemma pairParts_Kbd [simp]: 
  "\<lbrakk> a \<in> Agent; b \<in> Agent \<rbrakk> \<Longrightarrow> pairParts (Kbd a b) = {Kbd a b}"
  by (auto simp: Kbd_def)

inductive_set
  infer :: "execmsg set \<Rightarrow> execmsg set"
  for M :: "execmsg set"
where
  Inj [simp,intro]: "m \<in> M                     \<Longrightarrow> m \<in> infer M"
| Tup:  "\<lbrakk> x \<in> infer M; y \<in> infer M \<rbrakk>           \<Longrightarrow> Tup x y \<in> infer M"
| Fst:  "Tup x y \<in> infer M                      \<Longrightarrow> x \<in> infer M"
| Snd:  "Tup x y \<in> infer M                      \<Longrightarrow> y \<in> infer M"
| Hash: "m \<in> infer M                            \<Longrightarrow> Hash m \<in> infer M"
| Enc:  "\<lbrakk> m \<in> infer M; k \<in> infer M \<rbrakk>           \<Longrightarrow> Enc m k \<in> infer M"
| Dec:  "\<lbrakk> Enc m k \<in> infer M; inv k \<in> infer M \<rbrakk> \<Longrightarrow> m \<in> infer M"
  

subsection{* Properties *}

subsubsection{* Agents *}

lemma notin_Agent [iff]:
  "Lit (EConst x)   \<notin> Agent"
  "Lit (EAgent x)   \<in> Agent"
  "Lit (ENonce x i)   \<notin> Agent"
  "Lit (EveNonce x) \<notin> Agent"
  "Tup m1 m2 \<notin> Agent"
  "Enc m1 m2 \<notin> Agent"
  "Hash m1 \<notin> Agent"
  "K m1 m2 \<notin> Agent"
  "KShr V \<notin> Agent"
  "PK m1 \<notin> Agent"
  "SK m1 \<notin> Agent"
  "\<lbrakk> a \<in> Agent; b \<in> Agent \<rbrakk> \<Longrightarrow> Kbd a b \<notin> Agent"
  by (auto simp: Kbd_def Agent_def)


subsubsection{* Unification modulo key-inversion *}

lemma size_inv [simp]: "size (inv x) = size x"
  by (cases x) auto

lemma inv_eqs [iff]:
  "(inv x = Lit m)     = (x = Lit m)"
  "(inv x = Tup m1 m2) = (x = Tup m1 m2)"
  "(inv x = Enc m1 m2) = (x = Enc m1 m2)"
  "(inv x = Hash m1)   = (x = Hash m1)"
  "(inv x = K m1 m2)   = (x = K m1 m2)"
  "(inv x = PK m1)     = (x = SK m1)"
  "(inv x = SK m1)     = (x = PK m1)"
  "(Lit m = inv x)     = (x = Lit m)"
  "(Tup m1 m2 = inv x) = (x = Tup m1 m2)"
  "(Enc m1 m2 = inv x) = (x = Enc m1 m2)"
  "(Hash m1 = inv x)   = (x = Hash m1)"
  "(K m1 m2 = inv x)   = (x = K m1 m2)"
  "(PK m1 = inv x)     = (x = SK m1)"
  "(SK m1 = inv x)     = (x = PK m1)"
  "(KShr A = inv x)    = (x = KShr A)"
  "\<lbrakk> a \<in> Agent; b \<in> Agent \<rbrakk> \<Longrightarrow> 
   (Kbd a b = inv x)    = (x = Kbd a b)"
 by (auto) (induct x, simp+)+

lemma inv_inj [iff]:
  "(inv x = inv y) = (x = y)"
  by (auto) (induct x, auto)


subsubsection{* @{term subterms}  *}

lemma subterms_trans: 
  "\<lbrakk> x \<in> subterms y; y \<in> subterms z \<rbrakk> \<Longrightarrow> x \<in> subterms z"
  by(induct z, auto)

lemma unpair_subset_subterms: 
  "unpair m \<subseteq> subterms m"
  by(induct m, auto)

lemmas unpair_subtermsD = 
  subsetD[OF unpair_subset_subterms, rule_format]


subsubsection{* @{term infer} *}

text{* Monotonicity *}

lemma infer_mono [trans]: "M \<subseteq> N \<Longrightarrow> infer M \<subseteq> infer N"
  by(auto, erule infer.induct, auto intro: infer.intros)

lemma infer_increasing: "M \<subseteq> infer M"
  by(blast)


text{* Converse fails: A message composed from subterms of both
  sets is not in the union of the individual inferable sets. *}
lemma infer_Un: "infer M \<union> infer N \<subseteq> infer (M \<union> N)"
  by(intro Un_least infer_mono Un_upper1 Un_upper2)

lemmas infer_UnD = subsetD[OF infer_Un, rule_format]

lemma infer_insert: "insert x (infer M) \<subseteq> infer (insert x M)"
  by(blast intro: infer_mono[THEN [2] rev_subsetD])


text{* Idempotence and transitivity *}

lemma infer_inferD [dest!]: "x \<in> infer (infer M) \<Longrightarrow> x \<in> infer M"
  by (induct rule: infer.induct) (auto intro: infer.intros)

lemma infer_idem [iff]: "infer (infer M) = infer M"
  by blast

lemma infer_subset_iff [simp]: 
  "(infer M \<subseteq> infer N) = (M \<subseteq> infer N)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  have "M \<subseteq> infer M" by(rule infer_increasing)
  also note `?lhs`
  finally show ?rhs .
next
  assume ?rhs
  hence "infer M \<subseteq> infer (infer N)" by(rule infer_mono)
  thus ?lhs by simp
qed

lemma infer_trans: "\<lbrakk> x \<in> infer M;  M \<subseteq> infer N  \<rbrakk> \<Longrightarrow> x \<in> infer N"
by (drule infer_mono, blast)

text{*Cut; Lemma 2 of Lowe*}
lemma infer_cut: 
  "\<lbrakk> y \<in> infer (insert x M);  x \<in> infer M \<rbrakk> \<Longrightarrow> y \<in> infer M"
  by (erule infer_trans, blast)


lemma Tup_in_infer [simp]: 
  "Tup x y \<in> infer M = (x \<in> infer M \<and> y \<in> infer M)"
  by(blast intro: infer.intros)

lemma infer_insert_Tup [simp]:
  "infer (insert (Tup x y) M) = infer (insert x (insert y M))"
  by(safe, (erule infer.induct, auto intro: infer.intros)+)

lemma infer_insertI [intro]: "x \<in> infer M \<Longrightarrow> x \<in> infer (insert y M)"
  by(erule rev_subsetD[OF _ infer_mono], blast)

lemma infer_finite_support: 
  assumes "m \<in> infer M"
  shows "\<exists> N. N \<subseteq> M \<and> finite N \<and> m \<in> infer N"  (is "\<exists> N. ?support m N")
using assms
proof(induct rule: infer.induct)
  case (Inj m)
    hence "?support m {m}" by fast
    thus ?case by blast
next
  case (Hash m)
    then obtain Nm where "?support m Nm" by blast
    hence "?support (Hash m) Nm" by (blast intro: infer.intros)
    thus ?case by blast
next
  case (Tup x y) note IH = this
             obtain Nx where "?support x Nx" using IH by blast
    moreover obtain Ny where "?support y Ny" using IH by blast
    ultimately have "?support (Tup x y) (Nx \<union> Ny)" 
      by (blast intro: infer.intros infer_UnD)
    thus ?case by blast
next
  case (Fst x y)
    then obtain Nxy where "?support \<lbrace>x, y\<rbrace> Nxy" by blast
    hence "?support x Nxy" by (blast intro: infer.intros)
    thus ?case by blast
next
  case (Snd x y)
    then obtain Nxy where "?support \<lbrace>x, y\<rbrace> Nxy" by blast
    hence "?support y Nxy" by (blast intro: infer.intros)
    thus ?case by blast
next
  case (Enc m k) note IH = this
             obtain Nm where "?support m Nm" using IH by blast
    moreover obtain Nk where "?support k Nk" using IH by blast
    ultimately have "?support (Enc m k) (Nm \<union> Nk)" 
      by (blast intro: infer.intros infer_UnD)
    thus ?case by blast
next
  case (Dec m k) note IH = this
             obtain Nmk where "?support (Enc m k) Nmk" using IH by blast
    moreover obtain Nk where "?support (inv k) Nk" using IH by blast
    ultimately have "?support m (Nmk \<union> Nk)" 
      by (blast intro: infer.intros infer_UnD)
    thus ?case by blast
qed



subsubsection{* @{term pairParts} *}

lemma pairParts_mono [iff]: "m \<in> pairParts m"
  by(induct m rule: pairParts.induct, auto)

lemma pairParts_idem: 
  "m' \<in> pairParts m \<Longrightarrow> pairParts m' \<subseteq> pairParts m"
  by(induct m, auto)

lemmas pairParts_idemD = 
  subsetD[OF pairParts_idem, rule_format]

lemma pairParts_in_infer:
  "\<lbrakk> x \<in> pairParts m; m \<in> infer M \<rbrakk> \<Longrightarrow> x \<in> infer M"
  by(induct m arbitrary: x, auto)

lemma unpair_subset_pairParts: "unpair m \<subseteq> pairParts m"
  by(induct m, auto)

lemmas unpair_subset_pairPartsD =
  subsetD[OF unpair_subset_pairParts, rule_format]


subsection{* Initial Intruder Knowledge *}


definition IK0 :: "execmsg set"
where "IK0 \<equiv> 
  { Lit (EConst c)       | c. True} \<union>
  { Lit (EveNonce a)     | a. True} \<union>
  { Lit (EAgent a)       | a. True} \<union>
  { PK  (Lit (EAgent a)) | a. True} \<union> 
  { KShr {} }"

lemma IK0_unpair_inv: "m \<in> IK0 \<Longrightarrow> unpair m = {m}"
  by(auto simp: IK0_def image_def)

lemma in_IK0_by_unpair: 
  "\<lbrakk> m \<in> unpair m'; m' \<in> IK0 \<rbrakk> \<Longrightarrow> m \<in> IK0"
  by(frule IK0_unpair_inv, auto)

lemma notin_IK0 [iff]:
  "SK a \<notin> IK0"
  "K a b \<notin> IK0"
  "Enc m k \<notin> IK0"
  "Hash m \<notin> IK0"
  "Lit (ENonce n i) \<notin> IK0"
  "Tup x y \<notin> IK0"
  "A \<noteq> {} \<Longrightarrow> KShr A \<notin> IK0"
  "\<lbrakk> a \<in> Agent; b \<in> Agent \<rbrakk> \<Longrightarrow> Kbd a b \<notin> IK0"
  by (auto simp: IK0_def Kbd_def agents_def Agent_def)

lemma in_IK0_simps [iff]:
  "Lit (EConst c) \<in> IK0"
  "Lit (EveNonce n) \<in> IK0"
  "Lit (EAgent a) \<in> IK0"
  "PK  (Lit (EAgent a)) \<in> IK0"
  "KShr {} \<in> IK0"
  by(auto simp: IK0_def)

end
