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
theory Message
imports Main
begin

chapter{* Security Protocol Model *}

section{* Cryptographic Messages *}


types id = string

text{*
  A general message datatype which is polymorphic over 
  the type of its literals.
*}

datatype 'lit msg = Lit  "'lit"
                  | Tup  "'lit msg" "'lit msg"
                  | Enc  "'lit msg" "'lit msg"
                  | Hash "'lit msg"
                  | K    "'lit msg" "'lit msg"
                  | PK   "'lit msg"
                  | SK   "'lit msg"


text{*Concrete syntax: messages appear as {|A,B,NA|}, etc...*}
syntax
  "@MTuple"      :: "['a, args] => 'a * 'b"       ("(2{|_,/ _|})")

syntax (xsymbols)
  "@MTuple"      :: "['a, args] => 'a * 'b"       ("(2\<lbrace>_,/ _\<rbrace>)")

translations
  "{|x, y, z|}"   == "{|x, {|y, z|}|}"
  "{|x, y|}"      == "Tup x y"



subsection{* Operations *}

fun inv :: "'lit msg \<Rightarrow> 'lit msg"
where
  "inv (PK m)  = SK m"
| "inv (SK m)  = PK m"
| "inv m       = m"

fun unpair :: "'lit msg \<Rightarrow> 'lit msg set"
where
  "unpair (Tup x y) = unpair x \<union> unpair y"
| "unpair m         = {m}"


text{* 
  We do not use neither subterms nor parts in our reasoning 
  infrastructure. However it used to formulate a few lemmas
  illustrating the relation between Paulsons' approach and ours.
*}

fun subterms :: "'lit msg \<Rightarrow> 'lit msg set"
where
  "subterms (Lit l)   = {Lit l}"
| "subterms (Tup x y) = insert (Tup x y) (subterms x \<union> subterms y)"
| "subterms (Enc m k) = insert (Enc m k) (subterms m \<union> subterms k)"
| "subterms (Hash m)  = insert (Hash m)  (subterms m)"
| "subterms (K a b)   = insert (K a b)   (subterms a \<union> subterms b)"
| "subterms (PK a)    = insert (PK a)    (subterms a)"
| "subterms (SK a)    = insert (SK a)    (subterms a)"

fun parts :: "'a msg \<Rightarrow> 'a msg set"
where
  "parts (Lit l)   = {Lit l}"
| "parts (Tup x y) = insert (Tup x y) (parts x \<union> parts y)"
| "parts (Enc m k) = insert (Enc m k) (parts m)"
| "parts (Hash m)  = {Hash m}"
| "parts (K a b)   = {K a b}"
| "parts (PK a)    = {PK a}"
| "parts (SK a)    = {SK a}"


fun pairParts :: "'a msg \<Rightarrow> 'a msg set"
where
  "pairParts (Tup x y) = 
      insert (Tup x y) (pairParts x \<union> pairParts y)"
| "pairParts m = {m}"

inductive_set
  infer :: "'a msg set \<Rightarrow> 'a msg set"
  for M :: "'a msg set"
where
  Inj [simp,intro]: "m \<in> M                     \<Longrightarrow> m \<in> infer M"
| Tup:  "\<lbrakk> x \<in> infer M; y \<in> infer M \<rbrakk>           \<Longrightarrow> Tup x y \<in> infer M"
| Fst:  "Tup x y \<in> infer M                      \<Longrightarrow> x \<in> infer M"
| Snd:  "Tup x y \<in> infer M                      \<Longrightarrow> y \<in> infer M"
| Hash: "m \<in> infer M                            \<Longrightarrow> Hash m \<in> infer M"
| Enc:  "\<lbrakk> m \<in> infer M; k \<in> infer M \<rbrakk>           \<Longrightarrow> Enc m k \<in> infer M"
| Dec:  "\<lbrakk> Enc m k \<in> infer M; inv k \<in> infer M \<rbrakk> \<Longrightarrow> m \<in> infer M"
  

subsection{* Properties *}

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


end
