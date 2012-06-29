(*****************************************************************************
 * ESPL --- an embedded security protocol logic
 *          http://people.inf.ethz.ch/meiersi/espl/
 *
 *   Copyright (c) 2009-2011, Simon Meier, ETH Zurich, Switzerland
 *
 * All rights reserved. See file LICENCE for more information.
 ******************************************************************************)
theory DistinctList
imports Main
begin

chapter{* Preliminaries *}

section{* Splitting Lists *}


fun splits :: "'a list \<Rightarrow> ('a list \<times> 'a list) list"
where
  "splits [] = [([],[])]"
| "splits (x#xs) = ([],x#xs) # map (\<lambda>(pre,suf). (x#pre,suf)) (splits xs)"

lemma in_set_splits_conv: 
  "((ys,zs) \<in> set (splits xs)) = (xs = ys @ zs)"
by(induct xs arbitrary: ys zs) (auto simp: Cons_eq_append_conv)


section{* Distinct Lists *}

lemma distinct_in_set_decomp: 
  assumes "x \<in> set xs" and "distinct xs"
  shows "\<exists> ys zs. xs = ys@ x # zs \<and> 
            x \<notin> set ys \<and> x \<notin> set zs \<and> set ys \<inter> set zs = {}"
        (is "\<exists> ys zs. ?split xs ys zs")
using assms
proof(induct xs)
  case (Cons a xs)
    hence "x = a \<or> x \<in> set xs" (is "?hd \<or> ?tl") by simp
    moreover
    { assume ?hd 
      hence "?split (a#xs) [] xs" using Cons by auto
      hence ?case by fast
    }
    moreover
    { assume ?tl then 
      obtain ys zs where "?split xs ys zs" using Cons by auto
      with Cons have "?split (a#xs) (a#ys) zs" by auto
      hence ?case by fast
    }
    ultimately show ?case by fast
  next
qed simp


subsection{* Direct Predecessors *}

fun "nextRel" :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "nextRel []       a b = False"
| "nextRel [x]      a b = False"
| "nextRel (x#y#xs) a b = ((a = x \<and> b = y) \<or> (nextRel (y#xs) a b))"

lemma nextRelI: "xs = ys@x#y#zs \<Longrightarrow> nextRel xs x y"
  by (induct xs x y arbitrary: ys rule: nextRel.induct)
     (auto simp: Cons_eq_append_conv)

lemma nextRelD:
  "nextRel xs x y \<Longrightarrow> (\<exists> ys zs. xs = ys@x#y#zs)"
  by (induct xs x y arbitrary: ys rule: nextRel.induct)
     (auto simp: Cons_eq_append_conv)

lemma nextRel_conv:
  "(nextRel xs x y) = (\<exists> ys zs. xs = ys@x#y#zs)"
  by(auto intro: nextRelI nextRelD)

lemma in_set_nextRel1: "nextRel xs x y \<Longrightarrow> x \<in> set xs"
  by(auto simp: nextRel_conv)

lemma in_set_nextRel2: "nextRel xs x y \<Longrightarrow> y \<in> set xs"
  by(auto simp: nextRel_conv)

lemma nextRel_rev:
  "nextRel (rev xs) x y = nextRel xs y x"
unfolding nextRel_conv
proof
  assume "\<exists>ys zs. xs = ys @ y # x # zs" then
  obtain ys zs where "xs = ys @ y # x # zs" by fast
  then have "rev xs = rev (ys @ y # x # zs)" by (rule arg_cong)
  then show "\<exists>ys zs. rev xs = ys @ x # y # zs" by auto
next
  assume "\<exists>ys zs. rev xs = ys @ x # y # zs" then
  obtain ys zs where "rev xs = ys @ x # y # zs" by fast
  then have "rev (rev xs) = rev (ys @ x # y # zs)" by (rule arg_cong)
  then show "\<exists>ys zs. xs = ys @ y # x # zs" by auto
qed


text{* Specialized instances of nextRel_rev for Snoc appends *}
lemma nextRel_Snoc_simps:
  "nextRel (xs@[a])   x y = nextRel (a#rev xs)   y x"
  "nextRel (xs@[a,b]) x y = nextRel (b#a#rev xs) y x"
  by(subst nextRel_rev[symmetric], simp)+

lemma nextRel_Cons_simps:
  "x \<noteq> y \<Longrightarrow> nextRel (x#xs) y z = nextRel xs y z"
  "x' \<noteq> z \<Longrightarrow> nextRel (x#x'#xs) y z = nextRel (x'#xs) y z"
  by (cases xs) simp+

lemmas nextRel_simps [simp] = 
  nextRel_rev nextRel_Snoc_simps nextRel_Cons_simps
  
lemma nextRelI_direct [simp,intro!]: "nextRel (xs@x#y#ys) x y"
  by(auto simp: nextRel_conv)

lemma nextRel_appendI1:
  "nextRel xs x y \<Longrightarrow> nextRel (xs@ys) x y"
  by(induct xs x y rule: nextRel.induct) auto



subsection{* Predecessors *}

fun listOrd :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "listOrd []     a b = False"
| "listOrd (x#xs) a b = ((a = x \<and> b \<in> set xs) \<or> listOrd xs a b)"

lemma in_set_listOrd1: "listOrd xs x y \<Longrightarrow> x \<in> set xs"
  by(induct xs, auto)

lemma in_set_listOrd2: "listOrd xs x y \<Longrightarrow> y \<in> set xs"
  by(induct xs, auto)

lemma listOrd_append [simp]: 
  "listOrd (xs@ys) a b = 
   (listOrd xs a b \<or> listOrd ys a b \<or> (a \<in> set xs \<and> b \<in> set ys))"
  by(induct xs, auto)

lemma listOrd_rev [simp]: "listOrd (rev xs) x y = listOrd xs y x"
  by(induct xs, auto)

lemma nextRel_imp_listOrd: "nextRel xs x y \<Longrightarrow> listOrd xs x y"
  by(induct xs x y rule: nextRel.induct) auto

lemma listOrd_filter: "listOrd (filter p xs) x y \<Longrightarrow> listOrd xs x y"
  by(induct xs) (auto split: if_splits)

lemma listOrd_takeWhile: "listOrd (takeWhile p xs) x y \<Longrightarrow> listOrd xs x y"
proof(induct xs)
case Nil
  thus ?case by auto
next
case (Cons a xs)
  thus ?case by(auto split: if_splits dest: set_takeWhileD)
qed 

lemma list_Ord_singleton[simp]: "listOrd [a] x y \<Longrightarrow> False"
  by auto

lemma listOrd_distinct_irr [simp]: "distinct xs \<Longrightarrow> \<not>listOrd xs x x"
  by(induct xs, auto)

lemma listOrd_distinct_trans: 
  "\<lbrakk> listOrd xs x y; listOrd xs y z; distinct xs \<rbrakk> 
   \<Longrightarrow> listOrd xs x z"
  by (induct xs) (auto dest: in_set_listOrd1 in_set_listOrd2)

lemma listOrd_distinct_asymD: 
  "\<lbrakk> listOrd xs x y; distinct xs \<rbrakk> \<Longrightarrow> \<not> listOrd xs y x"
  by (induct xs) (auto dest: in_set_listOrd1 in_set_listOrd2)

lemma listOrd_distinct_cases: 
  "\<lbrakk> x \<in> set xs; y \<in> set xs; distinct xs \<rbrakk> 
   \<Longrightarrow> x = y \<or> listOrd xs x y \<or> listOrd xs y x"
  by(induct xs, auto)

definition listEqOrd :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "listEqOrd xs x y \<equiv> (x = y) \<or> listOrd xs x y"


subsection{* List Order *}

locale distinct_list = 
  fixes   xs :: "'a list"
  assumes distinct [simp,intro!]: "distinct xs"
begin
  abbreviation "next" (infixl "\<prec>\<^sub>1" 50) where "next \<equiv> nextRel xs"
  abbreviation pred (infixl "\<prec>" 50) where "pred \<equiv> listOrd xs"
  abbreviation predEq (infixl "\<preceq>" 50) where "predEq \<equiv> listEqOrd xs"
end

text{* Aquiring the order properties *}

sublocale distinct_list \<subseteq> order "predEq" "pred"
  by unfold_locales
     (auto simp: listEqOrd_def
           dest: listOrd_distinct_asymD 
          intro: listOrd_distinct_trans)


text{* Relating @{term next} to the order *}

context distinct_list begin

lemma next_imp_less: "x \<prec>\<^sub>1 y \<Longrightarrow> x \<prec> y"
  by(auto simp: listEqOrd_def  
         dest!: nextRel_imp_listOrd)

lemma next_imp_le: "x \<prec>\<^sub>1 y \<Longrightarrow> x \<preceq> y"
  by(auto dest: next_imp_less)

lemma in_set_less1: "x \<prec> y \<Longrightarrow> x \<in> set xs"
  by(simp add: pred_def in_set_listOrd1)

lemma in_set_less2: "x \<prec> y \<Longrightarrow> y \<in> set xs"
  by(simp add: pred_def in_set_listOrd2)

lemmas in_set_next1 = in_set_less1[OF next_imp_less, rule_format]
lemmas in_set_next2 = in_set_less2[OF next_imp_less, rule_format]


end


end
