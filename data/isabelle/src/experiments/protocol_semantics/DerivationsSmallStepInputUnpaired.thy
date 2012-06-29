theory DerivationsSmallStep
imports
  HOL_ext
  Hints
  Protocol
  ExecMessage
begin


chapter{* Security Proofs *}


section{* Networked Transition Systems *}

types 's nts = "'s \<times> ('s \<times> execmsg option \<times> 's \<times> execmsg option) set"

section{* Standard Execution Model *}

inductive_set 
  dy    :: "'s nts \<Rightarrow> ('s list \<times> execmsg set) set"
  for P :: "'s nts"
where
  init : "([fst P], {}) \<in> dy P"
| proto: 
  "\<lbrakk> (tr@[s], M) \<in> dy P;
     Option.set inp \<subseteq> M;
     (s, inp, s', out) \<in> snd P
   \<rbrakk> \<Longrightarrow>
     (tr@[s,s'], M \<union> Option.set out) \<in> dy P"     
| infer:
  "\<lbrakk> (tr, M) \<in> dy P;
     m \<in> infer M
   \<rbrakk> \<Longrightarrow>
     (tr, insert m M) \<in> dy P"


section{* Derivations *}

datatype 's node = State "nat \<times> 's" | Msg execmsg

types 's dependencies = "('s node \<times> 's node) set"

types 's derivation = "('s list \<times> 's dependencies)"

definition knows :: "'s dependencies \<Rightarrow> execmsg set"
where "knows D \<equiv> {m. Msg m \<in> Range D}"

inductive_set
  derivs :: "'s nts \<Rightarrow> 's derivation set"
  for P      :: "'s nts"
where
  init: "([fst P], {}) \<in> derivs P"

| proto:
  "\<lbrakk> (tr@[s], D) \<in> derivs P;
     Option.set inp \<subseteq> knows D;
     (s, inp, s', out) \<in> snd P
   \<rbrakk> \<Longrightarrow>
     ( tr@[s,s']
     , D \<union> (Msg ` (\<Union> mi \<in> Option.set inp. pairParts mi)) \<times>  
           {State (Suc (length tr), s')} 
         \<union> (\<Union> mo \<in> Option.set out. 
               {State (Suc (length tr), s')} \<times> 
               (Msg ` (pairParts mo - knows D)))
     ) \<in> derivs P"

| decr:
  "\<lbrakk> (tr, D) \<in> derivs P;
     Enc m k \<in> knows D;
     inv k \<in> knows D
   \<rbrakk> \<Longrightarrow> 
     ( tr
     , D \<union> (Msg ` insert (Enc m k) (pairParts (inv k))) \<times> 
           (Msg ` (pairParts m - knows D))
     ) \<in> derivs P"

| hash:
  "\<lbrakk> (tr, D) \<in> derivs P;
     m \<in> knows D;
     Hash m \<notin> knows D
   \<rbrakk> \<Longrightarrow> 
     (tr, D \<union> (Msg ` pairParts m) \<times> {Msg (Hash m)}) \<in> derivs P"

| tuple:
  "\<lbrakk> (tr, D) \<in> derivs P;
     x \<in> knows D;
     y \<in> knows D;
     Tup x y \<notin> knows D
   \<rbrakk> \<Longrightarrow> 
     (tr, (Msg ` (pairParts x \<union> pairParts y)) \<times> 
          {Msg (Tup x y)} \<union> D
     ) \<in> derivs P"

| encr:
  "\<lbrakk> (tr, D) \<in> derivs P;
     m \<in> knows D;
     k \<in> knows D;
     Enc m k \<notin> knows D
   \<rbrakk> \<Longrightarrow> 
     (tr, (Msg ` (pairParts m \<union> pairParts k)) \<times> 
          {Msg (Enc m k)} \<union> D
     ) \<in> derivs P"

locale derivation =
  fixes P  :: "'s nts"
  and   tr :: "'s list"
  and   D  :: "'s dependencies"
  assumes derivable: "(tr, D) \<in> derivs P"
begin

text{* A local variant of the induction rule of @{term "reachable"}. *}
lemmas derivs_induct = derivs.induct
  [ OF derivable
  , rule_format
  , consumes 0
  , case_names init proto decr hash tuple encr
  ]

lemma State2_to_trace:
  "(x, State (i, s)) \<in> D \<Longrightarrow> i < length tr"
  "(x, State (i, s)) \<in> D \<Longrightarrow> tr ! i = s"
by (induct rule: derivs_induct)
   (auto simp: nth_append)

lemmas State2_index_in_trace  = State2_to_trace(1)
lemmas State2_state_nth_trace = State2_to_trace(2)

end
lemma knows_iff: "(m \<in> knows D) = (\<exists> x. (x, Msg m) \<in> D)"
  by (auto simp: knows_def Range_iff)

lemma knows_Un [simp]: "knows (M \<union> N) = knows M \<union> knows N"
  by (auto simp: knows_def)

lemma knows_insert_Msg [simp]: "knows (insert (x, Msg m) D) = insert m (knows D)"
  by(auto simp: knows_def)

lemma knows_insert_State [simp]: "knows (insert (x, State s) D) = knows D"
  by(auto simp: knows_def)

lemma in_knows_times: "M \<noteq> {} \<Longrightarrow> (m \<in> knows (M \<times> N)) = (Msg m \<in> N)"
  by (auto simp: knows_iff)

lemma (in derivation) pairParts_before:
  "\<lbrakk> (Msg m, y) \<in> D; m' \<in> pairParts m \<rbrakk> \<Longrightarrow> (Msg m', y) \<in> D"
  by (induct rule: derivs_induct)
     (auto simp: image_def dest: pairParts_idemD)

lemma (in derivation) knows_pairParts_closed:
  "\<lbrakk> m \<in> knows D; x \<in> pairParts m \<rbrakk> \<Longrightarrow> x \<in> knows D"
proof(induct arbitrary: m rule: derivs_induct)
  case (tuple tr D mx my) thus ?case
    by(clarsimp, fastsimp simp: knows_iff)
qed (auto simp: knows_iff image_def dest: pairParts_idemD)

lemma (in derivation) Msg1_imp_Msg2:
  "(Msg m, y) \<in> D \<Longrightarrow> \<exists> x. (x, Msg m) \<in> D"
sorry
(*
proof(induct arbitrary: y rule: derivs_induct) 
  case proto thus ?case sorry
next
  case (hash r D m') thus ?case
    apply clarsimp
    apply(erule disjE)
    apply(fastsimp simp: knows_iff)
    apply(clarsimp)
    sorry

qed (auto simp: knows_iff)
*)

definition (in derivation) derivOrd
where "derivOrd = (D \<union> 
                   { (State (i, tr ! i), State (Suc i, tr ! Suc i))
                   | i. Suc i < length tr }
                  )\<^sup>+"


lemma irr_insert_tranclD:
  "\<lbrakk> (x,x) \<in> (insert (a,b) R)\<^sup>+; (b,a) \<notin> R\<^sup>+; (x,x) \<notin> R\<^sup>+ \<rbrakk> \<Longrightarrow> a = b"
  apply(clarsimp simp: trancl_insert)
  apply(subgoal_tac "(b,a) \<in>  R\<^sup>*")
  apply(simp add: rtrancl_eq_or_trancl)
  apply(fastsimp intro: rtrancl_trans)
  done

lemma in_trancl_into_r1: "(x,y) \<in> R\<^sup>+ \<Longrightarrow> \<exists> z. (x,z) \<in> R"
  by(drule DomainI, simp add: Domain_iff)

lemma (in derivation) derivOrd_irr:
  "(x, x) \<notin> derivOrd"
sorry
(*
unfolding derivOrd_def
proof(induct rule: derivs_induct)
  case init thus ?case by simp
next
  case (hash tr D m) 
  then interpret this_deriv: derivation P tr D by unfold_locales
  from hash show ?case 
    apply(clarsimp)
    apply(drule irr_insert_tranclD)
    apply(auto dest!: in_trancl_into_r1 this_deriv.Msg1_imp_Msg2 
                simp: knows_iff)
    done
next
  case (tuple tr D mx my) 
  then interpret this_deriv: derivation P tr D by unfold_locales
  from tuple show ?case 
    apply(clarsimp)
    apply(drule irr_insert_tranclD)
    apply(simp_all)
    apply(fastsimp dest!: in_trancl_into_r1 this_deriv.Msg1_imp_Msg2 
                simp: knows_iff)
    apply(clarsimp)
    apply(drule irr_insert_tranclD)
    apply(simp_all)
    apply(fastsimp dest!: in_trancl_into_r1 this_deriv.Msg1_imp_Msg2 
                simp: knows_iff)
    done
next
  case (encr tr D m k) 
  then interpret this_deriv: derivation P tr D by unfold_locales
  from encr show ?case 
    apply(clarsimp)
    apply(drule irr_insert_tranclD)
    apply(simp_all)
    apply(fastsimp dest!: in_trancl_into_r1 this_deriv.Msg1_imp_Msg2 
                simp: knows_iff)
    apply(clarsimp)
    apply(drule irr_insert_tranclD)
    apply(simp_all)
    apply(fastsimp dest!: in_trancl_into_r1 this_deriv.Msg1_imp_Msg2 
                simp: knows_iff)
    done
next
  case (proto tr s D inp s' out) thus ?case 
    apply(clarsimp)
    apply(case_tac inp)
    apply(simp)
    apply(case_tac out)
    apply(simp) 
    (* proceed by arguing about the individual inserts and that
       none is introducing a cycle.
    *)
    sorry
next
  case decr thus ?case sorry
qed
*)

lemma (in derivation) derivOrd_trans:
  "\<lbrakk> (x,y) \<in> derivOrd; (y,z) \<in> derivOrd \<rbrakk> \<Longrightarrow> (x,z) \<in> derivOrd"
  unfolding derivOrd_def by (auto intro!: trancl_trans)

lemma (in derivation) derivOrd_asymD:
  "(x,y) \<in> derivOrd \<Longrightarrow> (y,x) \<notin> derivOrd"
  by(auto dest: derivOrd_trans simp: derivOrd_irr)

lemma finite_pairParts [intro!]:
  "finite (pairParts m)"
  by (induct m) auto

(* MISSING in Isabelle library *)  
lemma Option_finite_set [iff]:
  "finite (Option.set x)"
  by (cases x) (auto)

lemma (in derivation) finite_D:
  "finite D"
proof -
  { fix A B assume "finite A" hence "finite (A - B)" by auto }
  note finite_setminus = this
  show ?thesis
    apply(induct rule: derivs_induct)
    apply(auto intro!: finite_setminus finite_cartesian_product finite_imageI)
    done
qed

lemma (in derivation) derivOrd_finite:
  "finite derivOrd"
proof -
  have "{i. Suc i < length tr} \<subseteq> {i. i < length tr}" by clarsimp
  hence "finite {i. Suc i < length tr}"
    by (auto dest!: finite_subset intro!: finite_Collect_less_nat)
  thus ?thesis using finite_D unfolding derivOrd_def
    by (auto simp: finite_trancl)
qed

lemma (in derivation) derivOrd_trancl [simp]:
  "derivOrd\<^sup>+ = derivOrd"
  unfolding derivOrd_def by auto

lemma (in derivation) derivOrd_wf: "wf derivOrd"
  by (auto intro!: finite_acyclic_wf derivOrd_finite acyclicI
             simp: derivOrd_irr)


section{* Relating the two models *}


lemma dy_conv_derivs:
  "{ (tr, M)       | tr M M'. M \<subseteq> M' \<and> (tr, M) \<in> dy P     } = 
   { (tr, knows D) | tr D.             (tr, D) \<in> derivs P }"
  oops

(* MOVE *)
lemma acyclic_empty [iff]: "acyclic {}"
  by (simp add: acyclic_def)

lemma knows_empty [iff]: "knows {} = {}"
  by (auto simp: knows_def)

(*
lemma in_derivsE [elim!]:
  "\<lbrakk> (tr, D) \<in> derivs P;
     \<And> M D'. \<lbrakk> (tr, D') \<in> derivs P;  
                D = D' - (Msg ` M) \<times> UNIV - UNIV \<times> (Msg ` M); 
                sound (tr, D)
              \<rbrakk> \<Longrightarrow> Q
   \<rbrakk> \<Longrightarrow> Q"
  by(auto simp: derivs_def)

lemma knows_cases: "\<lbrakk> (tr, D) \<in> derivs P; m \<in> knows D \<rbrakk> \<Longrightarrow> R"
  apply(clarsimp)
  apply(drule derivs.cases)
  apply(simp_all)
  oops
*)

lemma knows_times: 
  "N \<noteq> {} \<Longrightarrow> knows (N \<times> N') = {m. Msg m \<in> N'}"
  by (auto simp: knows_iff)

lemma (in derivation) infer_derivable:
  assumes m: "m \<in> infer M"
  and     M: "M \<subseteq> knows D"
  shows "\<exists>D'. (tr, D \<union> D') \<in> derivs P \<and> m \<in> knows (D \<union> D') \<and> 
              (\<forall> x \<in> M. x \<notin> knows D')"
  (is "\<exists>D'. ?extension D D' m")
using m M derivable
proof(induct arbitrary: D rule: infer.induct)
  case (Inj m D)
  hence "?extension D {} m" by auto
  thus ?case by fast
next
  case (Fst x y D) then
  obtain D' where ext: "?extension D D' \<lbrace>x, y\<rbrace>" by fastsimp
  then interpret ext_deriv: derivation P tr "D \<union> D'"
    by unfold_locales auto
  from ext have "?extension D D' x"
    by (fastsimp simp del: knows_Un
                    intro: ext_deriv.knows_pairParts_closed)
  thus ?case by fast
next
  case (Snd x y D) then
  obtain D' where ext: "?extension D D' \<lbrace>x, y\<rbrace>" by fastsimp
  then interpret ext_deriv: derivation P tr "D \<union> D'"
    by unfold_locales auto
  from ext have "?extension D D' y"
    by (fastsimp simp del: knows_Un
                    intro: ext_deriv.knows_pairParts_closed)
  thus ?case by fast
next
  case (Hash m D) then
  obtain D' where ext: "?extension D D' m" by fastsimp
  then interpret ext_state: derivation P tr "D \<union> D'"
    by unfold_locales auto
  show ?case
  proof(cases "Hash m \<in> knows (D \<union> D')")
    case True thus ?thesis using ext by auto
  next
    case False
    hence "(tr, D \<union> (D' \<union> Msg ` pairParts m \<times> {Msg (Hash m)})) \<in> derivs P"
      using ext
      by(fastsimp dest: derivs.hash simp: Un_ac)
    thus ?thesis using ext and `M \<subseteq> knows D` and False
      apply -
      apply(rule exI, rule conjI, assumption)
      apply(fastsimp simp: knows_iff)
      done
  qed
next
  case (Tup x y D)
  then obtain D' where ext1: "?extension D D' x" by fastsimp
  hence "\<exists> D''. ?extension (D \<union> D') D'' y" using Tup
    apply -
    apply(rule Tup)
    apply(auto)
    done
  then obtain D'' where ext2: "?extension D (D' \<union> D'') y" 
    using ext1 by (auto simp: Un_assoc)
  then interpret ext_deriv: derivation P tr "D \<union> D' \<union> D''"
    by unfold_locales (auto simp: Un_assoc)
  show ?case
  proof(cases "Tup x y \<in> knows (D \<union> D' \<union> D'')")
    case True thus ?thesis using ext2 by auto
  next
    case False thm derivs.tuple
    hence "(tr, D \<union> (Msg ` (pairParts x \<union> pairParts y) \<times> {Msg \<lbrace>x, y\<rbrace>} 
                     \<union> D' \<union> D'')) 
           \<in> derivs P"
      using ext1 and ext2
      apply clarsimp
      apply(drule_tac x=x and y=y in derivs.tuple) back
      apply(auto simp: Un_ac)
      done
    thus ?thesis using ext1 ext2 `M \<subseteq> knows D` and False
      apply -
      apply(rule exI, rule conjI, assumption)
      by (fastsimp simp: knows_iff Un_ac)
  qed
next
  case (Enc m k D)
  then obtain D' where ext1: "?extension D D' m" by fastsimp
  hence "\<exists> D''. ?extension (D \<union> D') D'' k" using Enc
    apply -
    apply(rule Enc)
    apply(auto)
    done
  then obtain D'' where ext2: "?extension D (D' \<union> D'') k" 
    using ext1 by (auto simp: Un_assoc)
  then interpret ext_deriv: derivation P tr "D \<union> D' \<union> D''"
    by unfold_locales (auto simp: Un_assoc)
  show ?case
  proof(cases "Enc m k \<in> knows (D \<union> D' \<union> D'')")
    case True thus ?thesis using ext2 by auto
  next
    case False
    hence "(tr, D \<union> ((Msg ` (pairParts m \<union> pairParts k)) \<times> {Msg (Enc m k)} \<union> D' \<union> D'')) 
           \<in> derivs P"
      using ext1 and ext2
      apply clarsimp
      apply(drule_tac m=m and k=k in derivs.encr) back
      apply(auto simp: Un_ac)
      done
    thus ?thesis using ext1 ext2 `M \<subseteq> knows D` and False
      apply -
      apply(rule exI, rule conjI, assumption)
      by (fastsimp simp: knows_iff Un_ac)
  qed
next

(* stopped here, as a simpler solution is possible *)

  case (Dec m k D)
  then obtain D' where ext1: "?extension D D' (Enc m k)" by fastsimp
  hence "\<exists> D''. ?extension (D \<union> D') D'' (inv k)" using Dec
    apply -
    apply(rule Dec)
    apply(auto)
    done
  then obtain D'' where ext2: "?extension D (D' \<union> D'') (inv k)" 
    using ext1 by (auto simp: Un_assoc)
  then interpret ext_deriv: derivation P tr "D \<union> D' \<union> D''"
    by unfold_locales (auto simp: Un_assoc)
  show ?case
  proof(cases "m \<in> knows (D \<union> D' \<union> D'')")
    case True thus ?thesis using ext2 by auto
  next
    case False thm decr
    hence "(tr, D \<union> (({Msg (Enc m k), Msg (inv k)} \<times>
                     Msg ` (pairParts m - knows (D \<union> D' \<union> D''))) \<union> D' \<union> D''))
           \<in> derivs P"
      using ext1 and ext2
      apply clarsimp
      apply(drule derivs.decr) back
      apply(auto simp: Un_ac)
      done
    thus ?thesis using ext1 ext2 `M \<subseteq> knows D` and False
      apply -
      apply(rule exI, rule conjI, assumption)
      apply(rule conjI)
      apply(fastsimp simp: knows_iff)
      apply(clarsimp simp: knows_iff)
      apply(drule subsetD)
      apply(assumption)
      apply(simp add: knows_iff)
      done
  qed
qed

lemma dy_imp_derivs:
  "(tr, M) \<in> dy P \<Longrightarrow>
   \<exists> D. (tr, D) \<in> derivs P \<and> M \<subseteq> knows D
  "
proof(induct rule: dy.induct)
  case init thus ?case by(auto intro!: derivs.init)
next
  case (proto tr s M inp s' out) thus ?case
    apply(clarsimp)
    apply(rule exI, rule conjI)
    apply(rule_tac inp=inp in derivs.proto)
    apply(auto simp: knows_iff)
    done
next
  case (infer tr M m)
  then obtain D where the_deriv: "(tr, D) \<in> derivs P" "M \<subseteq> knows D"
    by auto
  then interpret the_deriv: derivation P tr D
    by unfold_locales
  show ?case using `m \<in> infer M` `M  \<subseteq> knows D`
    by (fastsimp dest!: the_deriv.infer_derivable)
qed

lemma pairParts_in_dy:
  "\<lbrakk> (tr, M) \<in> dy P; m \<in> M \<rbrakk> \<Longrightarrow> (tr, M \<union> pairParts m) \<in> dy P"
proof(induct m arbitrary: M)
  case (Tup m1 m2) 
  hence "(tr, insert m1 M) \<in> dy P"
    by (best dest: dy.infer intro: infer.intros)
  hence "(tr, insert m1 (insert m2 M)) \<in> dy P"
    using Tup by (best dest: dy.infer intro: infer.intros)
  hence "(tr, M \<union> pairParts m1 \<union> pairParts m2) \<in> dy P"
    by(bestsimp dest: Tup(1-2) simp: insert_absorb)
  thus ?case
    using Tup by (simp add: insert_absorb Un_ac)
qed (auto simp: insert_absorb)

lemma insert_pairParts_in_dy:
  "(tr, insert m M) \<in> dy P \<Longrightarrow> (tr, M \<union> pairParts m) \<in> dy P"
  by (fastsimp dest: pairParts_in_dy simp: insert_absorb) 


lemma derivs_imp_dy:
  "(tr, D) \<in> derivs P \<Longrightarrow> (tr, knows D) \<in> dy P"
proof(induct rule: derivs.induct)
  case init thus ?case by (auto intro!: dy.init)
next
  case (proto tr s D inp s' out)
  moreover
  have "knows (Msg ` Option.set inp \<times>
               {State (Suc (length tr), s')}) = {}"
    by (auto intro!: set_ext simp: knows_iff)
  moreover
  have "knows (\<Union>m\<in>Option.set out.
                 {State (Suc (length tr), s')} \<times>
                 Msg ` (pairParts m - knows D))
        = (\<Union>m\<in>Option.set out. pairParts m) - knows D"
    by (cases out, simp) (auto intro!: set_ext simp: knows_iff)
  ultimately 
  show ?case
    apply -
    apply(drule dy.proto, assumption+)
    apply(simp)
    apply(cases out, simp)
    apply(force dest: pairParts_in_dy simp: insert_absorb)
    done
next
  case (decr tr D m k)
  hence "(tr, knows D \<union> pairParts m) \<in> dy P"
    by(blast intro!: insert_pairParts_in_dy
              intro: infer.intros dy.infer)
  moreover
  have "knows ({Msg (Enc m k), Msg (inv k)} \<times>
               Msg ` (pairParts m - knows D))
        = (pairParts m - knows D)"
    by (auto intro!: set_ext simp: knows_iff)
  ultimately
  show ?case
    by (fastsimp elim: ssubst)
qed (simp add: knows_times, 
     blast intro: infer.intros dy.infer)+
  

section{* Deriving the Chain Rule *}

abbreviation (in derivation) 
  derivOrd' (infixl "\<prec>" 50) where "derivOrd' x y \<equiv> (x,y) \<in> derivOrd"

definition (in derivation) derivOrdEq
where "derivOrdEq \<equiv> derivOrd \<union> Id"

abbreviation (in derivation) 
  derivOrdEq' (infixl "\<preceq>" 50) where "derivOrdEq' x y \<equiv> (x,y) \<in> derivOrdEq"


sublocale derivation \<subseteq> order "derivOrdEq'" "derivOrd'"
  apply(unfold_locales)
  apply(auto simp: derivOrdEq_def derivOrd_irr
            intro: derivOrd_trans
             dest: derivOrd_asymD)
  done

fun chain :: "'s dependencies \<Rightarrow> 's node set \<Rightarrow> execmsg \<Rightarrow> execmsg \<Rightarrow> bool"
where
  "chain D from (Enc msg key) m = 
   ( ( m = Enc msg key \<and> from \<times> {Msg m} \<subseteq> D)
     \<or>
     ( from \<times> {Msg (Enc msg key)} \<subseteq> D \<and> 
       chain D {Msg (Enc msg key), Msg (inv key)} msg m  )
   )"
| "chain D from (Tup x y) m = 
   ( ( m = Tup x y \<and> from \<times> {Msg m} \<subseteq> D) \<or>
     chain D from x m \<or>
     chain D from y m
   )"
| "chain D from msg m =
   ( m = msg \<and> from \<times> {Msg m} \<subseteq> D)
  "

lemma chain_mono: 
  "\<lbrakk> chain D from m' m; D \<subseteq> D' \<rbrakk> \<Longrightarrow> chain D' from m' m"
  by (induct m' arbitrary: "from") auto

lemma chain_pairParts:
  "\<lbrakk> m' \<in> pairParts m; m' \<in> knows D;
     from \<times> {Msg m'} \<subseteq> D
   \<rbrakk> \<Longrightarrow> chain D from m m'"
  by (induct m) auto

lemma chain_eq:
  "from \<times> {Msg m}  \<subseteq> D \<Longrightarrow> chain D from m m"
  by (induct m) auto

lemma chain_decrypt:
  "\<lbrakk> chain D from msg (Enc m k);
     m' \<in> pairParts m;
     (Msg (Enc m k), Msg m') \<in> D; 
     (Msg (inv k)  , Msg m') \<in> D
   \<rbrakk> \<Longrightarrow> chain D from msg m'"
apply(induct msg arbitrary: "from") 
apply(auto)
apply(fastsimp intro!: chain_pairParts simp: knows_iff)+
done


lemma (in derivation) knows_cases:
  assumes knows: "m' \<in> knows D"
  shows 
   "(\<exists> m.   m' = Hash m   \<and> (Msg m, Msg (Hash m)) \<in> D    ) \<or>
    (\<exists> m k. m' = Enc  m k \<and> (Msg m, Msg (Enc m k)) \<in> D \<and> 
                            (Msg k, Msg (Enc m k)) \<in> D   ) \<or>
    (\<exists> x y. m' = Tup  x y \<and> (Msg x, Msg (Tup x y)) \<in> D \<and> 
                            (Msg y, Msg (Tup x y)) \<in> D   ) \<or>
    (\<exists> s inp s' m i. 
       (s, inp, s', Some m) \<in> snd P \<and> chain D {State (i, s')} m m'
    )"
  (is "?cases m' D")
proof -
  --{* Prove case monotonicity *}
  { fix m' D D'
    let ?thesis = "?cases m' D'"
    assume "?cases m' D" (is "?hash \<or> ?enc \<or> ?tup \<or> ?chain D")
      and  "D \<subseteq> D'"
    moreover
    { assume "?hash" hence "?thesis" using `D \<subseteq> D'` by blast} moreover
    { assume "?enc"  hence "?thesis" using `D \<subseteq> D'` by blast} moreover
    { assume "?tup"  hence "?thesis" using `D \<subseteq> D'` by blast} moreover
    { assume "?chain D"
      hence "?chain D'" using `D \<subseteq> D'`
	by (fastsimp intro: chain_mono)
      hence "?thesis" by blast
    }
    ultimately have ?thesis by fast
  }
  note cases_mono = this

  --{* Prove actual thesis *}
  from knows show ?thesis
  proof (induct arbitrary: m' rule: derivs_induct)
    case init thus ?case by simp
  next
    case (hash tr D m m')
    note IH = hash(2)
    have "m' \<in> knows D \<or> m' = Hash m" (is "?old \<or> ?new")
      using hash by fastsimp
    moreover
    { assume "?new" hence ?case by fastsimp }
    moreover
    { assume "?old" hence ?case by (fast elim!: cases_mono[OF IH]) }
    ultimately show ?case by fast
  next
    case (encr tr D m k m')
    note IH = encr(2)
    have "m' \<in> knows D \<or> m' = Enc m k" (is "?old \<or> ?new")
      using encr by fastsimp
    moreover
    { assume "?new" hence ?case by fastsimp }
    moreover
    { assume "?old" hence ?case by (fast elim!: cases_mono[OF IH]) }
    ultimately show ?case by fast
  next
    case (tuple tr D x y m')
    note IH = tuple(2)
    have "m' \<in> knows D \<or> m' = Tup x y" (is "?old \<or> ?new")
      using tuple by fastsimp
    moreover
    { assume "?new" hence ?case by fastsimp }
    moreover
    { assume "?old" hence ?case by (fast elim!: cases_mono[OF IH]) }
    ultimately show ?case by fast
  next
    case (proto tr s D inp s' out m')
    note IH = proto(2)
    let ?ns' = "State (Suc (length tr), s')"
    let ?D' = "D \<union> Msg ` Option.set inp \<times> {?ns'}
                \<union> (\<Union> m\<in>Option.set out. 
                      {?ns'} \<times> Msg ` (pairParts m - knows D))"
    have "m' \<in> knows D \<or> 
          (\<exists> m. out = Some m \<and> m' \<in> pairParts m \<and> m' \<notin> knows D)" 
      (is "?old \<or> ?new")
      using proto(5) by (auto simp: knows_iff)
    moreover
    { assume "?old" hence ?case by (fast elim!: cases_mono[OF IH]) }
    moreover
    { assume "?new"
      then obtain m where 
        "out = Some m"
        "m' \<in> pairParts m"
        "m' \<notin> knows D"
        by auto
      hence "chain ?D' {?ns'} m m'"
	by (fastsimp intro!: chain_pairParts simp: knows_iff)
      hence ?case 
        using `out = Some m`   `(s, inp, s', out) \<in> snd P`
        by force
    }
    ultimately show ?case by fast
  next
    case (decr tr D m k m')
    then interpret this_deriv: derivation P tr D
      by unfold_locales
    note IH = decr(2)
    have "m' \<in> knows D \<or> m' \<in> pairParts m \<and> m' \<notin> knows D" 
      (is "?old \<or> ?new")
      using decr by (auto simp: knows_iff)
    moreover
    { assume "?old" hence ?case by (fast elim!: cases_mono[OF IH]) }
    moreover
    { assume "?new"
      have 
        "((Msg m, Msg (Enc m k)) \<in> D \<and> (Msg k, Msg (Enc m k)) \<in> D) \<or>
         (\<exists>s inp s' mo i.  (s, inp, s', Some mo) \<in> snd P \<and>
                           chain D {State (i, s')} mo (Enc m k))"
	(is "?fake_enc \<or> ?chain D (Enc m k)")
	using IH[OF `Enc m k \<in> knows D`] by auto
      moreover
      { assume "?fake_enc"
        hence "m \<in> knows D"
          by (auto dest!: this_deriv.Msg1_imp_Msg2 simp: knows_iff)
	hence "False" using `?new`
          by (auto dest: this_deriv.knows_pairParts_closed)
        hence "?case" by simp
      }
      moreover
      { let ?D' = "(D \<union> {Msg (Enc m k), Msg (Message.inv k)} \<times>
                         Msg ` (pairParts m - knows D))"
        assume "?chain D (Enc m k)" then
	obtain s inp s' mo i where 
          "(s, inp, s', Some mo) \<in> snd P"
          "chain D {State (i, s')} mo (Enc m k)"
	  by auto
	moreover
	hence "chain ?D' {State (i, s')} mo m'"
	  using `?new`
          apply -
          apply(rule chain_decrypt)
          apply(erule chain_mono)
          by auto
	ultimately
	have "?chain ?D' m'" by fastsimp
	hence "?case" by blast
      }
      ultimately have ?case by fast
    }
    ultimately show ?case by fast
  qed
qed



lemma

(* OOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOLD *)


where
  "add_index i []     = []"
| "add_index i (x#xs) = (i,x) # add_index (Suc i) xs"

definition deps :: "'s derivation \<Rightarrow> 's dependencies"
where "deps dr \<equiv> case dr of (tr, D) \<Rightarrow> 
         D \<union> { (x,y) | x y. listOrd (add_index 0 tr) (State x) (State y)}"
         
    
section{* Executing Protocol Scripts *}

types threadpool = "tid \<rightharpoonup> (rolestep list \<times> rolestep list)"

types state = "threadpool \<times> store"


definition proto2nts :: "proto \<Rightarrow> state option nts"
where "proto2nts P =
  ( None 
  , ({ ( None, None, Some (th, st), None)
     | th st.
       (\<forall> i done todo. th i = Some (done,todo) \<longrightarrow> 
                                done = [] \<and> todo \<in> P) \<and>
       (\<forall> a i. st (AVar a, i) \<in> Compromised \<union> Uncompromised)
     } 
     \<union>
     { (s, None, s, Some m) 
     | s m. 
       m \<in> IK0
     }
     \<union>
     (\<Union> R \<in> P.
       { ( Some (th, st)                          
         , Some (inst st i pt)
         , Some (th(i\<mapsto> (done @ [Recv l pt], todo)), st)
         , None 
         )
       | th st i l pt done todo.
         th i = Some (done, Recv l pt # todo)
       }
     )
     \<union>
     (\<Union> R \<in> P.
       { ( Some (th, st)                          
         , None
         , Some (th(i\<mapsto> (done @ [Send l pt], todo)), st)
         , Some (inst st i pt) 
         )
       | th st i l pt done todo.
         th i = Some (done, Send l pt # todo)
       }
     )
    )
  )
"



(* OOOOOOOOOOOOOOOOOOOOLDDDDDDDDDDDDDDDDDDDDDDDD *)

term "undefined"
thm the_def
thm 
thm undefined_def

types explicit_trace = "rawevent list"
types execstep = "tid \<times> rolestep"


fun knows :: "explicit_trace \<Rightarrow> execmsg set"
where
  "knows [] = {}"
| "knows (Learns M # t) = M \<union> knows t"
| "knows (Step estep # t) = knows t"

fun steps :: "explicit_trace \<Rightarrow> execstep set"
where
  "steps [] = {}"
| "steps (Learns M # t) = steps t"
| "steps (Step estep # t) = insert estep (steps t)"

types state = "explicit_trace \<times> threadpool \<times> store"

inductive_set 
  reachable :: "proto \<Rightarrow> state set" 
  for P     :: "proto"
where
  init:  "\<lbrakk> \<forall> i done todo. r i = Some (done,todo) \<longrightarrow> 
                             done = [] \<and> todo \<in> P;
            \<forall> a i. s (AVar a, i) \<in> Compromised \<union> Uncompromised
          \<rbrakk>
          \<Longrightarrow> ([Learns IK0], r, s) \<in> reachable P"

| send:  "\<lbrakk> (t, r, s) \<in> reachable P;
            r i = Some (done, Send l pt # todo);
            m = inst s i pt
          \<rbrakk>
          \<Longrightarrow> (t @ [Step (i, Send l pt), 
                    Learns (pairParts m - knows t)]
              , r(i \<mapsto> (done @ [Send l pt], todo))
              , s) \<in> reachable P"
            
| recv:  "\<lbrakk> (t, r, s) \<in> reachable P;
            r i = Some (done, Recv l pt # todo);
            inst s i pt \<in> knows t
          \<rbrakk>
          \<Longrightarrow> (t @ [Step (i, Recv l pt)]
              , r(i \<mapsto> (done @ [Recv l pt], todo))
              , s) \<in> reachable P"

| hash:  "\<lbrakk> (t, r, s) \<in> reachable P;
            m \<in> knows t;
            Hash m \<notin> knows t
          \<rbrakk>
          \<Longrightarrow> (t @ [Learns {Hash m}], r, s) \<in> reachable P"

| tuple: "\<lbrakk> (t, r, s) \<in> reachable P;
            x \<in> knows t;
            y \<in> knows t;
            Tup x y \<notin> knows t
          \<rbrakk>
          \<Longrightarrow> (t @ [Learns {Tup x y}], r, s) \<in> reachable P"

| encr:  "\<lbrakk> (t, r, s) \<in> reachable P;
            m \<in> knows t;
            k \<in> knows t;
            Enc m k \<notin> knows t
          \<rbrakk>
          \<Longrightarrow> (t @ [Learns {Enc m k}], r, s) \<in> reachable P"


| decr:  "\<lbrakk> (t, r, s) \<in> reachable P;
            Enc m k \<in> knows t;
            inv k \<in> knows t
          \<rbrakk>
          \<Longrightarrow> (t @ [Learns (pairParts m - knows t)], r, s) \<in> reachable P"

locale reachable_state =  wf_proto +
  fixes t :: explicit_trace
  and   r :: threadpool
  and   s :: store
  assumes reachable [simp,intro!]: "(t,r,s) \<in> reachable P"
begin
  text{* A local variant of the induction rule of @{term "reachable"}. *}
  lemmas reachable_induct = reachable.induct
    [ OF reachable
    , rule_format
    , consumes 0
    , case_names init send recv hash tuple encr decr
    ]
end

text{* An extension of the reachable state locale denoting
       an individual thread and its state. *}

locale reachable_thread = reachable_state +
  fixes i      :: "tid"
    and "done" :: "rolestep list"
    and todo   :: "rolestep list"
  assumes thread_exists: "r i = Some (done, todo)"
begin

  text{* The thread state is built such that @{term "done @ todo"} is
         always a role of @{term P}. *}

  lemma role_in_P:
    "done @ todo \<in> P"
  using thread_exists
  proof (induct arbitrary: i "done" todo rule: reachable_induct)
  qed (fastsimp split: if_splits)+

end

text{* Importing all lemmas of the wellformed role locale for
the term @{term "done @ todo"}. *}
sublocale reachable_thread \<subseteq> wf_role "done @ todo"
  by (rule wf_roles[OF role_in_P])



subsection{* Basic Properties *}

lemma knowsI: "\<lbrakk> Learns M \<in> set t; m \<in> M \<rbrakk> \<Longrightarrow> m \<in> knows t"
  by(induct t rule: knows.induct, auto)

lemma knowsD: "m \<in> knows t \<Longrightarrow> \<exists> M. Learns M \<in> set t \<and> m \<in> M"
  by(induct t rule: steps.induct, auto)

lemma knows_append [simp]: 
  "knows (xs@ys) = knows xs \<union> knows ys"
  by(induct xs rule: knows.induct, auto)

lemma stepsI: "Step estep \<in> set t \<Longrightarrow> estep \<in> steps t"
  by(induct t rule: steps.induct, auto)

lemma stepsD: "estep \<in> steps t \<Longrightarrow> Step estep \<in> set t"
  by(induct t rule: steps.induct, auto)

lemma Step_in_set_conv [simp]: 
  "(Step estep \<in> set t) = (estep \<in> steps t)"
  by(auto intro!: stepsI stepsD)

lemma steps_append [simp]: 
  "steps (t@t') = steps t \<union> steps t'"
  by(induct t rule: steps.induct, auto)



subsection{* Thread Execution *}

lemma (in reachable_state) step_in_dom: 
  "(i, step) \<in> steps t \<Longrightarrow> i \<in> dom r"
proof (induct rule: reachable_induct) qed auto

context reachable_thread
begin

lemma in_dom_r [iff]: "i \<in> dom r" 
  by (auto intro!: thread_exists)

lemma distinct_done [iff]: "distinct done"
using distinct by auto

lemma distinct_todo [iff]: "distinct todo"
using distinct by auto

lemma in_steps_eq_in_done:
  "((i, step) \<in> steps t) = (step \<in> set done)"
proof -
  have   
    "((i, step) \<in> steps t) = 
    (\<exists> done todo. r i = Some (done, todo) \<and> step \<in> set done)"
  proof(induct arbitrary: i "done" todo rule: reachable_induct)
    case (init r s i) thus ?case by fastsimp
  qed auto
  thus ?thesis using thread_exists by auto
qed

lemmas steps_in_done [elim!] = iffD1[OF in_steps_eq_in_done, rule_format]
lemmas done_in_steps [elim!] = iffD2[OF in_steps_eq_in_done, rule_format]

lemma todo_notin_stepsD:
  "step \<in> set todo \<Longrightarrow> (i, step) \<notin> steps t"
using distinct by(auto dest!: steps_in_done)

lemmas todo_notin_stepsE = notE[OF todo_notin_stepsD, rule_format]

lemma listOrd_done_imp_listOrd_trace: 
  "listOrd done prev step \<Longrightarrow> 
   listOrd t (Step (i, prev)) (Step (i, step))"
using thread_exists
proof(induct arbitrary: i "done" todo rule: reachable_induct)
  case (init r s i "done" todo) thus ?case
    by fastsimp
next
  case (send t r s i "done" l msg todo m i' done' todo')
  then interpret this_thread: 
    reachable_thread P t r s i "done" "Send l msg # todo"
    by unfold_locales auto
  from send show ?case
    by(auto split: if_splits)
next
  case (recv t r s i "done" l msg todo i' done' todo')
  then interpret this_thread: 
    reachable_thread P t r s i "done" "Recv l msg # todo"
    by unfold_locales auto
  from recv show ?case
    by(auto split: if_splits)
qed auto

lemma listOrd_role_imp_listOrd_trace:
  "\<lbrakk> (i, step) \<in> steps t; listOrd (done @ todo) prev step \<rbrakk>
  \<Longrightarrow> listOrd t (Step (i, prev)) (Step (i, step))"
using distinct
by (fastsimp dest: in_set_listOrd2 listOrd_done_imp_listOrd_trace)

end


subsection{* Variable Substitutions *}

context reachable_state
begin

lemma inst_AVar_cases: 
  "s (AVar v, i) \<in> Uncompromised \<or> s (AVar v, i) \<in> Compromised"
  by (induct rule: reachable_induct) (fastsimp+)

lemma inst_AVar_in_IK0: 
 "s (AVar v, i) \<in> IK0"
using inst_AVar_cases[of v i] 
by (auto simp: IK0_def Uncompromised_def Compromised_def)

lemma knows_IK0: "m \<in> IK0 \<Longrightarrow> m \<in> knows t"
  by(induct rule: reachable_induct, auto)

lemma inst_AVar_in_knows [iff]:
  "s (AVar a, i) \<in> knows t"
  by (rule knows_IK0[OF inst_AVar_in_IK0])

end (* reachable_state *)

(* TODO: Move *)
lemma MVar_in_FV_conv_FMV [iff]:
  "(MVar v \<in> FV pt) = (v \<in> FMV pt)"
  by(induct pt, auto, case_tac varid, auto)


context reachable_state
begin

lemma send_step_FV:
  assumes thread_exists: "r i = Some (done, Send l msg # todo)"
  and FV: "MVar n \<in> FV msg"
  shows "\<exists> l' msg'. (i, Recv l' msg') \<in> steps t \<and>  MVar n \<in> FV msg'"
proof -
  interpret this_thread: reachable_thread P t r s i "done" "Send l msg # todo"
    using thread_exists by unfold_locales auto
  let ?role = "done @ Send l msg # todo"
  have "Send l msg \<in> set ?role" by simp
  then obtain l' msg' 
    where "listOrd ?role (Recv l' msg') (Send l msg)"
    and "MVar n \<in> FV msg'"
    using FV by(fast dest!: this_thread.Send_FV)
  thus ?thesis using this_thread.distinct
    by(auto dest: in_set_listOrd1 in_set_listOrd2)
qed

end


subsubsection{* The Effect of a Step on the Intruder Knowledge *}


context reachable_state
begin

lemma SendD: 
  "(i, Send lbl pt) \<in> steps t \<Longrightarrow> 
   inst s i pt \<in> knows t"
proof(induct rule: reachable_induct)
qed auto

end


subsection{* Almost Distinct Traces *}

fun distinct' :: "explicit_trace \<Rightarrow> bool"
where
  "distinct' [] = True"
| "distinct' (Learns M # t) =
     ((\<forall> m \<in> M. m \<notin> knows t) \<and> distinct' t)"
| "distinct' (Step estep # t) =
     ((estep \<notin> steps t) \<and> distinct' t)"


lemma distinct'_append [simp]:
  "distinct' (t@t') = 
   (distinct' t \<and> distinct' t' \<and> 
    (knows t \<inter> knows t' = {}) \<and> (steps t \<inter> steps t' = {}))"
proof (induct t rule: distinct'.induct)
qed (auto intro!: knowsI)

lemma distinct'_singleton [iff]: "distinct' [x]"
by (cases x) auto

lemma (in reachable_state) distinct'_trace [iff]:
  "distinct' t"
proof(induct rule: reachable_induct)
  case (recv t r s i "done" l msg todo)
  then interpret this_thread: 
    reachable_thread P t r s i "done" "Recv l msg # todo"
    by unfold_locales auto
  show ?case using `distinct' t` and this_thread.distinct
    by(auto dest!: this_thread.steps_in_done)
next
  case (send t r s i "done" l msg todo m)
  then interpret this_thread: 
    reachable_thread P t r s i "done" "Send l msg # todo"
    by unfold_locales auto
  show ?case using `distinct' t` and this_thread.distinct
    by(auto dest!: this_thread.steps_in_done)
qed auto


subsection{* Happens-Before Order *}

datatype event = St "tid \<times> rolestep" | Ln execmsg

fun predOrd :: "explicit_trace \<Rightarrow> event \<Rightarrow> event \<Rightarrow> bool"
where
  "predOrd []             x y = False"
| "predOrd (Learns M # xs) x y =
     ((x \<in> Ln ` M \<and> (y \<in> Ln ` knows xs \<or> y \<in> St ` steps xs)) \<or>
      predOrd xs x y)"
| "predOrd (Step estep # xs) x y =
     ((x = St estep \<and> (y \<in> Ln ` knows xs \<or> y \<in> St ` steps xs)) \<or>
      predOrd xs x y)"


definition predEqOrd :: "explicit_trace \<Rightarrow> event \<Rightarrow> event \<Rightarrow> bool"
where "predEqOrd t x y = ((x = y) \<or> predOrd t x y)"


lemma predOrd_singleton [simp]: "\<not> predOrd [a] x y"
by (cases a) auto

lemma in_knows_predOrd1: "predOrd t (Ln x) y \<Longrightarrow> x \<in> knows t"
proof (induct t)
  case (Cons e t) thus ?case by (cases e) auto
qed auto


lemma in_knows_predOrd2: "predOrd t x (Ln y) \<Longrightarrow> y \<in> knows t"
proof (induct t)
  case (Cons e t) thus ?case by (cases e) auto
qed auto

lemma in_steps_predOrd1: "predOrd t (St x) y \<Longrightarrow> x \<in> steps t"
proof (induct t)
  case (Cons e t) thus ?case by (cases e) auto
qed auto

lemma in_steps_predOrd2: "predOrd t x (St y) \<Longrightarrow> y \<in> steps t"
proof (induct t)
  case (Cons e t) thus ?case by (cases e) auto
qed auto

lemmas event_predOrdI = 
  in_knows_predOrd1 in_knows_predOrd2 
  in_steps_predOrd1 in_steps_predOrd2

lemma in_set_predOrd1: 
  "predOrd t x y \<Longrightarrow> x \<in> Ln ` knows t \<or> x \<in> St ` steps t"
by (induct t x y rule: predOrd.induct) auto

lemma in_set_predOrd2: 
  "predOrd t x y \<Longrightarrow> y \<in> Ln ` knows t \<or> y \<in> St ` steps t"
by (induct t x y rule: predOrd.induct) auto

lemma listOrd_imp_predOrd:
  "listOrd t (Step e) (Step e') \<Longrightarrow> predOrd t (St e) (St e')"
by (induct t rule: steps.induct) (auto dest!: stepsI)

lemma predOrd_append [simp]:
  "predOrd (xs@ys) x y = 
   (predOrd xs x y \<or> predOrd ys x y \<or>
   ((x \<in> Ln ` knows xs \<or> x \<in> St ` steps xs) \<and> 
    (y \<in> Ln ` knows ys \<or> y \<in> St ` steps ys)))"
  apply(induct xs x y rule: predOrd.induct)
  apply(simp_all)
  apply(blast+)
  done

lemma predOrd_distinct'_irr [simp]: 
  "distinct' t \<Longrightarrow> \<not>predOrd t x x"
  apply(induct t, auto)
  apply(case_tac x, auto)
  apply(case_tac a, auto)
  apply(case_tac a, auto)
  done

lemma predOrd_distinct'_trans: 
  "\<lbrakk> predOrd t x y; predOrd t y z; distinct' t \<rbrakk> 
   \<Longrightarrow> predOrd t x z"
  apply(induct t x y rule: predOrd.induct)
  apply(auto dest: in_set_predOrd1 in_set_predOrd2)
  done

lemma predOrd_distinct'_asymD: 
  "\<lbrakk> predOrd t x y; distinct' t \<rbrakk> \<Longrightarrow> \<not> predOrd t y x"
  apply(induct t x y rule: predOrd.induct)
  apply(auto dest: in_set_predOrd1 in_set_predOrd2)
  done


sublocale reachable_state \<subseteq> beforeOrd: order "predEqOrd t" "predOrd t"
  apply(unfold_locales)
  apply(auto simp: predEqOrd_def
          dest: predOrd_distinct'_asymD 
         intro: predOrd_distinct'_trans)
  done

abbreviation (in reachable_state)
  "pred'"   (infixl "\<prec>" 50) where "pred' \<equiv> predOrd t"

abbreviation (in reachable_state) 
  "predEq'" (infixl "\<preceq>" 50) where "predEq' \<equiv>  predEqOrd t"

lemma predOrd_conv:
  "predOrd xs x y = 
  (\<exists> ys zs. xs = ys @ zs \<and> 
            (x \<in> Ln ` knows ys \<or> x \<in> St ` steps ys) \<and>
            (y \<in> Ln ` knows zs \<or> y \<in> St ` steps zs))"
  (is "?pred xs = (\<exists> ys zs. ?decomp xs ys zs)")
proof -
  { assume "?pred xs"
    hence "\<exists> ys zs. ?decomp xs ys zs"
    proof (induct xs)
      case Nil thus ?case by simp
    next
      case (Cons e xs) thus ?case
      proof(cases e)
	case (Step st) thus ?thesis
	proof(cases "x = St st")
	  case True hence "?decomp (e#xs) [e] xs" 
	    using Step Cons by auto
	  thus ?thesis by blast
	next
	  case False
	  hence "predOrd xs x y"
	    using Step Cons by auto
	  then obtain ys zs where "?decomp xs ys zs"
	    using Cons by auto
	  hence "?decomp (e#xs) (e#ys) zs"
	    using Step Cons by auto
	  thus ?thesis by blast
	qed
      next
	case (Learns M) thus ?thesis
	proof(cases "\<exists> m \<in> M. x = Ln m")
	  case True 
	  then obtain m where "m \<in> M" and "x = Ln m"
	    by auto
	  hence "?decomp (e#xs) [e] xs" 
	    using Learns Cons by auto
	  thus ?thesis by blast
	next
	  case False
	  hence "predOrd xs x y"
	    using Learns Cons by auto
	  then obtain ys zs where "?decomp xs ys zs"
	    using Cons by auto
	  hence "?decomp (e#xs) (e#ys) zs"
	    using Learns Cons by auto
	  thus ?thesis by blast
	qed
      qed
    qed
  }
  moreover
  { assume "\<exists> ys zs. ?decomp xs ys zs"
    hence "?pred xs"
    proof (induct xs)
      case Nil thus ?case by simp
    next
      case (Cons e xs)
      then obtain ys zs where decomp1: "?decomp (e#xs) ys zs"
	by blast
      hence "ys = [] \<and> e # xs = zs \<or> (\<exists>ys'. e # ys' = ys \<and> xs = ys' @ zs)"
	(is "?nil \<or> ?non_nil")
	by (simp add: Cons_eq_append_conv)
      moreover
      { assume ?nil hence ?case using decomp1 by auto }
      moreover
      { assume ?non_nil
	then obtain ys' where decomp2: "ys = e # ys'" and "xs = ys' @ zs"
	  by auto
	hence ?case
	proof(cases e)
	  case (Step st) thus ?thesis
	  proof(cases "x = St st")
	    case True thus ?thesis
	      using Step decomp1 decomp2 by auto
	  next
	    case False
	    hence "?decomp xs ys' zs"
	      using Step decomp1 decomp2 by auto
	    hence "predOrd xs x y"
	      using Cons by auto
	    thus ?thesis
	      using Step by auto
	  qed
	next
	  case (Learns M) thus ?thesis
	  proof(cases "\<exists> m \<in> M. x = Ln m")
	    case True thus ?thesis
	      using Learns decomp1 decomp2 by auto
	  next
	    case False
	    hence "?decomp xs ys' zs"
	      using Learns decomp1 decomp2 by auto
	    hence "predOrd xs x y"
	      using Cons by auto
	    thus ?thesis
	      using Learns by auto
	  qed
	qed
      }
      ultimately show ?case by fast
    qed
  }
  ultimately show ?thesis by fast
qed


subsection{* Input Terms *}


context reachable_state
begin

lemma knows_pairParts_closed:
  "m \<in> knows t \<Longrightarrow> pairParts m \<subseteq> knows t"
proof(induct arbitrary: m rule: reachable_induct)
  case init thus ?case by(auto simp: IK0_def) 
next
  case send thus ?case by(auto dest: pairParts_idemD)
next
  case decr thus ?case by(auto dest: pairParts_idemD)
next
  case tuple thus ?case by fastsimp
qed auto


lemmas knows_pairParts_closedD =
  subsetD[OF knows_pairParts_closed, rule_format]

lemmas rev_knows_pairParts_closedD =
  rev_subsetD[OF _ knows_pairParts_closed, rule_format]


lemma pairParts_before:
  "\<lbrakk> predOrd t (Ln m) y; m' \<in> pairParts m \<rbrakk> \<Longrightarrow>
   predOrd t (Ln m') y"
proof(induct rule: reachable_induct)
  case (hash t r s msg)
  then interpret s1: reachable_state P t r s
    by unfold_locales
  from hash show ?case
    by (fastsimp dest: s1.rev_knows_pairParts_closedD)
next
  case (encr t r s msg key)
  then interpret s1: reachable_state P t r s
    by unfold_locales
  from encr show ?case
    by (fastsimp dest: s1.rev_knows_pairParts_closedD)
next
  case (tuple t r s msg1 msg2)
  then interpret s1: reachable_state P t r s
    by unfold_locales
  from tuple show ?case
    by (fastsimp dest: s1.rev_knows_pairParts_closedD)
next
  case (decr t r s msg key)
  then interpret s1: reachable_state P t r s
    by unfold_locales
  from decr show ?case
    by (fastsimp dest: s1.rev_knows_pairParts_closedD)
next
  case (send t r s i "done" l msg todo msg)
  then interpret s1: reachable_state P t r s
    by unfold_locales
  from send show ?case
    by (fastsimp dest: s1.rev_knows_pairParts_closedD)
next
  case (recv t r s i "done" l msg todo)
  then interpret s1: reachable_state P t r s
    by unfold_locales
  from recv show ?case
    by (fastsimp dest: s1.rev_knows_pairParts_closedD)
next
  case (init r s) thus ?case by simp
qed

lemma Ln_before_inp:
  "(i, Recv l pt) \<in> steps t \<Longrightarrow> 
   Ln (inst s i pt) \<prec> St (i, Recv l pt)"
proof(induct arbitrary: i l pt rule: reachable_induct)
qed auto

lemmas knows_inp = in_knows_predOrd1[OF Ln_before_inp, rule_format]

text{* Three of the lemmas for the reasoning technique. *}
lemmas Input = Ln_before_inp

lemma split_before:
  "Ln (Tup m m') \<prec> y \<Longrightarrow> Ln m \<prec> y \<and> Ln m' \<prec> y"
  by (fastsimp intro: pairParts_before)

lemma split_knows:
  "Tup m m' \<in> knows t \<Longrightarrow> m \<in> knows t \<and> m' \<in> knows t"
  by (fastsimp intro: knows_pairParts_closedD)

end


subsection{* Case Distinction on Learning Messages *}

text{* Note that the hints are logically equal to true. Thus they have no logical
  content. However they are placed here to track the individual cases when 
  computing the decryption chains for a concrete message and protocol.
*}
fun decrChain :: "string \<Rightarrow> explicit_trace \<Rightarrow> event set \<Rightarrow> execmsg \<Rightarrow> execmsg \<Rightarrow> bool"
where
  "decrChain path t from (Enc msg key) m = 
   ( ( m = Enc msg key \<and> (\<forall> f \<in> from. predOrd t f (Ln m)) \<and> 
       hint ''decrChainPath'' path
     ) \<or>
     ( (\<forall> f \<in> from. predOrd t f (Ln (Enc msg key))) \<and> 
       decrChain (path@''E'') t {Ln (Enc msg key), Ln (inv key)} msg m  )
   )"
| "decrChain path t from (Tup x y) m = 
   ( ( m = Tup x y \<and> (\<forall> f \<in> from. predOrd t f (Ln m)) \<and>
       hint ''decrChainPath'' path
     ) \<or>
     decrChain (path@''L'') t from x m \<or>
     decrChain (path@''R'') t from y m
   )"
| "decrChain path t from msg m =
   ( m = msg \<and> (\<forall> f \<in> from. predOrd t f (Ln m)) \<and>
     hint ''decrChainPath'' path
   )"

lemma decrChain_append:
  "decrChain path t from msg m \<Longrightarrow> decrChain path (t@t') from msg m"
  by (induct path t "from" msg m rule: decrChain.induct) auto

lemma decrChain_unpair:
  "\<lbrakk> m' \<in> pairParts m; m' \<in> M;
     \<forall> f \<in> from. f \<in> Ln ` knows t \<or> f \<in> St ` steps t
   \<rbrakk> \<Longrightarrow> decrChain path (t@[Learns M]) from m m'"
by (induct m arbitrary: path M) (auto simp: remove_hints)

lemma decrChain_decrypt:
  "\<lbrakk> decrChain path t from msg (Enc m k);
     Enc m k \<in> knows t; inv k \<in> knows t;
     m' \<in> pairParts m; m' \<notin> knows t \<rbrakk> \<Longrightarrow>
   decrChain path' (t @ [Learns (pairParts m - knows t)]) from msg m'"
proof(induct msg arbitrary: path path' "from")
  case (Enc msg key)
  hence from_before [simp]: 
    "\<forall>f\<in>from. predOrd t f (Ln (Enc msg key))" by auto
  have "m = msg \<and> k = key \<or> 
    decrChain (path@''E'') t {Ln (Enc msg key), Ln (Message.inv key)} msg (Enc m k)"
    (is "?here \<or> ?nested")
    using Enc by auto
  moreover
  { assume "?here"
    hence "?case"
    proof(cases "m' = Enc m k")
      case True thus ?thesis
	using `?here` Enc by fastsimp
    next
      case False thus ?thesis
	using `?here` Enc
	by(auto intro!: decrChain_unpair)
    qed
  }
  moreover
  { assume "?nested"
    hence "?case" using Enc
      by (fastsimp dest!: Enc(2))
  }
  ultimately show ?case by fast
qed auto


lemma (in reachable_state) knows_cases_raw:
  assumes knows: "m' \<in> knows t"
  shows 
   "(m' \<in> IK0) \<or>
    (\<exists> m.   m' = Hash m   \<and> Ln m \<prec> Ln (Hash m)) \<or>
    (\<exists> m k. m' = Enc  m k \<and> Ln m \<prec> Ln (Enc m k) \<and> Ln k \<prec> Ln (Enc m k)) \<or>
    (\<exists> x y. m' = Tup  x y \<and> Ln x \<prec> Ln (Tup x y) \<and> Ln y \<prec> Ln (Tup x y)) \<or>
    (\<exists> i done todo. r i = Some (done, todo) \<and> 
       (\<exists> l pt. 
          Send l pt \<in> set done \<and>
          decrChain [] t {St (i, Send l pt)} (inst s i pt) m'
       )
    )"
  (is "?cases m' t r s")
proof -
  --{* Prove cases transfer lemma for trace extension *}
  { fix m' t t' r s
    let ?thesis = "?cases m' (t@t') r s"
    assume "?cases m' t r s" (is "?ik0 \<or> ?hash \<or> ?enc \<or> ?tup \<or> ?chain t r s")
    moreover
    { assume "?ik0"  hence "?thesis" by blast }    moreover
    { assume "?hash" hence "?thesis" by fastsimp } moreover
    { assume "?enc"  hence "?thesis" by fastsimp } moreover
    { assume "?tup"  hence "?thesis" by fastsimp } moreover
    { assume "?chain t r s"
      hence "?chain (t@t') r s" 
	by (fastsimp intro!: decrChain_append)
      hence "?thesis" by blast
    }
    ultimately have ?thesis by fast
  }
  note cases_appendI_trace = this

  --{* Prove actual thesis *}
  from knows show ?thesis
  proof (induct arbitrary: m' rule: reachable_induct)
    case init thus ?case by simp
  next
    case (hash t r s m)
    let ?t' = "t @ [Learns {Hash m}]"
    note IH = hash(2)
    have "m' \<in> knows t \<or> m' = Hash m" (is "?old \<or> ?new")
      using hash by fastsimp
    moreover
    { assume "?new" hence ?case 
	using `m \<in> knows t` by fastsimp 
    }
    moreover
    { assume "?old" 
      hence ?case by (fastsimp intro!: IH cases_appendI_trace)
    }
    ultimately show ?case by fast
  next
    case (encr t r s m k)
    let ?t' = "t @ [Learns {Enc m k}]"
    note IH = encr(2)
    have "m' \<in> knows t \<or> m' = Enc m k" (is "?old \<or> ?new")
      using encr by fastsimp
    moreover
    { assume "?new" hence ?case 
	using `m \<in> knows t` and `k \<in> knows t` by fastsimp 
    }
    moreover
    { assume "?old" 
      hence ?case by (fast intro!: IH cases_appendI_trace)
    }
    ultimately show ?case by fast
  next
    case (tuple t r s x y)
    let ?t' = "t @ [Learns {Tup x y}]"
    note IH = tuple(2)
    have "m' \<in> knows t \<or> m' = Tup x y" (is "?old \<or> ?new")
      using tuple by fastsimp
    moreover
    { assume "?new" hence ?case 
	using `x \<in> knows t` and `y \<in> knows t` by fastsimp 
    }
    moreover
    { assume "?old" 
      hence ?case by (fast intro!: IH cases_appendI_trace)
    }
    ultimately show ?case by fast
  next
    case (recv t r s i "done" l pt todo)
    hence "?cases m' t r s" (is "?ik0 \<or> ?hash \<or> ?enc \<or> ?tup \<or> ?chain t r s")
      by clarsimp
    moreover
    { assume "?ik0"  hence "?case" by blast    } moreover
    { assume "?hash" hence "?case" by fastsimp } moreover
    { assume "?enc"  hence "?case" by fastsimp } moreover
    { assume "?tup"  hence "?case" by fastsimp } moreover
    { let ?t' = "t@[Step (i, Recv l pt)]"
      and ?r' = "r(i \<mapsto> (done @ [Recv l pt], todo))"
      assume "?chain t r s" then
      obtain i' done' todo' l' pt'
	where thread': "r i' = Some (done', todo')"
	and send: "Send l' pt' \<in> set done'"
	and chain: "decrChain [] t {St (i', Send l' pt')} (inst s i' pt') m'"
	by auto
      then interpret th1: reachable_thread P t r s i' done' todo'
	using recv by unfold_locales auto
      moreover
      obtain done'' todo'' 
	where "Send l' pt' \<in> set done''"
	and "?r' i' = Some (done'', todo'')"
	using `r i = Some (done, Recv l pt # todo)` thread' send
	by (cases "i = i'") (fastsimp+)
      ultimately
      have "?chain ?t' ?r' s"
	using chain
	apply-
	apply(rule exI)+
	apply(rule conjI, assumption)
	by(fastsimp intro!: decrChain_append)+
      hence "?case" by auto
    }
    ultimately show ?case by fast
  next
    case (send t r s i "done" l pt todo m)
    then interpret th1: 
      reachable_thread P t r s i "done" "Send l pt # todo"
      by unfold_locales
    let ?r' = "r(i \<mapsto> (done @ [Send l pt], todo))"
    let ?m  = "inst s i pt"
    let ?t' = "(t @ [Step (i, Send l pt)]) @ [Learns (pairParts ?m - knows t)]"
    have "m' \<in> knows t \<or> m' \<in> pairParts m \<and> m' \<notin> knows t" (is "?old \<or> ?new")
      using send by fastsimp
    moreover
    { assume "?new"
      hence "m' \<in> pairParts (inst s i pt)" and "m' \<notin> knows t" 
	using `m = inst s i pt` by auto
      hence "decrChain [] ?t' {St (i, Send l pt)} ?m m'"
	by (fastsimp intro!: decrChain_unpair)
      moreover
      have "?r' i = Some (done @ [Send l pt], todo)"
	using th1.thread_exists by auto
      ultimately
      have ?case using `m = inst s i pt`
	apply-
	apply(rule disjI2)+
	apply(rule exI)+
	apply(rule conjI, assumption)
	apply(auto)
	done
    }
    moreover
    { assume "?old" 
      hence "?cases m' t r s" (is "?ik0 \<or> ?hash \<or> ?enc \<or> ?tup \<or> ?chain t r s")
	using send by clarsimp
      moreover
      { assume "?ik0"  hence "?case" by blast    } moreover
      { assume "?hash" hence "?case" by fastsimp } moreover
      { assume "?enc"  hence "?case" by fastsimp } moreover
      { assume "?tup"  hence "?case" by fastsimp } moreover
      { assume "?chain t r s" then
	obtain i' done' todo' l' pt'
	  where thread': "r i' = Some (done', todo')"
	  and send: "Send l' pt' \<in> set done'"
	  and chain: "decrChain [] t {St (i', Send l' pt')} (inst s i' pt') m'"
	  by auto
	obtain done'' todo'' 
	  where "Send l' pt' \<in> set done''"
	  and "(r(i \<mapsto> (done @ [Send l pt], todo))) i' = Some (done'', todo'')"
	  using `r i = Some (done, Send l pt # todo)` thread' send
	  by (cases "i = i'") (fastsimp+)
	hence "?chain ?t' ?r' s"
	  using chain
	  apply-
	  apply(rule exI)+
	  apply(rule conjI, assumption)
	  by(fastsimp intro!: decrChain_append)+
	hence "?case" using `m = inst s i pt` by auto
      }
      ultimately have ?case by fast
    }
    ultimately show ?case by fast
  next
    case (decr t r s m k)
    then interpret s1: reachable_state P t r s
      by unfold_locales
    let ?t' = "t @ [Learns (pairParts m - knows t)]"
    note IH = decr(2)
    have "m' \<in> knows t \<or> m' \<in> pairParts m \<and> m' \<notin> knows t" (is "?old \<or> ?new")
      using decr by fastsimp
    moreover
    { assume "?new"
      hence "m' \<in> pairParts m" and "m' \<notin> knows t" by auto
      have 
	"predOrd t (Ln m) (Ln (Enc m k)) \<and> predOrd t (Ln k) (Ln (Enc m k)) \<or>
        (\<exists>i done todo. r i = Some (done, todo) \<and>
          (\<exists>l pt. Send l pt \<in> set done \<and>
                  decrChain [] t {St (i, Send l pt)} (inst s i pt) (Enc m k)))"
	(is "?fake_enc \<or> ?chain t (Enc m k)")
	using IH[OF `Enc m k \<in> knows t`] by auto
      moreover
      { assume "?fake_enc"
	hence "?case" using `?new`
	  by (auto dest!: in_knows_predOrd1 s1.rev_knows_pairParts_closedD)
      }
      moreover
      { assume "?chain t (Enc m k)" then
	obtain i' done' todo' l' pt'
	  where thread': "r i' = Some (done', todo')"
	  and send: "Send l' pt' \<in> set done'"
	  and chain: "decrChain [] t {St (i', Send l' pt')} (inst s i' pt') (Enc m k)"
	  by auto
	moreover
	hence "decrChain [] ?t' {St (i', Send l' pt')} (inst s i' pt') m'"
	  using `?new` `Enc m k \<in> knows t` `inv k \<in> knows t`
	  by (fastsimp intro!: decrChain_decrypt)
	ultimately
	have "?chain ?t' m'" by fastsimp
	hence "?case" by blast
      }
      ultimately have ?case by fast
    }
    moreover
    { assume "?old" 
      hence ?case by (fast intro!: IH cases_appendI_trace)
    }
    ultimately show ?case by fast thm decr
  qed
qed

end