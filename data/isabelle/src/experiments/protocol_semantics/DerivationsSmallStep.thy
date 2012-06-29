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

datatype 's node = State nat | Msg execmsg

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
     , D \<union> 
       (Msg ` Option.set inp) \<times>  {State (Suc (length tr))} \<union>
       (\<Union> m \<in> Option.set out. 
          {State (Suc (length tr))} \<times> (Msg ` (pairParts m - knows D)))
     ) \<in> derivs P"

| decr:
  "\<lbrakk> (tr, D) \<in> derivs P;
     Enc m k \<in> knows D;
     inv k \<in> knows D
   \<rbrakk> \<Longrightarrow> 
     ( tr
     , D \<union> {Msg (Enc m k), Msg (inv k)} \<times> (Msg ` (pairParts m - knows D))
     ) \<in> derivs P"

| hash:
  "\<lbrakk> (tr, D) \<in> derivs P;
     m \<in> knows D;
     Hash m \<notin> knows D
   \<rbrakk> \<Longrightarrow> 
     (tr, insert (Msg m, Msg (Hash m)) D) \<in> derivs P"

| tuple:
  "\<lbrakk> (tr, D) \<in> derivs P;
     x \<in> knows D;
     y \<in> knows D;
     Tup x y \<notin> knows D
   \<rbrakk> \<Longrightarrow> 
     (tr, {Msg x, Msg y} \<times> {Msg (Tup x y)} \<union> D) \<in> derivs P"

| encr:
  "\<lbrakk> (tr, D) \<in> derivs P;
     m \<in> knows D;
     k \<in> knows D;
     Enc m k \<notin> knows D
   \<rbrakk> \<Longrightarrow> 
     (tr, {Msg m, Msg k} \<times> {Msg (Enc m k)} \<union> D) \<in> derivs P"

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

lemma State2_index_in_trace:
  "(x, State i) \<in> D \<Longrightarrow> i < length tr"
by (induct rule: derivs_induct)
   (auto simp: nth_append)


lemma (in -) in_knowsD: "m \<in> knows D \<Longrightarrow> \<exists> x. (x, Msg m) \<in> D"
  by (auto simp: knows_def Range_iff)

lemma (in -) knows_iff: "(m \<in> knows D) = (\<exists> x. (x, Msg m) \<in> D)"
  by (auto simp: knows_def Range_iff)

lemma Msg1_imp_Msg2:
  "(Msg m, y) \<in> D \<Longrightarrow> \<exists> x. (x, Msg m) \<in> D"
  by (induct rule: derivs_induct) (auto simp: knows_iff)

definition derivOrd
where "derivOrd = 
         (D \<union> 
          { (State i, State (Suc i)) | i. Suc i < length tr } \<union>
          { (Msg m', y) | m m' y. (Msg m, y) \<in> D \<and> m' \<in> pairParts m } 
         )\<^sup>+"

thm pairParts_idemD

lemma pairParts_trans:
  "\<lbrakk>x \<in> pairParts y; y \<in> pairParts z\<rbrakk> \<Longrightarrow> x \<in> pairParts z"
  by (auto intro: pairParts_idemD)

lemma derivOrd_pairParts_closed: 
  assumes asms: "(Msg mx, y) \<in> derivOrd" "mx' \<in> pairParts mx"
  shows "(Msg mx', y) \<in> derivOrd"
proof -
  { fix x
    have "\<lbrakk> (x, y) \<in> derivOrd; x = Msg mx; mx' \<in> pairParts mx \<rbrakk> 
         \<Longrightarrow> (Msg mx', y) \<in> derivOrd"
      unfolding derivOrd_def
      apply(induct rule: trancl_trans_induct[consumes 1])
      apply(auto dest: pairParts_trans intro!: r_into_trancl)
      done
  }
  thus ?thesis using asms by auto
qed

lemma derivOrd_Tup1D: 
  "(Msg (Tup mx my), y) \<in> derivOrd \<Longrightarrow> (Msg mx, y) \<in> derivOrd"
  by (auto dest: derivOrd_pairParts_closed)

lemma derivOrd_Tup2D: 
  "(Msg (Tup mx my), y) \<in> derivOrd \<Longrightarrow> (Msg my, y) \<in> derivOrd"
  by (auto dest: derivOrd_pairParts_closed)


lemma (in -) irrefl_trancl_rtranclD:
  assumes  irrefl: "\<And> x. (x,x) \<notin> R\<^sup>+"
  and in_rtrancl: "(y, x) \<in> R\<^sup>*" 
  shows "(x, y) \<notin> R"
  using in_rtrancl
  apply(clarsimp)
  apply(drule rtranclD)
  apply(safe)
  apply(fastsimp dest: r_into_trancl simp: irrefl)
  apply(fastsimp dest: trancl_into_trancl simp: irrefl)
  done



lemma (in -) irrefl_Un_new:
  assumes irr_R: "\<And> x. (x,x) \<notin> R\<^sup>+"
  and     irr_S: "\<And> x. (x,x) \<notin> S\<^sup>+"
  and     new_S: "\<And> x y z. (x,y) \<in> S \<Longrightarrow> (y,z) \<notin> R"
  shows "(x,x) \<notin> (R \<union> S)\<^sup>+"
proof -
  { fix x y z
    assume "(x,y) \<in> S\<^sup>+" hence "(y,z) \<notin> R"
      by (blast dest!: tranclD2 new_S)
  }
  note new_trancl_S = this
  { fix x y z
    assume "(x,y) \<in> S" hence "(y,z) \<notin> R\<^sup>+"
      by (blast dest!: tranclD new_S)
  }
  note new_trancl_R = this
  { fix x y
    assume "(y, x) \<in> (R \<union> S)\<^sup>*" 
    hence "(x, y) \<notin> R"
      by(blast dest: rtrancl_Un_separator_converseE
                     rtranclD new_S new_trancl_R
                     irrefl_trancl_rtranclD[OF irr_R])
  }
  moreover
  { fix x y
    assume "(y, x) \<in> (R \<union> S)\<^sup>*" 
    hence "(x, y) \<notin> S"
      apply(subst (asm) Un_commute)
      by(blast dest: rtrancl_Un_separatorE
                     rtranclD new_S new_trancl_S
                     irrefl_trancl_rtranclD[OF irr_S])
  }
  ultimately
  show ?thesis
    by (fast intro!: irrefl_tranclI)
qed


lemma (in - ) irr_insert_tranclD:
  "\<lbrakk> (x,x) \<in> (insert (a,b) R)\<^sup>+; (b,a) \<notin> R\<^sup>+; (x,x) \<notin> R\<^sup>+ \<rbrakk> \<Longrightarrow> a = b"
  apply(clarsimp simp: trancl_insert)
  apply(subgoal_tac "(b,a) \<in>  R\<^sup>*")
  apply(simp add: rtrancl_eq_or_trancl)
  apply(fastsimp intro: rtrancl_trans)
  done

end

lemma acyclic_empty [iff]: "acyclic {}"
  by (simp add: acyclic_def)


lemma knows_empty [iff]: "knows {} = {}"
  by (auto simp: knows_def)

lemma knows_Un [simp]: "knows (M \<union> N) = knows M \<union> knows N"
  by (auto simp: knows_def)

lemma knows_insert_Msg [simp]: "knows (insert (x, Msg m) D) = insert m (knows D)"
  by(auto simp: knows_def)

lemma knows_insert_State [simp]: "knows (insert (x, State s) D) = knows D"
  by(auto simp: knows_def)

lemma in_knows_times: "M \<noteq> {} \<Longrightarrow> (m \<in> knows (M \<times> N)) = (Msg m \<in> N)"
  by (auto simp: knows_iff)


lemma (in -) in_trancl_into_r1: "(x,y) \<in> R\<^sup>+ \<Longrightarrow> \<exists> z. (x,z) \<in> R"
  by(drule DomainI, simp add: Domain_iff)

lemma (in derivation) knows_pairParts_closed:
  "\<lbrakk> m \<in> knows D; x \<in> pairParts m \<rbrakk> \<Longrightarrow> x \<in> knows D"
proof(induct arbitrary: m rule: derivs_induct)
  case proto thus ?case
    by (auto simp: knows_iff image_def dest: pairParts_idemD)
next
  case (decr tr D mx kx) thus ?case
    by (auto simp: knows_iff image_def dest: pairParts_idemD)
next
  case (tuple tr D mx my) thus ?case
    by force
qed auto

lemma (in derivation) Msg1_imp_knows:
  "(Msg m, y) \<in> D \<Longrightarrow> m \<in> knows D"
  by (auto dest: Msg1_imp_Msg2 simp: knows_iff)

lemma irrefl_disjoint_product:
  "A \<inter> B = {} \<Longrightarrow> 
  (x, x) \<notin> {(Msg a, Msg b) | a b. a \<in> A \<and> b \<in> B}\<^sup>+"
  apply -
  apply(rule irrefl_tranclI)
  apply(auto dest!: rtranclD)
  apply(drule RangeI)
  apply(simp add: Range_iff)
  apply(fastsimp)
  done

lemma irrefl_disjoint_fanin:
  "b \<notin> A \<Longrightarrow> 
  (x, x) \<notin> {(Msg a, Msg b) | a. a \<in> A }\<^sup>+"
  apply -
  apply(rule irrefl_tranclI)
  apply(auto dest!: rtranclD)
  apply(drule RangeI)
  apply(simp add: Range_iff)
  done


lemma irrefl_disjoint_fanin_state:
  "(x, x) \<notin> {(Msg a, State b) | a. a \<in> A }\<^sup>+"
  apply -
  apply(rule irrefl_tranclI)
  apply(auto dest!: rtranclD)
  apply(drule RangeI)
  apply(simp add: Range_iff)
  done


lemma size_pairParts:
  "x \<in> pairParts m \<Longrightarrow> size x \<le> size m"
  by (induct m) auto


lemma (in derivation) State1_index_in_trace:
  "(State i, y) \<in> D \<Longrightarrow> i < length tr"
  by (induct rule: derivs_induct)
     (auto simp: nth_append)


lemma irrefl_subst: 
  "\<lbrakk> (x,x) \<notin> R\<^sup>+; R = S \<rbrakk> \<Longrightarrow> (x,x) \<notin> S\<^sup>+" 
  by simp

context derivation
begin

lemma derivOrd_irr:
  "(x, x) \<notin> derivOrd"
unfolding derivOrd_def
proof(induct arbitrary: x rule: derivs_induct)
  case init thus ?case by simp
next
  case (hash tr D m) 
  then interpret this_deriv: derivation P tr D by unfold_locales
  let ?R = "(D \<union> {(State i, State (Suc i)) |i. Suc i < length tr} \<union>
     {(Msg m', y) | m m' y.  (Msg m, y) \<in> D \<and> m' \<in> pairParts m})"
  let ?S = "{ (Msg m', Msg (Hash m)) | m'. m' \<in> pairParts m}"
  have "(x,x) \<notin> (?R \<union> ?S)\<^sup>+"
    apply -
    apply(rule irrefl_Un_new)
    apply(rule hash)
    apply(rule irrefl_disjoint_fanin)
    apply(clarsimp dest!: size_pairParts)
    apply(fastsimp dest!: this_deriv.Msg1_imp_knows 
                    dest: this_deriv.knows_pairParts_closed 
                    simp: hash)
    done
  thus ?case
    by (fastsimp elim!: irrefl_subst)
next
  case (tuple tr D mx my) 
  then interpret this_deriv: derivation P tr D by unfold_locales
  let ?R = "(D \<union> {(State i, State (Suc i)) |i. Suc i < length tr} \<union>
     {(Msg m', y) | m m' y.  (Msg m, y) \<in> D \<and> m' \<in> pairParts m})"
  let ?S = "{ (Msg m', Msg \<lbrace>mx, my\<rbrace>) 
            | m'. m' \<in> pairParts mx \<union> pairParts my   }"
  have "(x,x) \<notin> (?R \<union> ?S)\<^sup>+"
    apply -
    apply(rule irrefl_Un_new)
    apply(rule tuple)
    apply(rule irrefl_disjoint_fanin)
    apply(fastsimp dest!: size_pairParts)
    apply(fastsimp dest!: this_deriv.Msg1_imp_knows 
                    dest: this_deriv.knows_pairParts_closed 
                    simp: tuple)
    done
  thus ?case
    by (fastsimp elim!: irrefl_subst)
next
  case (encr tr D m k) 
  then interpret this_deriv: derivation P tr D by unfold_locales
  let ?R = "(D \<union> {(State i, State (Suc i)) |i. Suc i < length tr} \<union>
     {(Msg m', y) | m m' y.  (Msg m, y) \<in> D \<and> m' \<in> pairParts m})"
  let ?S = "{ (Msg m', Msg (Enc m k)) 
            | m'. m' \<in> pairParts m \<union> pairParts k   }"
  have "(x,x) \<notin> (?R \<union> ?S)\<^sup>+"
    apply -
    apply(rule irrefl_Un_new)
    apply(rule encr)
    apply(rule irrefl_disjoint_fanin)
    apply(fastsimp dest!: size_pairParts)
    apply(fastsimp dest!: this_deriv.Msg1_imp_knows 
                    dest: this_deriv.knows_pairParts_closed 
                    simp: encr)
    done
  thus ?case
    by (fastsimp elim!: irrefl_subst)
next
  case (decr tr D m k) 
  then interpret this_deriv: derivation P tr D by unfold_locales
  let ?R = "(D \<union> {(State i, State (Suc i)) |i. Suc i < length tr} \<union>
     {(Msg m', y) | m m' y.  (Msg m, y) \<in> D \<and> m' \<in> pairParts m})"
  let ?S = "{ (Msg m', Msg y) 
            | m' y. m' \<in> insert (Enc m k) (pairParts (inv k)) \<and> 
                    y \<in> (pairParts m - knows D) }"
  have "(x,x) \<notin> (?R \<union> ?S)\<^sup>+"
    apply -
    apply(rule irrefl_Un_new)
    apply(rule decr)
    apply(rule irrefl_disjoint_product)
    defer 1
    apply(fastsimp dest!: this_deriv.Msg1_imp_knows 
                    dest: this_deriv.knows_pairParts_closed 
                    simp: decr)
    apply(auto)
    apply(fastsimp dest!: size_pairParts)
    apply(insert decr)
    apply(fastsimp dest: this_deriv.knows_pairParts_closed) 
    done
  thus ?case
    by (fastsimp elim!: irrefl_subst)
next
  case (proto tr s D inp s' out)
  then interpret this_deriv: derivation P "tr @ [s]" D
    by unfold_locales
  let ?R = "(D \<union> 
            {(State i, State (Suc i)) |i. Suc i < length (tr @ [s])} \<union>
            {(Msg m', y) | m m' y.  (Msg m, y) \<in> D \<and> m' \<in> pairParts m})"
  let ?S = "{(State (length tr), State (Suc (length tr)))} \<union> 
            ({ (Msg m', State (Suc (length tr))) 
            | m'. m' \<in> (\<Union> mi \<in> Option.set inp. pairParts mi) } \<union>
             (\<Union>m\<in>Option.set out. {State (Suc (length tr))} \<times>
                                  Msg ` (pairParts m - knows D))
            )"
  have "(x,x) \<notin> (?R \<union> ?S)\<^sup>+"
    apply -
    apply(rule irrefl_Un_new)
    apply(rule proto) 
    defer 1
    apply(fastsimp dest!: this_deriv.State1_index_in_trace
                          this_deriv.Msg1_imp_knows 
                    dest: this_deriv.knows_pairParts_closed)
    apply(rule irrefl_Un_new) 
    apply(fastsimp simp: trancl_insert)
defer 1
    apply(fastsimp dest: this_deriv.knows_pairParts_closed)
    apply(rule irrefl_Un_new)
    apply(rule irrefl_disjoint_fanin_state)
defer 1
    apply(insert proto(3))
    apply(clarsimp)
    apply(fastsimp dest: this_deriv.knows_pairParts_closed)

    apply(cases out, clarsimp)
    apply(clarsimp)
    apply(erule contrapos_pp) back
    apply(rule irrefl_tranclI)
    apply(auto)
    apply(drule rtranclD)
    apply(simp)
    apply(drule RangeI)
    apply(simp add: Range_iff image_def)
    done
  thus ?case
    by (fastsimp elim!: irrefl_subst)
qed

lemma derivOrd_trans:
  "\<lbrakk> (x,y) \<in> derivOrd; (y,z) \<in> derivOrd \<rbrakk> \<Longrightarrow> (x,z) \<in> derivOrd"
  unfolding derivOrd_def by (auto intro!: trancl_trans)

lemma derivOrd_asymD:
  "(x,y) \<in> derivOrd \<Longrightarrow> (y,x) \<notin> derivOrd"
  by(auto dest: derivOrd_trans simp: derivOrd_irr)

lemma (in -) finite_pairParts [simp, intro!]:
  "finite (pairParts m)"
  by (induct m) auto

(* MISSING in Isabelle library *)  
lemma (in -) Option_finite_set [iff]:
  "finite (Option.set x)"
  by (cases x) (auto)

lemma finite_D:
  "finite D"
proof -
  { fix A B assume "finite A" hence "finite (A - B)" by auto }
  note finite_setminus = this
  show ?thesis
    apply (induct rule: derivs_induct)
    apply(auto intro!: finite_setminus finite_cartesian_product finite_imageI)
    done
qed

lemma derivOrd_finite:
  "finite derivOrd"
proof -
  have "{i. Suc i < length tr} \<subseteq> {i. i < length tr}" by clarsimp
  hence "finite {i. Suc i < length tr}"
    by (auto dest!: finite_subset intro!: finite_Collect_less_nat)
  moreover
  have "finite (\<Union> { {(Msg m', y) | m m' y. d = (Msg m, y) \<and> m' \<in> pairParts m} | d. d \<in> D})"
    apply(rule finite_Union)
    apply(rule finite_image_set)
    apply(simp add: finite_D)
    apply(auto)
    apply(case_tac a, auto)
    done
  hence "finite {(Msg m', y) 
                | m m' y. (Msg m, y) \<in> D \<and> m' \<in> pairParts m}"
    apply -
    apply(rule finite_subset, auto)
    done
  ultimately
  show ?thesis using finite_D unfolding derivOrd_def
    by (auto simp: finite_trancl)
qed

lemma derivOrd_trancl [simp]:
  "derivOrd\<^sup>+ = derivOrd"
  unfolding derivOrd_def by auto

lemma derivOrd_wf: "wf derivOrd"
  by (auto intro!: finite_acyclic_wf derivOrd_finite acyclicI
             simp: derivOrd_irr)

end

section{* Relating the two models *}


lemma dy_conv_derivs:
  "{ (tr, M)       | tr M M'. M \<subseteq> M' \<and> (tr, M) \<in> dy P     } = 
   { (tr, knows D) | tr D.             (tr, D) \<in> derivs P }"
  oops

(* MOVE *)


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
    hence "(tr, D \<union> insert (Msg m, Msg (Hash m)) D') \<in> derivs P"
      using ext by(fastsimp intro!: derivs.hash)
    thus ?thesis using ext and `M \<subseteq> knows D` and False
      by bestsimp
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
    hence "(tr, D \<union> ({Msg x, Msg y} \<times> {Msg \<lbrace>x, y\<rbrace>} \<union> D' \<union> D'')) 
           \<in> derivs P"
      using ext1 and ext2
      apply clarsimp
      apply(drule derivs.tuple) back  
      apply(auto)
      done
    thus ?thesis using ext1 ext2 `M \<subseteq> knows D` and False
      apply -
      apply(rule exI, rule conjI, assumption)
      by auto
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
    hence "(tr, D \<union> ({Msg m, Msg k} \<times> {Msg (Enc m k)} \<union> D' \<union> D'')) 
           \<in> derivs P"
      using ext1 and ext2
      apply clarsimp
      apply(drule derivs.encr) back  
      apply(auto)
      done
    thus ?thesis using ext1 ext2 `M \<subseteq> knows D` and False
      apply -
      apply(rule exI, rule conjI, assumption)
      by auto
  qed
next
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

lemma knows_times: 
  "N \<noteq> {} \<Longrightarrow> knows (N \<times> N') = {m. Msg m \<in> N'}"
  by (auto simp: knows_iff)

lemma derivs_imp_dy:
  "(tr, D) \<in> derivs P \<Longrightarrow> (tr, knows D) \<in> dy P"
proof(induct rule: derivs.induct)
  case init thus ?case by (auto intro!: dy.init)
next
  case (proto tr s D inp s' out)
  moreover
  have "knows (Msg ` Option.set inp \<times>
               {State (Suc (length tr))}) = {}"
    by (auto intro!: set_ext simp: knows_iff)
  moreover
  have "knows (\<Union>m\<in>Option.set out.
                 {State (Suc (length tr))} \<times>
                 Msg ` (pairParts m - knows D))
        = (\<Union>m\<in>Option.set out. pairParts m) - knows D"
    by (cases out, simp) (auto intro!: set_ext simp: knows_iff)
  ultimately 
  show ?case
    apply -
    apply(drule dy.proto, assumption+)
    apply(simp)
    apply(cases out, fastsimp elim: ssubst)
    apply(force elim: ssubst 
                dest: pairParts_in_dy simp: insert_absorb)
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

lemma (in derivation) initial_state [simp]:
  "tr ! 0 = fst P"
 by (induct rule: derivs_induct) (auto simp: nth_append)

lemma (in derivation) reachable_state_transition:
  "\<lbrakk> 0 \<le> i; Suc i < length tr \<rbrakk> \<Longrightarrow> 
  (\<exists> inp out. 
     (tr!i, inp, tr!(Suc i), out) \<in> snd P \<and> 
     (\<forall> mi. inp = Some mi \<longrightarrow> (Msg mi, State (Suc i)) \<in> D))"
proof(induct rule: derivs_induct)
  case (proto tr sx D inp sx' out) show ?case
  proof(cases "i < length tr")
    case True thus ?thesis using proto
      by(force simp: nth_append)
  next
    case False 
    hence "i = length tr" using proto by force
    thus ?thesis using proto
      by(force simp: nth_append)
  qed
qed auto

lemma (in derivation) State2_index_nonzero:
  "(x, State i) \<in> D \<Longrightarrow> 0 < i"
 by (induct rule: derivs_induct) auto

definition "states" :: "'s dependencies \<Rightarrow> nat set"
where "states D \<equiv> { i. \<exists> x. (x, State i) \<in> D }"

lemma states_mono: "D \<subseteq> D' \<Longrightarrow> states D \<subseteq> states D'"
  by (auto simp: states_def)

lemmas states_monoD = rev_subsetD[OF _ states_mono]

lemma states_empty [iff]: "states {} = {}"
  by (auto simp: states_def)

lemma states_Un [simp]: "states (M \<union> N) = states M \<union> states N"
  by (auto simp: states_def)

lemma states_insert_State [simp]: 
  "states (insert (x, State i) D) = insert i (states D)"
  by(auto simp: states_def)

lemma states_insert_Msg [simp]: 
  "states (insert (x, Msg m) D) = states D"
  by(auto simp: states_def)

lemma states_iff: "(i \<in> states D) = (\<exists> x. (x, State i) \<in> D)"
  by (auto simp: states_def)

lemma in_states_times: 
  "M \<noteq> {} \<Longrightarrow> (i \<in> states (M \<times> N)) = (State i \<in> N)"
  by (auto simp: states_iff)


lemma (in derivation) knows_cases:
  assumes knows: "m' \<in> knows D"
  shows 
   "(\<exists> m.   m' = Hash m   \<and> (Msg m, Msg (Hash m)) \<in> D    ) \<or>
    (\<exists> m k. m' = Enc  m k \<and> (Msg m, Msg (Enc m k)) \<in> D \<and> 
                            (Msg k, Msg (Enc m k)) \<in> D   ) \<or>
    (\<exists> x y. m' = Tup  x y \<and> (Msg x, Msg (Tup x y)) \<in> D \<and> 
                            (Msg y, Msg (Tup x y)) \<in> D   ) \<or>
    (\<exists> i \<in> {1..(length tr - 1)}. \<exists> inp m.        
       (tr!(i - 1), inp, tr!i, Some m) \<in> snd P \<and> 
       chain D {State i} m m' \<and>
       (\<forall> mi. inp = Some mi \<longrightarrow> (Msg mi, State i) \<in> D)
    )"
  (is "?cases m' tr D")
proof -
  --{* Prove case monotonicity *}
  { fix m' tr tr' D D'
    let ?thesis = "?cases m' (tr@tr') D'"
    assume "?cases m' tr D" (is "?hash \<or> ?enc \<or> ?tup \<or> ?chain tr D")
      and  "D \<subseteq> D'"
    moreover
    { assume "?hash" hence "?thesis" using `D \<subseteq> D'` by blast} moreover
    { assume "?enc"  hence "?thesis" using `D \<subseteq> D'` by blast} moreover
    { assume "?tup"  hence "?thesis" using `D \<subseteq> D'` by blast} moreover
    { assume "?chain tr D"
      hence "?chain (tr@tr') D'" using `D \<subseteq> D'`
        apply(clarsimp)
        apply(rule_tac x=i in bexI)
        apply(force intro: chain_mono simp: nth_append)
        apply(force)
        done
      hence "?thesis" by blast
    }
    ultimately have ?thesis by fast
  }
  note cases_append_mono = this[rule_format]
  { fix m' tr tr' D D'
    assume "?cases m' tr D" and  "D \<subseteq> D'"
    hence  "?cases m' tr D'"
      apply -
      apply(drule_tac tr'="[]" in cases_append_mono)
      by auto
  }
  note cases_mono = this[rule_format]

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
    { assume "?new" thm IH[OF `Enc m k \<in> knows D`]
      have 
        "((Msg m, Msg (Enc m k)) \<in> D \<and> (Msg k, Msg (Enc m k)) \<in> D) \<or>
         (\<exists>i \<in> {1..(length tr - 1)}. \<exists>inp ma.
            (tr ! (i - 1), inp, tr ! i, Some ma) \<in> snd P \<and>
            chain D {State i} ma (Enc m k) \<and> 
            (\<forall> mi. inp = Some mi \<longrightarrow> (Msg mi, State i) \<in> D)
         )
        "
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
        assume "?chain D (Enc m k)"
        hence "?chain ?D' m'" using `?new`
          apply(clarsimp)
          apply(rule bexI | rule exI | rule conjI | assumption)+
          apply(rule chain_decrypt)
          apply(erule chain_mono)
          by auto
	hence "?case" by blast
      }
      ultimately have ?case by fast
    }
    ultimately show ?case by fast
  next
    case (proto tr s D inp s' out m')
    note IH = proto(2)
    let ?ns' = "State (Suc (length tr))"
    let ?D' = "D \<union> Msg ` Option.set inp \<times> {?ns'}
                \<union> (\<Union> m\<in>Option.set out. 
                      {?ns'} \<times> Msg ` (pairParts m - knows D))"
    have "m' \<in> knows D \<or> 
          (\<exists> m. out = Some m \<and> m' \<in> pairParts m \<and> m' \<notin> knows D)" 
      (is "?old \<or> ?new")
      using proto(5) by (auto simp: knows_iff)
    moreover
    { assume "?old" hence ?case 
        apply -
        apply(drule cases_append_mono[OF IH, of _ _ "[s']"])
        prefer 2 
        apply(simp only: append_Nil append_Cons append_assoc)
        by force
    }
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
        by (force simp: nth_append)
    }
    ultimately show ?case by fast
  qed
qed


locale dy_state = 
  fixes P  :: "'s nts"
  and   tr :: "'s list"
  and   M  :: "execmsg set"
  assumes in_dy: "(tr, M) \<in> dy P"
begin
  text{* A local variant of the induction rule of @{term "dy"}. *}
  lemmas dy_induct = dy.induct
    [ OF in_dy
    , rule_format
    , consumes 0
    , case_names init proto infer
    ]
end

sublocale derivation \<subseteq> dy_state P tr "knows D"
  using derivable 
  by unfold_locales (auto intro!: derivs_imp_dy)



section{* Executing Protocol Scripts *}

types threadpool = "tid \<rightharpoonup> (rolestep list \<times> rolestep list)"

types state = "((tid \<times> rolestep) option \<times> threadpool \<times> store) option"

definition proto2nts :: "proto \<Rightarrow> state nts"
where "proto2nts P =
  ( None 
  , ({ ( None, None, Some (None, th, st), None)
     | th st.
       (\<forall> i done todo. th i = Some (done,todo) \<longrightarrow> 
                                done = [] \<and> todo \<in> P) \<and>
       (\<forall> a i. st (AVar a, i) \<in> Compromised \<union> Uncompromised)
     }
     \<union>
     { (None, None, None, Some m) 
     | m. 
       m \<in> IK0
     }
     \<union>
     ( { ( Some (prev, th, st)                          
         , Some (inst st i pt)
         , Some ( Some (i, Recv l pt)
                , th(i\<mapsto> (done @ [Recv l pt], todo))
                , st
                )
         , None 
         )
       | prev th st i l pt done todo.
         th i = Some (done, Recv l pt # todo)
       }
     )
     \<union>
     ( { ( Some (prev, th, st)                          
         , None
         , Some ( Some (i, Send l pt)
                , th(i\<mapsto> (done @ [Send l pt], todo))
                , st
                )
         , Some (inst st i pt) 
         )
       | prev th st i l pt done todo.
         th i = Some (done, Send l pt # todo)
       }
     )
    )
  )
"

text{* A direct formulation as an inductive set: gives us easy
access to a customized induction scheme and eliminiation rules.
*}

inductive_set dy_script
for P :: proto
where
  init: "([None], {}) \<in> dy_script P"

| init_proto:
  "\<lbrakk> (tr@[None], M) \<in> dy_script P;
     \<forall> i done todo.
       th i = Some (done, todo) \<longrightarrow> done = [] \<and> todo \<in> P;
     \<forall>a i. st (AVar a, i) \<in> Compromised \<or>
               st (AVar a, i) \<in> Uncompromised
   \<rbrakk> \<Longrightarrow> (tr@[None, Some (None, th, st)], M) \<in> dy_script P"

| ik0:
  "\<lbrakk> (tr @ [None], M) \<in> dy_script P; 
     m \<in> IK0
   \<rbrakk> \<Longrightarrow> (tr @ [None, None], insert m M) \<in> dy_script P"

| send:
  "\<lbrakk> (tr @ [Some (prev, th, st)], M) \<in> dy_script P;
     th i = Some (done, Send l pt # todo)
   \<rbrakk> \<Longrightarrow> (tr @
           [Some (prev, th, st),
            Some
             (Some (i, Send l pt), th(i \<mapsto>
              (done @ [Send l pt], todo)), st)],
           insert (inst st i pt) M)
          \<in> dy_script P"

| recv:
  "\<lbrakk> (tr @ [Some (prev, th, st)], M) \<in> dy_script P;
     inst st i pt \<in> M;
     th i = Some (done, Recv l pt # todo)
   \<rbrakk> \<Longrightarrow> (tr @
           [Some (prev, th, st),
            Some
             (Some (i, Recv l pt), th(i \<mapsto>
              (done @ [Recv l pt], todo)), st)],
           M)
          \<in> dy_script P"

| infer:
  "\<lbrakk>(tr, M) \<in> dy_script P; m \<in> infer M
   \<rbrakk> \<Longrightarrow> (tr, insert m M) \<in> dy_script P"


lemma dy_proto2nts_conv_dy_script:
  "dy (proto2nts P) = dy_script P"
  apply(simp add: dy_script_def dy_scriptp_def dy_def dyp_def)
  apply(rule_tac P="\<lambda> x. ?X = Collect (split (lfp x))" in subst) defer 1
  apply(rule refl)
  apply(rule ext)+
  apply(force simp: proto2nts_def)
  done


locale script_dy = wf_proto +
  fixes tr :: "state list"
  and   M  :: "execmsg set"
  assumes in_dy_script: "(tr, M) \<in> dy_script P"
begin
  text{* A local variant of the induction rule of @{term "dy"}. *}
  lemmas script_dy_induct = dy_script.induct
    [ OF in_dy_script
    , rule_format
    , consumes 0
    , case_names init init_proto ik0 send recv infer
    ]
end

locale script_derivation = wf_proto +
  fixes tr :: "state list"
  and   D  :: "state dependencies"
  assumes in_derivs: "(tr, D) \<in> derivs (proto2nts P)"

sublocale script_derivation \<subseteq> derivation "proto2nts P" tr D
  using in_derivs by unfold_locales

definition steps :: "state list \<Rightarrow> (tid \<times> rolestep) list"
where "steps tr = filtermap 
  (\<lambda> x. case x of Some (Some step, th, st) => Some step 
                | _                        => None) tr"

lemma steps_Nil [simp]: 
  "steps [] = []"
  by (simp add: steps_def)

lemma steps_Cons [simp]:
  "steps (None # tr) = steps tr"
  "steps (Some (None, th, st) # tr) = steps tr"
  "steps (Some (Some step, th, st) # tr) = step # (steps tr)"
  by (induct tr) (auto simp: steps_def)

lemma steps_Cons_case:
  "steps (Some (prev, th, st) # tr) = 
   (case prev of None => steps tr | Some step => step # (steps tr))"
  by (induct tr) (auto simp: steps_def split: option.splits)

lemma steps_append [simp]: 
  "steps (tr@tr') = steps tr @ steps tr'"
  by (induct tr) (auto simp: steps_def split: option.splits)


sublocale script_derivation \<subseteq> script_dy P tr "knows D"
  using derivable 
  apply unfold_locales 
  by (auto intro!: derivs_imp_dy 
             simp: dy_proto2nts_conv_dy_script[symmetric])

lemma (in script_dy) prev_in_done:
  "Some (Some s, th, st) \<in> set tr \<Longrightarrow>
   \<exists> done todo. th (fst s) = Some (done, todo) \<and> snd s \<in> set done"
  by (induct rule: script_dy_induct) auto


lemma (in script_dy) distinct_steps:
  "distinct (steps tr)"
proof(induct rule: script_dy_induct)
  case (send tr prev th st M i "done" l pt todo)
  then interpret this: script_dy P "tr@[Some (prev, th, st)]" M
    by unfold_locales auto
  show ?case
  proof(cases prev)
    case (Some s)
    thus ?thesis using send (* this.prev_in_done[of "s" th st] *)
      apply clarsimp
      sorry
  next
    case None thus ?thesis using send
      sorry
  qed
next
  case recv thus ?case sorry
qed auto

thm set_conv_nth

lemma steps_nth:
  "\<lbrakk> tr ! i  = Some (Some s, th,  st );
     i < length tr
   \<rbrakk> \<Longrightarrow>
   \<exists> j. steps tr ! j = s \<and> j < length (steps tr)"
apply(induct tr rule: rev_induct)
apply(auto)
apply(simp add: nth_append)
apply(simp split: if_splits)
apply(

lemma steplist_nth_conv
nth_eq_iff_index_eq

definition (in script_derivation) scriptOrd 
where "scriptOrd = 
         { (s, s') 
         | i s th st i' s' th' st'. 
            (State i, State i') \<in> derivOrd \<and> 
             tr!i  = Some (Some s,  th,  st ) \<and> 
             tr!i' = Some (Some s', th', st')
         }"

lemma (in script_derivation) unique_steps:
  "\<lbrakk> tr ! i  = Some (Some s, th,  st ); 
     tr ! i' = Some (Some s, th', st');
     i  < length tr;
     i' < length tr
   \<rbrakk> \<Longrightarrow> i' = i"
sorry


lemma (in derivation) State2_derivOrd_index_in_trace:
  "(x, State i) \<in> derivOrd \<Longrightarrow> i < length tr"
  unfolding derivOrd_def
  apply(drule RangeI)
  by (auto dest!: State2_index_in_trace simp: Range_Un_eq) 

lemma (in derivation) State1_derivOrd_index_in_trace:
  "(State i, y) \<in> derivOrd \<Longrightarrow> i < length tr"
  unfolding derivOrd_def
  apply(drule DomainI)
  by (auto dest!: State1_index_in_trace)

lemma (in script_derivation) sriptOrd_trans:
  "\<lbrakk> (x,y) \<in> scriptOrd; (y,z) \<in> scriptOrd \<rbrakk> 
   \<Longrightarrow> (x,z) \<in> scriptOrd"
  unfolding scriptOrd_def
  apply(clarsimp)
  apply(drule unique_steps, assumption)
  apply(auto elim!: State1_derivOrd_index_in_trace 
                    State2_derivOrd_index_in_trace)
  apply(drule derivOrd_trans, force+)
  done

lemma (in script_derivation) sriptOrd_irrefl:
  "(x,x) \<notin> scriptOrd"
  unfolding scriptOrd_def
  apply(clarsimp)
  apply(drule unique_steps, assumption)
  apply(auto elim!: State1_derivOrd_index_in_trace 
                    State2_derivOrd_index_in_trace
              simp: derivOrd_irr)
  done

lemma listOrdD:
  "listOrd xs a b \<Longrightarrow>
   \<exists> as bs. xs = as @ bs \<and> a \<in> set as \<and> b \<in> set bs"
  apply(induct xs a b rule: listOrd.induct, auto)
  apply(rule_tac x="[x]" in exI, force)
  apply(rule_tac x="x#as" in exI, force)
  done

lemma listOrdI:
  "\<lbrakk> xs = as @ bs; a \<in> set as; b \<in> set bs \<rbrakk> \<Longrightarrow>
   listOrd xs a b"
  by (induct as, auto)

lemma listOrd_conv:
  "listOrd xs a b =
   (\<exists> as bs. xs = as @ bs \<and> a \<in> set as \<and> b \<in> set bs)"
  by (auto intro!: listOrdD listOrdI)

lemma listOrd_nth_conv:
  assumes xs: "distinct xs"
  and      i: "i < length xs"
  and      j: "j < length xs"
  shows "listOrd xs (xs!i) (xs!j) = (i < j)"
proof -
  { assume "listOrd xs (xs!i) (xs!j)"
    hence  "i < j" using i j xs
      apply(clarsimp simp: listOrd_conv)
      apply(auto simp: nth_append split: if_splits)
      apply(force simp: set_conv_nth)
      done
  } moreover
  { have "\<exists> as bs. xs = as @ bs \<and> length as = Suc i"
      using i
      proof(induct xs rule: rev_induct)
        case (snoc x xs) show ?case
        proof(cases "i = length xs")
          case True thus ?thesis using snoc
            apply(rule_tac x="xs@[x]" in exI)
            by auto
        next
          case False thus ?thesis using snoc
            apply(clarsimp)
            apply(rule_tac x="as" in exI)
            by auto
        qed
      qed auto
    then obtain as bs where "xs = as @ bs" "length as = Suc i"
      by auto
    moreover assume "i < j"   
    ultimately have "listOrd xs (xs ! i) (xs ! j)"
      using i j xs
      by (auto simp: nth_append split: if_splits)
  } ultimately
  show ?thesis by blast
qed




locale script_dy_state = script_dy +
  assumes reachable: "\<exists> prev. last tr = Some (prev, th, st)"


  
sublocale script_dy_state \<subseteq> dy_state "proto2nts P" tr M
  using in_dy_script
  by unfold_locales (auto simp:dy_proto2nts_conv_dy_script) 




text{* An extension of the script dy state locale denoting
       an individual thread and its state. *}

locale script_dy_thread = script_dy_state +
  fixes i      :: "tid"
    and "done" :: "rolestep list"
    and todo   :: "rolestep list"
  assumes thread_exists: "th i = Some (done, todo)"

text{* The thread state is built such that @{term "done @ todo"} is
       always a role of @{term P}. *}

lemma (in script_dy_thread) role_in_P:
  "done @ todo \<in> P"
  using thread_exists reachable
  by (induct arbitrary: th i "done" todo rule: dy_script_induct)
     (clarsimp, (fastsimp split: if_splits)?)+

text{* Importing all lemmas of the wellformed role locale for
the term @{term "done @ todo"}. *}
sublocale script_dy_thread \<subseteq> wf_role "done @ todo"
  by (rule wf_roles[OF role_in_P])


subsection{* Basic Properties *}

(* building the derivation order referring to steps instead of
   indices
*)




   


lemma 
(* older steplist construction *)



(*

lemma stepsI: "Step estep \<in> set t \<Longrightarrow> estep \<in> steps t"
  by(induct t rule: steps.induct, auto)

lemma stepsD: "estep \<in> steps t \<Longrightarrow> Step estep \<in> set t"
  by(induct t rule: steps.induct, auto)

lemma Step_in_set_conv [simp]: 
  "(Step estep \<in> set t) = (estep \<in> steps t)"
  by(auto intro!: stepsI stepsD)
*)
subsection{* Thread Execution *}

lemma (in script_dy_thread) step_in_dom: 
  "(i, step) \<in> steps t \<Longrightarrow> i \<in> dom th"
using thread_exists reachable
by (induct rule: dy_script_induct) auto


lemma script_IK0_phase:
  "\<lbrakk> (tr, M) \<in> dy_script P; last tr = None \<rbrakk> \<Longrightarrow> set tr = {None}"
  by (induct rule: dy_script.induct) auto

context script_dy_thread
begin

lemma in_dom_r: "i \<in> dom th" 
  by (auto intro!: thread_exists)

lemma distinct_done [iff]: "distinct done"
using distinct by auto

lemma distinct_todo [iff]: "distinct todo"
using distinct by auto

lemma in_steps_eq_in_done:
  "((i, step) \<in> steps tr) = (step \<in> set done)"
using reachable thread_exists
proof(induct arbitrary: th st i "done" todo rule: dy_script_induct)
  case init_proto thus ?case
    by (fastsimp dest: script_IK0_phase simp: steps_def)
next
  case (send tr prev th st M i "done" l pt todo th' st' i' done' todo')
  thus ?case 
  proof(cases "i = i'")
    case False thus ?thesis using send
      by (clarsimp simp: steps_def)
  next
    case True thus ?thesis using send
      apply(clarsimp)
      apply(cases prev)
      apply(fastsimp)+
      done
  qed
next
  case (recv tr prev th st M i pt "done" l todo th' st' i' done' todo')
  thus ?case 
  proof(cases "i = i'")
    case False thus ?thesis using recv
      by (clarsimp simp: steps_def)
  next
    case True thus ?thesis using recv
      apply(clarsimp)
      apply(cases prev)
      apply(fastsimp)+
      done
  qed
qed auto

lemmas steps_in_done [elim!] = iffD1[OF in_steps_eq_in_done, rule_format]
lemmas done_in_steps [elim!] = iffD2[OF in_steps_eq_in_done, rule_format]

lemma todo_notin_stepsD:
  "step \<in> set todo \<Longrightarrow> (i, step) \<notin> steps tr"
using distinct by(auto dest!: steps_in_done)

lemmas todo_notin_stepsE = notE[OF todo_notin_stepsD, rule_format]

lemma listOrd_done_imp_listOrd_trace: 
  "listOrd done prev step \<Longrightarrow> 
   listOrd (steplist tr) (i, prev) (i, step)"
using thread_exists reachable
proof(induct arbitrary: th st i "done" todo rule: dy_script_induct)
  case (send tr prev' th st M i "done" l pt todo th' st' i' done' todo')
  then interpret this_thread: 
    script_dy_thread P "tr @ [Some (prev', th, st)]" M 
                     th st i "done" "Send l pt # todo"
    by unfold_locales auto
  show ?case
  proof(cases "i = i'")
    case False thus ?thesis using send
      by (clarsimp split: if_splits, cases prev', fastsimp+)
  next
    case True thus ?thesis using send this_thread.done_in_steps
      apply(clarsimp)
      apply(cases prev')
      apply(fastsimp)
      apply(clarsimp)
      apply(fastsimp)
      done
  qed
next
  case (recv tr prev' th st M i pt "done" l todo th' st' i' done' todo')
  then interpret this_thread: 
    script_dy_thread P "tr @ [Some (prev', th, st)]" M 
                     th st i "done" "Recv l pt # todo"
    by unfold_locales auto
  show ?case
  proof(cases "i = i'")
    case False thus ?thesis using recv
      by (clarsimp split: if_splits, cases prev', fastsimp+)
  next
    case True thus ?thesis using recv this_thread.done_in_steps
      apply(clarsimp)
      apply(cases prev')
      apply(fastsimp)
      apply(clarsimp)
      apply(fastsimp)
      done
  qed
next
  case init_proto thus ?case by fastsimp
qed auto

lemma listOrd_role_imp_listOrd_trace:
  "\<lbrakk> (i, step) \<in> steps tr; listOrd (done @ todo) prev step \<rbrakk>
  \<Longrightarrow> listOrd (steplist tr) (i, prev) (i, step)"
using distinct
by (fastsimp dest: in_set_listOrd2 listOrd_done_imp_listOrd_trace)

end


subsection{* Variable Substitutions *}

(*
context script_dy_thread
begin

lemma inst_AVar_cases: 
  "st (AVar v, i) \<in> Uncompromised \<or> st (AVar v, i) \<in> Compromised"
  apply (induct rule: dy_script_induct) 
  apply(auto)
  apply(fastsimp+)

lemma inst_AVar_in_IK0: 
 "s (AVar v, i) \<in> IK0"
using inst_AVar_cases[of v i] 
by (auto simp: IK0_def Uncompromised_def Compromised_def)

lemma inst_AVar_in_knows [iff]:
  "s (AVar a, i) \<in> knows t"
  by (rule knows_IK0[OF inst_AVar_in_IK0])

end (* reachable_state *)
*)

(* TODO: Move *)
lemma MVar_in_FV_conv_FMV [iff]:
  "(MVar v \<in> FV pt) = (v \<in> FMV pt)"
  by(induct pt, auto, case_tac varid, auto)


lemma (in script_dy_thread) send_step_FV:
  assumes send_step: "todo = Send l msg # todo'"
  and FV: "n \<in> FMV msg"
  shows "\<exists> l' msg'. (i, Recv l' msg') \<in> steps tr \<and>  MVar n \<in> FV msg'"
proof -
  let ?role = "done @ todo"
  have "Send l msg \<in> set ?role" using send_step by simp
  then obtain l' msg' 
    where "listOrd ?role (Recv l' msg') (Send l msg)"
    and "MVar n \<in> FV msg'"
    by (fast intro!: FV dest!: Send_FV)
  thus ?thesis using distinct send_step
    by (auto dest: in_set_listOrd1 in_set_listOrd2)+
qed

end

(* OLD STUFF *)

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