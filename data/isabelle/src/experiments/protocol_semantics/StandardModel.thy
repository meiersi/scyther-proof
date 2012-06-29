theory StandardModel
imports
  Protocol
  ExecMessage
  Subst
begin


section{* Operational Semantics *}

types execstep = "i \<times> rolestep"

types trace = "execstep list"

fun spies :: "subst \<Rightarrow> trace \<Rightarrow> execmsg set" 
where
  "spies s [] = IK0"
| "spies s ((i, Send l pt) # es) = 
     insert (inst s i pt) (spies s es)"
| "spies s ((i, Recv l pt) # es) = spies s es"

types threadpool = "i \<rightharpoonup> (rolestep list \<times> rolestep list)"

types state = "trace \<times> threadpool \<times> subst"


inductive_set 
  ossp :: "proto \<Rightarrow> state set" 
  for P     :: "proto"
where
  init:  "\<lbrakk> \<forall> i done todo. r i = Some (done,todo) \<longrightarrow> 
                             done = [] \<and> todo \<in> P;
            domS s = {EVar (AVar a) i | a i. True};
            ranS s \<subseteq> {Lit (EHonest a) | a. True} \<union> {Lit (Eve a) | a. True}
          \<rbrakk>
          \<Longrightarrow> ([], r, s) \<in> ossp P"

| send:  "\<lbrakk> (t, r, s) \<in> ossp P;
            r i = Some (done, Send l pt # todo)
          \<rbrakk>
          \<Longrightarrow> ( t @ [(i, Send l pt)], 
                r(i \<mapsto> (done@[Send l pt], todo)), s) \<in> ossp P"
            
| recv:  "\<lbrakk> (t, r, s) \<in> ossp P;
            r i = Some (done, Recv l pt # todo);
            domS \<alpha> = { EVar v i | v. v \<in> FV pt };
            inst (extendS s \<alpha>) i pt \<in> infer (spies s t)
          \<rbrakk>
          \<Longrightarrow> (t @ [(i, Recv l pt)], 
               r(i \<mapsto> (done@[Recv l pt], todo)), extendS s \<alpha>) \<in> ossp P"

locale ossp_state = wf_proto+
  fixes t :: trace
  and r :: threadpool
  and s :: subst
  assumes ossp: "(t,r,s) \<in> ossp P"


subsubsection{* Properties *}

lemma spies_conv_set: 
  "spies s t = IK0 \<union> { inst s i pt
                     | i l pt. (i, Send l pt) \<in> set t }"
  by (induct t rule: spies.induct) auto

lemma in_IK0_in_spies [simp,intro]: "m \<in> IK0 \<Longrightarrow> m \<in> spies s t"
  by (simp add: spies_conv_set)

lemma spies_append [simp]: 
  "spies s (t@t') = spies s t \<union> spies s t'"
  by (auto simp: spies_conv_set)

lemma spies_Un_IK0_conv_spies [simp]: 
  "spies s t \<union> IK0 = spies s t"
  "IK0 \<union> spies s t = spies s t"
  by(auto)


section{* Security Properties *}

definition runs :: "threadpool \<Rightarrow> i \<Rightarrow> role \<Rightarrow> bool"
where "runs r i R \<equiv> case r i of 
                        Some (done, todo) \<Rightarrow> R = done@todo
                      | None \<Rightarrow> False"

(* TODO: adapt names: knows \<rightarrow> learnt, kntrace \<rightarrow> ?, \<dots>*)
definition known :: "subst \<Rightarrow> trace \<Rightarrow> execmsg set"
where "known s t \<equiv> infer (spies s t)"

types honesty_asms = "id set"

definition secret :: "proto \<Rightarrow> role \<Rightarrow> rolestep \<Rightarrow> honesty_asms \<Rightarrow> pattern  \<Rightarrow> bool"
where 
  "secret P R step H pt \<equiv> \<forall> (t,r,s) \<in> ossp P. \<forall> i.
     ( runs r i R \<and> (i,step) \<in> set t \<and> 
       (\<forall> a \<in> H. Rep_subst s (EVar (AVar a) i) \<notin> Compromised)
     ) \<longrightarrow>
     ( inst s i pt \<notin> known s t )"
     

subsection{* Parts from other theories to be ported  *}

subsection{* Relation to Operational Semantics *}

(* TODO: Port to substitution-less explicit model 

subsubsection{* From Explicit Traces to Implicit Traces *}

fun execsteps :: "explicit_trace \<Rightarrow> trace"
where
  "execsteps []               = []"
| "execsteps (Step estep # t) =  estep # execsteps t"
| "execsteps (_ # t)          =          execsteps t"

lemma execsteps_append [simp]: 
  "execsteps (t@t') = execsteps t @ execsteps t'"
  by(induct t rule: execsteps.induct, auto)

lemma set_execsteps_conv_set [simp]:
  "set (execsteps t) = 
   { (i,step) | i step. (i, step) \<in> steps t}"
  by(induct t rule: execsteps.induct, auto)


context reachable_state begin

lemma spies_execsteps_extendS [simp]:
  "spies (extendS s \<alpha>) (execsteps t) = 
   spies s (execsteps t)"
  apply(auto simp: spies_conv_set)
  apply(force dest: steps_ground)+
  done

(* MOVE *)
lemmas infer_monoD = rev_subsetD[OF _ infer_mono]

lemma knows_spies_execsteps:
  "m \<in> knows t \<Longrightarrow> m \<in> infer (spies s (execsteps t))"
proof(induct arbitrary: m rule: reachable_induct)
  case init thus ?case by simp
next
  case (send t r s i "done" l msg todo m' m) thus ?case
    by(fastsimp elim!: infer_monoD pairParts_in_infer)
next
  case (recv t r s i "done" l msg todo \<alpha> m)
  then interpret this_state: reachable_state P t r s by unfold_locales
  show ?case using recv
    by(simp add: this_state.spies_execsteps_extendS)
next
  case hash thus ?case by(fastsimp intro: infer.Hash)
next
  case encr thus ?case by(fastsimp intro: infer.Enc)
next
  case decr thus ?case
    by(simp, blast intro: pairParts_in_infer[OF _ infer.Dec])
next
  case tuple thus ?case by fastsimp
qed

lemma in_ossp:
  "(execsteps t, r, s) \<in> ossp P"
proof (induct rule: reachable_induct)
  case init thus ?case by (simp add: ossp.init)
next
  case (send t r s i "done" l msg todo m) thus ?case
    by(fastsimp simp del: Fun.fun_upd_apply 
                  intro!: ossp.send)
next
  case (recv t r s i "done" l msg todo \<alpha>)
  then interpret this_state: reachable_state P t r s by unfold_locales
  show ?case using recv
    by(fastsimp simp del: Fun.fun_upd_apply 
                  intro!: ossp.recv
                          this_state.knows_spies_execsteps)
qed auto

end


subsubsection{* Implicit to Explicit Traces *}


context reachable_state
begin

lemma infer_known_subset_in_knows:
  assumes m: "m \<in> infer M" 
  and M: "M \<subseteq> knows t"
  shows "\<exists> t'. (t@t',r,s) \<in> reachable P \<and> execsteps t' = [] \<and> 
            m \<in> knows (t@t') \<and> (\<forall> x \<in> M. x \<notin> knows t')"
  (is "\<exists> t'. ?extension t t' m")
using m M reachable
proof(induct arbitrary: t rule: infer.induct)
  case (Inj m t)
  hence "?extension t [] m" by auto
  thus ?case by fast
next
  case (Fst x y t) then
  obtain t' where ext: "?extension t t' \<lbrace>x, y\<rbrace>" by fastsimp
  then interpret ext_state: reachable_state P "t@t'" r s 
    by unfold_locales auto
  from ext have "?extension t t' x"
    by (fastsimp simp del: knows_append 
                    intro: ext_state.knows_pairParts_closedD)
  thus ?case by fast
next
  case (Snd x y t) then
  obtain t' where ext: "?extension t t' \<lbrace>x, y\<rbrace>" by fastsimp
  then interpret ext_state: reachable_state P "t@t'" r s 
    by unfold_locales auto
  from ext have "?extension t t' y"
    by (fastsimp simp del: knows_append 
                    intro: ext_state.knows_pairParts_closedD)
  thus ?case by fast
next
  case (Hash m t) then
  obtain t' where ext: "?extension t t' m" by fastsimp
  then interpret ext_state: reachable_state P "t@t'" r s 
    by unfold_locales auto
  show ?case
  proof(cases "Hash m \<in> knows (t@t')")
    case True thus ?thesis using ext by auto
  next
    case False
    hence "((t@t')@[Learns {Hash m}], r, s) \<in> reachable P"
      using ext
      by(fastsimp intro!: reachable.hash simp del: append_assoc)
    thus ?thesis using ext and `M \<subseteq> knows t` and False
      by(fastsimp)
  qed
next
  case (Tup x y t)
  then obtain t' where ext1: "?extension t t' x" by fastsimp
  hence "\<exists> t''. ?extension (t@t') t'' y" using Tup
    apply-
    apply(rule prems)
    apply(auto)
    done
  then obtain t'' where ext2: "?extension t (t'@t'') y" 
    using ext1 by auto
  then interpret ext_state: reachable_state P "t@t'@t''" r s 
    by unfold_locales auto
  show ?case
  proof(cases "Tup x y \<in> knows (t@t'@t'')")
    case True thus ?thesis using ext2 by auto
  next
    case False
    hence "((t@t'@t'')@[Learns {Tup x y}], r, s) \<in> reachable P"
      using ext1 and ext2
      by(fastsimp intro!: reachable.tuple simp del: append_assoc)
    thus ?thesis using ext1 ext2 `M \<subseteq> knows t` and False
      by(fastsimp)
  qed
next
  case (Enc m k t)
  then obtain t' where ext1: "?extension t t' m" by fastsimp
  hence "\<exists> t''. ?extension (t@t') t'' k" using Enc
    apply-
    apply(rule prems)
    apply(auto)
    done
  then obtain t'' where ext2: "?extension t (t'@t'') k" 
    using ext1 by auto
  then interpret ext_state: reachable_state P "t@t'@t''" r s 
    by unfold_locales auto
  show ?case
  proof(cases "Enc m k \<in> knows (t@t'@t'')")
    case True thus ?thesis using ext2 by auto
  next
    case False
    hence "((t@t'@t'')@[Learns {Enc m k}], r, s) \<in> reachable P"
      using ext1 and ext2
      by(fastsimp intro!: reachable.encr simp del: append_assoc)
    thus ?thesis using ext1 ext2 `M \<subseteq> knows t` and False
      by(fastsimp)
  qed
next
  case (Dec m k t)
  then obtain t' where ext1: "?extension t t' (Enc m k)" by fastsimp
  hence "\<exists> t''. ?extension (t@t') t'' (inv k)" using Dec
    apply-
    apply(rule prems)
    apply(auto)
    done
  then obtain t'' where ext2: "?extension t (t'@t'') (inv k)" 
    using ext1 by auto
  then interpret ext_state: reachable_state P "t@t'@t''" r s 
    by unfold_locales auto
  show ?case
  proof(cases "m \<in> knows (t@t'@t'')")
    case True thus ?thesis using ext2 by auto
  next
    case False
    hence "((t@t'@t'')@[Learns (pairParts m - knows (t@t'@t''))], r, s) 
           \<in> reachable P"
      using ext1 and ext2
      by(fastsimp intro!: reachable.decr simp del: append_assoc)
    thus ?thesis using ext1 ext2 `M \<subseteq> knows t` and False
      by(fastsimp)
  qed
qed

lemma  in_spies_imp_in_knows:
  "m \<in> spies s (execsteps t) \<Longrightarrow> m \<in> knows t"
proof(induct rule: reachable_induct)
  case (recv t r s i "done" l msg todo \<alpha>)
  then interpret this_state: reachable_state P t r s by unfold_locales
  show ?case using recv
    by(simp add: this_state.spies_execsteps_extendS)
qed auto

lemma in_infer_spies_imp_in_ext_knows:
  assumes "m \<in> infer (spies s (execsteps t))"
  shows "\<exists> t'. execsteps t' = [] \<and> (t@t',r,s) \<in> reachable P \<and> 
               m \<in> knows (t@t')"
proof -
  from `m \<in> infer (spies s (execsteps t))`
  obtain M 
    where "finite M" 
    and "m \<in> infer M" 
    and "M \<subseteq> spies s (execsteps t)"
    by (blast dest: infer_finite_support)
  hence "M \<subseteq> knows t" 
    by (fast intro!: in_spies_imp_in_knows)
  with `m \<in> infer M`
  obtain t' where "(t @ t', r, s) \<in> reachable P" 
    and "execsteps t' = []"
    and "m \<in> knows (t @ t')"
    by (fast dest!: infer_known_subset_in_knows)
  thus ?thesis by fast
qed

lemma refine_attack_raw:
  assumes subset: "M \<subseteq> infer (spies s (execsteps t))"
  and finite: "finite M"
  shows "\<exists> t'. execsteps t' = [] \<and> (t@t',r,s) \<in> reachable P \<and> 
               M \<subseteq> knows (t@t')"
  (is "\<exists> t'. ?extension M t'")
using finite subset
proof(induct rule: finite.induct)
  case emptyI
  have "execsteps [] = []" by simp
  thus ?case by fastsimp
next
  case (insertI M m)
  then obtain t' where ext1: "?extension M t'" by auto
  moreover
  then interpret s1: reachable_state P "t@t'" r s
    by unfold_locales auto
  have infer_m: "m \<in> infer (spies s (execsteps (t@t')))"
    using insertI ext1 by fastsimp
  then obtain t'' 
    where "execsteps t'' = []" 
      "(t@(t'@t''),r,s) \<in> reachable P"
      "m \<in> knows (t@t'@t'')"
    using ext1 s1.in_infer_spies_imp_in_ext_knows[OF infer_m]
    by(auto)
  ultimately show ?case 
    apply-
    apply(rule_tac x="t'@t''" in exI)
    by(auto)
qed

end


context ossp_state
begin 

(* TODO: move *)
lemmas ossp_induct = 
  ossp.induct[OF ossp, consumes 0, case_names init send recv]

lemma in_reachable:
  "\<exists> t'. t = execsteps t' \<and> (t',r,s) \<in> reachable P"
  (is "\<exists> t'. ?witness t r s t'")
proof(induct rule: ossp_induct)
  case (init r s)
  hence "?witness [] r s [Learns IK0]"
    by(fastsimp intro!: reachable.init)
  thus ?case by fast
next
  case (send t r s i "done" l pt todo) then
  obtain t' where "?witness t r s t'" by fast
  hence "?witness (t @ [(i, Send l pt)]) 
                  (r(i \<mapsto> (done @ [Send l pt], todo))) 
                  s 
    (t'@[Step (i, Send l pt), 
         Learns (pairParts (inst s i pt) - knows t')])"
    using send
    by(fastsimp intro!: reachable.send)
  thus ?case by fast
next
  case (recv t r s i "done" l pt todo \<alpha>)
  then obtain t' where "?witness t r s t'" by fast
  hence "t = execsteps t'" and "(t', r, s) \<in> reachable P" by auto
  then interpret s1: reachable_state P t' r s by unfold_locales auto
  let ?m = "inst (extendS s \<alpha>) i pt"
  from `?m \<in> infer (spies s t)` and `t = execsteps t'`
  obtain t'' where "(t' @ t'', r, s) \<in> reachable P" 
    and "execsteps t'' = []"
    and "?m \<in> knows (t' @ t'')"
    by (fastsimp dest!: s1.in_infer_spies_imp_in_ext_knows)
  hence "?witness (t @ [(i, Recv l pt)]) 
                  (r(i \<mapsto> (done @ [Recv l pt], todo))) 
                  (extendS s \<alpha>)
                  ((t'@t'')@[Step (i, Recv l pt)])"
    using `t = execsteps t'` and recv
    by(fastsimp intro!: reachable.recv)
  thus ?case by fast
qed

end


lemma (in wf_proto) ossp_conv_reachable:
  "ossp P = {(execsteps t,r,s) | t r s. (t,r,s) \<in> reachable P}"
proof -
  { fix t r s
    assume "(t,r,s) \<in> ossp P"
    then interpret s1: ossp_state P t r s by unfold_locales
    note this = s1.in_reachable
  }
  moreover
  { fix t r s
    assume "(t,r,s) \<in> reachable P"
    then interpret s2: reachable_state P t r s by unfold_locales
    note this = s2.in_ossp
  }
  ultimately
  show ?thesis by fast
qed

*)



subsection{* Reduction Rules for Security Properties *}

(* TODO: Port to substitition-less explicit model 

lemma runs_conv_roleMap [iff]:
  "runs r i R = (roleMap r i = Some R)"
by(auto simp: runs_def roleMap_def split: option.splits)

lemma (in reachable_state) in_known_kntrace_imp_in_ext_knows:
  assumes known: "m \<in> known s (execsteps t)"
  shows "\<exists> t'. execsteps t' = [] \<and> (t@t',r,s) \<in> reachable P \<and> 
                m \<in> knows (t@t')"
using known unfolding known_def 
by (rule in_infer_spies_imp_in_ext_knows) 

lemma (in ossp_state) known_in_ext_knows: 
  assumes "m \<in> known s t"
  shows "\<exists> t'. t = execsteps t' \<and> (t',r,s) \<in> reachable P \<and> 
                m \<in> knows t'"
proof -
  from in_reachable
  obtain t' where "t = execsteps t'" and "(t',r,s) \<in> reachable P"
    by fast
  moreover
  then interpret s1: reachable_state P t' r s 
    by unfold_locales auto
  from `m \<in> known s t` and `t = execsteps t'`
  obtain t'' 
    where "execsteps t'' = []" 
    and "(t'@t'',r,s) \<in> reachable P"
    and "m \<in> knows (t'@t'')"
    by (fast dest!: s1.in_known_kntrace_imp_in_ext_knows)
  moreover
  with `t = execsteps t'`
  have "t = execsteps (t'@t'')" by simp
  ultimately
  show ?thesis by fast
qed

lemma (in wf_proto) secretI:
  assumes reachable_secrecy:
    "\<And> t r s i. 
     \<lbrakk> (t, r, s) \<in> reachable P; roleMap r i = Some R; 
       \<forall> a \<in> H. Rep_subst s (EVar (AVar a) i) \<notin> Compromised;
       (i, step) \<in> steps t;
       inst s i msg \<in> knows t
     \<rbrakk> \<Longrightarrow> False "
  shows "secret P R step H msg"
proof -
  { fix t r s i
    assume asms: 
      "(t, r, s) \<in> ossp P" 
      "runs r i R"
      "\<forall> a \<in> H. Rep_subst s (EVar (AVar a) i) \<notin> Compromised"
      "(i,step) \<in> set t"
      "inst s i msg \<in> known s t" (is "?m \<in> known s t")
    moreover
    then interpret s1: ossp_state P t r s by unfold_locales
    obtain t' 
      where "(t', r, s) \<in> reachable P" 
      and "t = execsteps t'"
      and "?m \<in> knows t'"
      using asms by (fast dest!: s1.known_in_ext_knows)
    ultimately
    have "False" 
      by (fastsimp dest!: reachable_secrecy)
  }
  thus ?thesis by (fastsimp simp: secret_def)
qed

lemma listOrd_kntrace_conv_predOrd [iff]:
  "listOrd (execsteps t) (i,step) (i',step') =
   predOrd t (St (i, step)) (St (i', step'))"
by (induct t rule: execsteps.induct) auto

*)


end