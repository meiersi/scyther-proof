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
theory WeakTyping
imports
  InferenceRules
  Syntax
begin

section{* A Shallow Embedding of a Message Type System *}

subsection{* Introduction *}

text{*
  The goal of this theory is to develop a simple way for specifying
  type invariants for the message variables of a protocol. A message
  type is a set of messages that depends on the thread and the 
  system state that this message type is interpreted relative to.
  
  A typing is then a function assigning to each combination of a
  role and an identifier of a message variable in this role a 
  message type. 

  Each typing approximates the set of states where all instantiated
  message variables are instantiated with a message corresponding 
  to their type.
*}

type_synonym msgtype = "tid \<Rightarrow> state \<Rightarrow> execmsg set"

type_synonym typing = "(role \<times> id) \<Rightarrow> msgtype"

definition approx :: "typing \<Rightarrow> state set"
where "approx typing \<equiv> {q. case q of (t,r,s) \<Rightarrow>
  \<forall> (i,step) \<in> steps t. 
    \<forall> R. roleMap r i = Some R \<longrightarrow>
      (\<forall> n. MVar n \<in> FV_rolestep step \<longrightarrow>
         s (MVar n, i) \<in> typing (R, n) i (t,r,s)
      )}"

locale typed_state = reachable_state+
  fixes typing :: "typing"
  assumes approximates: "(t,r,s) \<in> approx typing"

locale typed_thread = reachable_thread+
  fixes typing :: "typing"
  assumes approximates: "(t,r,s) \<in> approx typing"

sublocale typed_thread \<subseteq> typed_state
  using approximates by unfold_locales


lemma approx_unfold:
  "((t,r,s) \<in> approx typing) = 
   (\<forall> (i,step) \<in> steps t. 
      \<forall> R. roleMap r i = Some R \<longrightarrow>
        (\<forall> n. MVar n \<in> FV_rolestep step \<longrightarrow>
           s (MVar n, i) \<in> typing (R, n) i (t,r,s)))"
by (auto simp: approx_def)

lemma in_approxI:
  assumes all_vars:
    "\<And> i step R n.
     \<lbrakk> (i,step) \<in> steps t;
       roleMap r i = Some R;
       MVar n \<in> FV_rolestep step
     \<rbrakk>
       \<Longrightarrow> s (MV n i) \<in> typing (R, n) i (t,r,s)"
  shows "(t,r,s) \<in> approx typing"
by (auto simp: approx_unfold dest!: all_vars)

lemma in_approxD:
  assumes approx: "(t,r,s) \<in> approx typing"
  and asms: "(i,step) \<in> steps t"
            "roleMap r i = Some R"
            "MVar n \<in> FV_rolestep step"
  shows "s (MV n i) \<in> typing (R, n) i (t,r,s)"
using approx asms
by (auto simp: approx_unfold)


subsection{* A Combinator Language for Message Types *}

subsubsection{* Structural Types *}

text{*
  Structural message types specify the structure of a message.
  Their interpretation is independent of the thread that they
  are interpreted in. All of them except the type for nonces of
  a specific role are also independent of the state that they
  are interpreted in.
*}

definition ConstT :: "id \<Rightarrow> msgtype"
where "ConstT c i q \<equiv> { LC c }"

definition AgentT :: msgtype
where "AgentT i q \<equiv>  Agent"

declare AgentT_def [simp]

definition NonceT :: "role \<Rightarrow> id \<Rightarrow> msgtype"
where "NonceT R n i q  \<equiv> case q of 
         (t,r,s) \<Rightarrow> { LN n i' | i'. roleMap r i' = Some R }"

definition HashT :: "msgtype \<Rightarrow> msgtype"
where "HashT ty  i q \<equiv> { Hash m | m. m \<in> ty i q }"

definition TupT :: "msgtype \<Rightarrow> msgtype \<Rightarrow> msgtype"
where "TupT ty1 ty2 i q \<equiv> 
         { \<lbrace>x, y\<rbrace> | x y. x \<in> ty1 i q \<and> y \<in> ty2 i q }"

definition EncT :: "msgtype \<Rightarrow> msgtype \<Rightarrow> msgtype"
where "EncT tym tyk i q \<equiv> 
         { Enc m k | m k. m \<in> tym i q \<and> k \<in> tyk i q }"

definition PKT :: "msgtype \<Rightarrow> msgtype"
where "PKT ty  i q \<equiv> { PK m | m. m \<in> ty i q }"

definition SKT :: "msgtype \<Rightarrow> msgtype"
where "SKT ty  i q \<equiv> { SK m | m. m \<in> ty i q }"

definition KT :: "msgtype \<Rightarrow> msgtype \<Rightarrow> msgtype"
where "KT ty1 ty2 i q \<equiv> 
         { K m1 m2 | m1 m2. m1 \<in> ty1 i q \<and> m2 \<in> ty2 i q }"

definition KShrT :: "msgtype"
where "KShrT i q \<equiv> { KShr A | A. True }" 


text{* TODO: Make this syntax abbreviation work. *}
syntax
  "@TTuple"      :: "['a, args] => 'a * 'b"       ("(2{$_,/ _$})")

syntax (xsymbols)
  "@TTuple"      :: "['a, args] => 'a * 'b"       ("(2\<lbrace>$_,/ _$\<rbrace>)")

translations
  "{$x, y, z$}"   == "{$x, {$y, z$}$}" 
  "{$x, y$}"      == "WeakTyping.TupT x y"


subsubsection{* Special Types *}

text{* 
  The empty type denotes that a variable is never instantiated.
  The sum type denotes the union of two message types, while
  the intersection type denotes the intersection of the two 
  message types.
*}

definition EmptyT :: "msgtype"
where "EmptyT i q \<equiv> {}"

declare EmptyT_def [simp]

definition SumT :: "msgtype \<Rightarrow> msgtype \<Rightarrow> msgtype"
where "SumT ty1 ty2 i q \<equiv> ty1 i q \<union> ty2 i q"

definition InterT :: "msgtype \<Rightarrow> msgtype \<Rightarrow> msgtype"
where "InterT ty1 ty2 i q \<equiv> ty1 i q \<inter> ty2 i q"


text{*
  The known before a specific role step type captures the
  interaction of the intruder with the execution of a protocol.
  If the intruder fakes a message being received, then the
  variables are instantiated with messages known to the intruder
  \emph{before} the receive step was executed.
*}

definition KnownT :: "rolestep \<Rightarrow> msgtype"
where "KnownT step i q \<equiv> case q of  (t,r,s) \<Rightarrow> 
  { m | m. predOrd t (Ln m) (St (i,step)) }"


subsubsection{* Constructing Type Invariants *}

text{*
  The following function converts a list of type assignments to a
  typing. It will be used to specify the type invariants of specific
  protocols.
*}

definition mk_typing :: "((role \<times> id) \<times> msgtype) list \<Rightarrow> typing"
where "mk_typing tyeqs \<equiv> 
         foldr (\<lambda>(x, ty) typing. typing(x:=ty)) tyeqs (\<lambda>x. EmptyT)"


subsection{* Proving Well-Typedness *}

text{*
  A protocol is well-typed with respect to a typing iff
  all its reachable state are approximated by the typing.

  We specialize the induction scheme that we get from the definition
  of the set of reachable states to a ``type checking'' induction
  scheme. It works for message typings that are monotoneous with
  respect to state updates.
*}

definition monoTyp :: "typing \<Rightarrow> bool" 
where "monoTyp typ \<equiv> 
  (\<forall> x i t r s t' r'.
      roleMap r \<subseteq>\<^sub>m roleMap r' \<longrightarrow>
      typ x i (t,r,s) \<subseteq> typ x i (t@t',r',s)
  )"

lemma monoTypI:
  "\<lbrakk> \<And> x i t r s t' r' s' m. 
     \<lbrakk> roleMap r \<subseteq>\<^sub>m roleMap r'; m \<in> typ x i (t,r,s) \<rbrakk>
     \<Longrightarrow> m \<in> typ x i (t@t',r',s)
   \<rbrakk> \<Longrightarrow> monoTyp typ"
  by(auto simp: monoTyp_def)

lemma monoTypD:
  "\<lbrakk> monoTyp typ;
     m \<in> typ x i (t,r,s);
     roleMap r \<subseteq>\<^sub>m roleMap r'
   \<rbrakk> \<Longrightarrow>
   m \<in> typ x i (t@t',r',s)"
  unfolding monoTyp_def by blast

lemma monoTyp_freeD:
  "\<lbrakk> monoTyp typ;
     m \<in> typ x i (t,r,s);
     roleMap r \<subseteq>\<^sub>m roleMap r';
     t' = t@t''
   \<rbrakk> \<Longrightarrow>
   m \<in> typ x i (t',r',s)"
  unfolding monoTyp_def by blast

lemma monoTyp_appendD:
  "\<lbrakk> monoTyp typ;
     m \<in> typ x i (t,r,s)
   \<rbrakk> \<Longrightarrow>
   m \<in> typ x i (t@t',r,s)"
  by (rule monoTyp_freeD) auto


lemma (in reachable_thread) step_done_typing:
  assumes typ_rule:
    "\<And> step.
     \<lbrakk> (i, step) \<in> steps t;
       MVar v \<in> FV_rolestep step
     \<rbrakk> \<Longrightarrow> s (MV v i) \<in> typing (done @ todo, v) i (t, r, s)"
  and step_done: "step \<in> set done"
  and step_var: "MVar v \<in> FV_rolestep step"
  shows "s (MV v i) \<in> typing (done @ todo, v) i (t, r, s)"
proof (cases "step \<in> skipped")
  case False
  thus ?thesis using assms by auto
next
  case True
  note inSkipped = this
  then obtain l ty pt
    where noteEq: "(Note l ty pt) = step"
    by(auto dest!: note_in_skipped)
  hence "\<exists> step'. listOrd (done@todo) step' (Note l ty pt) \<and> v \<in> sourced_vars step'"
    using inSkipped step_done step_var
    apply -
    apply(subgoal_tac "v \<in> used_vars step")
      apply(subgoal_tac "Note l ty pt \<in> set (done@todo)")
        apply(drule source_use_ord)
    by auto
  then obtain step'
    where roleBefore: "listOrd (done@todo) step' (Note l ty pt)"
    and varSourced: "v \<in> sourced_vars step'"
    by auto
  have notNote: "\<not> noteStep step'" using varSourced by auto
  have "step' \<in> set done" 
    using roleBefore step_done noteEq
    apply -
    apply(drule listOrd_append[THEN iffD1])
    apply(case_tac "listOrd done step' (Note l ty pt)")
      apply(fastforce dest: in_set_listOrd1)
    apply(case_tac "listOrd todo step' (Note l ty pt)")
      apply(fastforce dest: in_set_listOrd2 done_notin_todoD)
    apply(case_tac "step' \<in> set done \<and> Note l ty pt \<in> set todo")
    by(auto dest: done_notin_todoD)
  hence "(i, step') \<in> steps t" using notNote by (cases step', auto)
  thus ?thesis
    using varSourced by (auto intro!: typ_rule thread_exists)
qed


lemma (in reachable_state) reachable_in_approxI:
  assumes monoTyp: "monoTyp typing"
  and source_case:
    "\<And> t r s i done todo skipped m R step n.
     \<lbrakk> R \<in> P; 
       roleMap r i = Some R;
       (done, step # todo) \<in> set (splits R);
       \<not> sendStep step; \<not> noteStep step;
       n \<in> sourced_vars step;
       \<forall> step' \<in> set done. MVar n \<notin> FV_rolestep step';
       hint ''completenessCase'' (step, n);
       
       (t,r,s) \<in> reachable P;
       (t,r,s) \<in> approx typing;
       r i = Some (done, step # todo, skipped);
       
       recvStep step \<Longrightarrow> Some m = inst s i (stepPat step) \<and> m \<in> knows t;
       matchEqStep step \<Longrightarrow> exec_match s i (matchVar step) (stepPat step)
     \<rbrakk> \<Longrightarrow> 
        s (MV n i) \<in> typing (R, n) i (t @ [Step (i, step)], r(i \<mapsto> (done @ [step], todo, skipped)), s)"
  shows "(t,r,s) \<in> approx typing"
proof -
  { fix i step "done" todo skipped n
    have
     "\<lbrakk> r i = Some (done, todo, skipped);
        (i,step) \<in> steps t;
        MVar n \<in> FV_rolestep step
      \<rbrakk> \<Longrightarrow> s (MV n i) \<in> typing (done@todo, n) i (t,r,s)"
    proof(induct arbitrary: i "done" todo step n skipped rule: reachable_induct)
      case (send t r s i "done" l pt todo skipped m i' done' todo' step n skipped')
      then interpret th1: 
        reachable_thread P t r s i "done" "Send l pt # todo" skipped
        by unfold_locales auto
      from send 
      have "(i', step) \<in> steps t \<or> (i' = i) \<and> step = Send l pt"
        (is "?old \<or> ?new") by auto
      moreover
      { assume ?old
        hence "s(MV n i') \<in> typing (done'@todo', n) i' (t,r,s)"
          using send by (auto split: if_splits)
        hence ?case
        proof(rule monoTyp_freeD[OF monoTyp])
        qed (auto simp: th1.thread_exists)
      }
      moreover
      { let ?role = "done @ Send l pt # todo"
        note IH = send(2)
        assume "?new"
        moreover hence "n \<in> used_vars step" using send by auto
        ultimately obtain step' 
          where "(i, step') \<in> steps t" 
                "n \<in> sourced_vars step'"   
          by (fastforce dest!: th1.source_step[OF th1.thread_exists])
        hence typed: "s (MV n i) \<in> typing (?role, n) i (t, r, s)"
          by (auto dest: IH[OF th1.thread_exists])
        have "done'@todo' = ?role"
          using send `?new` by auto
        hence ?case using `?new`
          apply -
          apply(rule monoTyp_freeD[OF monoTyp])
          by (auto intro!: typed simp: th1.thread_exists)
      }
      ultimately show ?case by fast
    next
      case (recv t r s i "done" l pt todo skipped m i' done' todo' step n skipped') then
      interpret th1: 
        reachable_thread P t r s i "done" "Recv l pt # todo" skipped
        by unfold_locales auto
      from recv
      have "(i', step) \<in> steps t \<or> (i' = i) \<and> step = Recv l pt"
        (is "?old \<or> ?new") by auto
      moreover
      { assume ?old
        hence "s(MV n i') \<in> typing (done'@todo', n) i' (t,r,s)"
          using recv by (auto split: if_splits)
        hence ?case using `?old`
          apply -
          apply(rule monoTyp_freeD[OF monoTyp])
          apply(auto simp: th1.thread_exists)
          done
      }
      moreover
      { let ?role = "done @ Recv l pt # todo"
        note IH = recv(2)
        assume "?new"
        hence cur_thread: "?role = done' @ todo'" "i = i'" 
          using recv by auto
        have ?case
        proof(cases "\<exists> step' \<in> set done. MVar n \<in> FV_rolestep step'")
          case True
          with recv
          obtain step'
            where FV: "MVar n \<in> FV_rolestep step'" 
            and step': "step' \<in> set done"
            by auto
          hence "s (MV n i) \<in> typing (done'@todo', n) i (t, r, s)"
            using th1.thread_exists cur_thread IH
            by (metis th1.step_done_typing)
          thus ?thesis using `?new`
            apply -
            apply(rule monoTyp_freeD[OF monoTyp])
            apply(auto simp: th1.thread_exists)
            done
        next
          case False
            moreover have "(t, r, s) \<in> approx typing"
              by (auto simp: approx_unfold dest!: IH roleMap_SomeD)
            moreover note `?new`
            moreover note `MVar n \<in> FV_rolestep step`
            moreover note `Some m = inst s i pt`
            moreover note `m \<in> knows t`
            moreover note cur_thread[symmetric]
          
            ultimately show ?thesis
              apply -
              apply(clarsimp simp del: fun_upd_apply)
              apply(rule source_case)
              apply(simp_all add: th1.role_in_P th1.roleMap th1.thread_exists 
                                  in_set_splits_conv remove_hints)
              apply(blast)
              done
         qed
      }
      ultimately show ?case by fastforce
    next
      case (compr t r s i "done" l ty pt todo skipped m i' done' todo' step n skipped')
      then interpret th1: 
        reachable_thread P t r s i "done" "Note l ty pt # todo" skipped
        by unfold_locales auto
      from compr
      have "(i', step) \<in> steps t \<or> (i' = i) \<and> step = Note l ty pt"
        (is "?old \<or> ?new") by auto
      moreover
      { assume ?old
        hence "s(MV n i') \<in> typing (done'@todo', n) i' (t,r,s)"
          using compr by (auto split: if_splits)
        hence ?case
        proof(rule monoTyp_freeD[OF monoTyp])
        qed (auto simp: th1.thread_exists)
      }
      moreover
      { let ?role = "done @ Note l ty pt # todo"
        note IH = compr(2)
        assume "?new"
        hence "n \<in> used_vars (Note l ty pt)"
          using compr by auto
        then obtain step' 
          where "(i, step') \<in> steps t" 
                "n \<in> sourced_vars step'"
          by (fastforce dest!: th1.source_step[OF th1.thread_exists])
        moreover hence "MVar n \<in> FV_rolestep step'" by auto
        ultimately have typed: "s (MV n i) \<in> typing (?role, n) i (t, r, s)"
          by (auto dest: IH[OF th1.thread_exists])
        have "done'@todo' = ?role"
          using compr `?new` by auto
        hence ?case using `?new`
          apply -
          apply(rule monoTyp_freeD[OF monoTyp])
          by (auto intro!: typed simp: th1.thread_exists)
      }
      ultimately show ?case by fast
    next
      case (skip t r s i "done" l ty pt todo skipped i' done' todo' step n skipped')
      then interpret th1: 
        reachable_thread P t r s i "done" "Note l ty pt # todo" skipped
        by unfold_locales auto
      from skip
      have "(i', step) \<in> steps t" (is "?old") by auto
      hence "s(MV n i') \<in> typing (done'@todo', n) i' (t,r,s)"
        using skip by (auto split: if_splits)
      thus ?case
      proof(rule monoTyp_freeD[OF monoTyp])
      qed (auto simp: th1.thread_exists)
    next
      case (match t r s i "done" l eq mv pt todo skipped i' done' todo' step n skipped') then
      interpret th1:
        reachable_thread P t r s i "done" "Match l eq mv pt # todo" skipped
        by unfold_locales auto
      from match
      have "(i', step) \<in> steps t \<or> (i' = i) \<and> step = Match l eq mv pt"
        (is "?old \<or> ?new") by auto
      moreover
      { assume ?old
        hence "s (MV n i') \<in> typing (done'@todo', n) i' (t,r,s)"
          using match by (auto split: if_splits)
        hence ?case
        proof (rule monoTyp_freeD[OF monoTyp])
        qed (auto simp: th1.thread_exists)
      }
      moreover
      { let ?role = "done @ Match l eq mv pt # todo"
        note IH = match(2)
        assume "?new"
        have ?case proof (cases eq)
          case True
          note eq_case = this
          hence cur_thread: "?role = done' @ todo'" "i = i'" and
                match_FV: "n \<in> used_vars step \<or> n \<in> sourced_vars step"
          using `?new` match by auto
          from match_FV show ?thesis proof
            assume "n \<in> used_vars step"
            with `?new` obtain step'
              where "(i, step') \<in> steps t"
                    "n \<in> sourced_vars step'"
              by (fastforce dest!: th1.source_step[OF th1.thread_exists])
            hence typed: "s (MV n i) \<in> typing (?role, n) i (t, r, s)"
              by (auto dest: IH[OF th1.thread_exists])
            thus ?thesis using `?new` cur_thread(1)
              apply -
              apply(rule monoTyp_freeD[OF monoTyp])
              by (auto intro!: typed simp: th1.thread_exists)
          next
            assume "n \<in> sourced_vars step"
            thus ?thesis
            proof (cases "\<exists> step' \<in> set done. MVar n \<in> FV_rolestep step'")
              case True
              with match
              obtain step'
                where FV: "MVar n \<in> FV_rolestep step'"
                and step': "step' \<in> set done"
                by auto
              hence "s (MV n i) \<in> typing (done'@todo', n) i (t, r, s)"
                using th1.thread_exists cur_thread IH
                by (metis th1.step_done_typing)
              thus ?thesis using `?new`
                apply -
                apply(rule monoTyp_freeD[OF monoTyp])
                apply(auto simp: th1.thread_exists)
                done
            next
              case False
                moreover have "(t, r, s) \<in> approx typing"
                  by (auto simp: approx_unfold dest!: IH roleMap_SomeD)
                moreover note `?new`
                moreover note `n \<in> sourced_vars step`
                moreover have "exec_match s i mv pt"
                  using match eq_case by simp
                moreover note cur_thread[symmetric]

                ultimately show ?thesis
                  apply -
                  apply(clarsimp simp del: fun_upd_apply)
                  apply(rule source_case)
                  apply(simp_all add: th1.role_in_P th1.roleMap th1.thread_exists
                                      in_set_splits_conv remove_hints)
                  done
            qed
          qed

        next
          case False note notMatch = this
          moreover note `?new`
          moreover hence "n \<in> used_vars step" using match notMatch by auto
          ultimately obtain step'
            where "(i, step') \<in> steps t" 
                  "n \<in> sourced_vars step'"   
            by (fastforce dest!: th1.source_step[OF th1.thread_exists])
          hence typed: "s (MV n i) \<in> typing (?role, n) i (t, r, s)"
            by (auto dest: IH[OF th1.thread_exists])
          have "done'@todo' = ?role" using match `?new` by auto
          thus ?thesis using `?new`
            apply -
            apply(rule monoTyp_freeD[OF monoTyp])
            by (auto intro!: typed simp: th1.thread_exists)
        qed
      }
      ultimately show ?case by fastforce

    qed (auto intro: monoTyp_appendD[OF monoTyp])
  }
  thus ?thesis unfolding approx_unfold by(auto elim!: roleMap_SomeE)
qed

text{*
  We prove a variant of the above lemma, which is suitable for
  automation. The difference is the description of the variables
  that need to be checked. Here, it is done such that Isabelle's
  simplifier gets a finite set that it can rewrite into normal
  form.
*}
lemma (in reachable_state) reachable_in_approxI_ext:
  assumes monoTyp: "monoTyp typing"
  and source_case:
    "\<And> t r s i done todo skipped m R step n.
     \<lbrakk> R \<in> P; 
       roleMap r i = Some R;
       (done, step # todo) \<in> set (splits R);
       \<not> sendStep step; \<not> noteStep step;
       n \<in> foldl (\<lambda> fv step'. fv - sourced_vars step') (sourced_vars step) done;
       hint ''completenessCase'' (step, n);
       
       (t,r,s) \<in> reachable P;
       (t,r,s) \<in> approx typing;
       r i = Some (done, step # todo, skipped);
       \<forall> st'. st' \<in> set done \<longrightarrow> \<not> noteStep st' \<longrightarrow> (i, st') \<in> steps t;

       recvStep step \<Longrightarrow> Some m = inst s i (stepPat step) \<and> m \<in> knows t;
       matchEqStep step \<Longrightarrow> exec_match s i (matchVar step) (stepPat step)
     \<rbrakk> \<Longrightarrow>
        s (MV n i) \<in> typing (R, n) i ( t @ [Step (i, step)], r(i \<mapsto> (done @ [step], todo, skipped)), s)"
  shows "(t,r,s) \<in> approx typing"
proof(induct rule: reachable_in_approxI[OF monoTyp])
  case (1 t r s i "done" todo skipped m R step n)
  { fix v V
    assume "v \<in> V"
      and "\<forall>step'\<in>set done. MVar v \<notin> FV_rolestep step'"
    hence "v \<in> foldl (\<lambda> fv step'. fv - sourced_vars step') V done"
      by (induct "done" arbitrary: V) (auto intro!: sourced_imp_FV)
  }
  hence "n \<in> foldl (\<lambda> fv step'. fv - sourced_vars step') (sourced_vars step) done"
    using 1 by auto
  moreover {
    interpret thread: reachable_thread P t r s i "done" "(step # todo)" skipped
      using 1 by unfold_locales auto
    fix st'
    assume "st' \<in> set done" and "\<not> noteStep st'"
    hence "(i, st') \<in> steps t" by (auto intro: thread.not_note_done_in_steps)
  }
  ultimately show ?case using 1
    apply(subgoal_tac "True")
    apply(clarsimp)
    apply(rule source_case)
    by(assumption | simp add: remove_hints)+
qed

text{* Proving typing monotonicity *}

subsubsection{* Monotonicity Proofs *}

definition monoMsgTyp :: "msgtype \<Rightarrow> bool"
where "monoMsgTyp ty \<equiv>
         (\<forall>i t r s t' r'.
            roleMap r \<subseteq>\<^sub>m roleMap r' \<longrightarrow>
            ty i (t, r, s) \<subseteq> ty i (t @ t', r', s))"

lemma monoMsgTypD:
  "\<lbrakk> monoMsgTyp ty;
     m \<in> ty i (t,r,s);
     roleMap r \<subseteq>\<^sub>m roleMap r'
   \<rbrakk> \<Longrightarrow>
   m \<in> ty  i (t@t',r',s)"
  unfolding monoMsgTyp_def by blast


lemma monoMsgTyp_SumTI[intro!]:
  assumes ty1: "monoMsgTyp ty1"
  and     ty2: "monoMsgTyp ty2"
  shows "monoMsgTyp (SumT ty1 ty2)"
  by(auto simp: monoMsgTyp_def SumT_def 
          dest: monoMsgTypD[OF ty1] monoMsgTypD[OF ty2])

lemma monoMsgTyp_InterTI[intro!]:
  assumes ty1: "monoMsgTyp ty1"
  and     ty2: "monoMsgTyp ty2"
  shows "monoMsgTyp (InterT ty1 ty2)"
  by(auto simp: monoMsgTyp_def InterT_def 
          dest: monoMsgTypD[OF ty1] monoMsgTypD[OF ty2])

lemma monoMsgTyp_KnownTI[iff]:
  shows "monoMsgTyp (KnownT step)"
  by(auto simp: monoMsgTyp_def KnownT_def )
      
lemma monoMsgTyp_NonceTI[iff]:
  shows "monoMsgTyp (NonceT R n)"
  by(auto simp: monoMsgTyp_def NonceT_def dest: map_leD)

lemma monoMsgTyp_ConstTI[iff]:
  shows "monoMsgTyp (ConstT c)"
  by(auto simp: monoMsgTyp_def ConstT_def dest: map_leD)

lemma monoMsgTyp_AgentTI[iff]:
  shows "monoMsgTyp AgentT"
  by(auto simp: monoMsgTyp_def AgentT_def dest: map_leD)

lemma monoMsgTyp_EncTI[intro!]:
  assumes ty1: "monoMsgTyp ty1"
  and     ty2: "monoMsgTyp ty2"
  shows "monoMsgTyp (EncT ty1 ty2)"
  by(auto simp: monoMsgTyp_def EncT_def 
          dest: monoMsgTypD[OF ty1] monoMsgTypD[OF ty2])

lemma monoMsgTyp_KTI[intro!]:
  assumes ty1: "monoMsgTyp ty1"
  and     ty2: "monoMsgTyp ty2"
  shows "monoMsgTyp (KT ty1 ty2)"
  by(auto simp: monoMsgTyp_def KT_def 
          dest: monoMsgTypD[OF ty1] monoMsgTypD[OF ty2])

lemma monoMsgTyp_KShrTI[intro!]:
  shows "monoMsgTyp KShrT"
  by(auto simp: monoMsgTyp_def KShrT_def)

lemma monoMsgTyp_TupTI[intro!]:
  assumes ty1: "monoMsgTyp ty1"
  and     ty2: "monoMsgTyp ty2"
  shows "monoMsgTyp (TupT ty1 ty2)"
  by(auto simp: monoMsgTyp_def TupT_def 
          dest: monoMsgTypD[OF ty1] monoMsgTypD[OF ty2])

lemma monoMsgTyp_HashTI[intro!]:
  assumes ty: "monoMsgTyp ty"
  shows "monoMsgTyp (HashT ty)"
  by(auto simp: monoMsgTyp_def HashT_def 
          dest: monoMsgTypD[OF ty])

lemma monoMsgTyp_PKTI[intro!]:
  assumes ty: "monoMsgTyp ty"
  shows "monoMsgTyp (PKT ty)"
  by(auto simp: monoMsgTyp_def PKT_def 
          dest: monoMsgTypD[OF ty])

lemma monoMsgTyp_SKTI[intro!]:
  assumes ty: "monoMsgTyp ty"
  shows "monoMsgTyp (SKT ty)"
  by(auto simp: monoMsgTyp_def SKT_def 
          dest: monoMsgTypD[OF ty])

lemma monoTyp_mk_typing[intro!]:
  assumes monoMsgTyp: 
     "\<And> pos ty. (pos, ty) \<in> set tyeqs \<Longrightarrow> monoMsgTyp ty"
  shows "monoTyp (mk_typing tyeqs)"
using monoMsgTyp
proof(induct tyeqs)
  case Nil thus ?case
    by(auto intro!: monoTypI simp: mk_typing_def EmptyT_def)
next
  case (Cons tyeq tyeqs) 
  thus ?case
    proof(cases tyeq)
      case (Pair pos' ty') 
      have mk_typing_Cons [simp]:
        "mk_typing ((pos',ty')#tyeqs) = (mk_typing tyeqs)(pos' := ty')"
        by (simp add: mk_typing_def)
      with Pair show ?thesis
        apply(auto intro!: monoTypI)
        apply(auto intro: monoTypD[OF Cons(1), OF Cons(2)]
                          monoMsgTypD[OF Cons(2)]
                   simp: Pair)
        done
    qed
qed

subsection{* Automation *}

text{*
The automation of the welltypedness proofs is rather fragile.
As a general rule of operation we try to unfold type information
as late as possible. This allows to guide the automation tools
by matching on the structure of the types. However, it also
implies that more rules are necessary. Moreover the current set
of rules is not guaranteed to be complete.
*}

subsubsection{* ACI of Sum and Intersection Types *}

lemma SumT_absorb [simp]: "SumT ty ty = ty"
  by (rule ext, rule ext) (auto simp: SumT_def)

lemma SumT_left_absorb: "SumT ty1 (SumT ty1 ty2) = SumT ty1 ty2"
  by (rule ext, rule ext) (auto simp: SumT_def)

lemma SumT_commute: "SumT ty1 ty2 = SumT ty1 ty2"
  by (rule ext, rule ext) (auto simp: SumT_def)

lemma SumT_left_commute: "SumT ty1 (SumT ty2 ty3) = SumT ty2 (SumT ty1 ty3)"
  by (rule ext, rule ext) (auto simp: SumT_def)

lemma SumT_assoc: "SumT (SumT ty1 ty2) ty3  = SumT ty1 (SumT ty2 ty3)"
  by (rule ext, rule ext) (auto simp: SumT_def)

lemmas SumT_ac = SumT_assoc SumT_left_absorb SumT_commute SumT_left_commute
  -- {* Type sum is an AC-operator *}

lemma InterT_absorb [simp]: "InterT ty ty = ty"
  by (rule ext, rule ext) (auto simp: InterT_def)

lemma InterT_left_absorb: "InterT ty1 (InterT ty1 ty2) = InterT ty1 ty2"
  by (rule ext, rule ext) (auto simp: InterT_def)

lemma InterT_commute: "InterT ty1 ty2 = InterT ty1 ty2"
  by (rule ext, rule ext) (auto simp: InterT_def)

lemma InterT_left_commute: "InterT ty1 (InterT ty2 ty3) = InterT ty2 (InterT ty1 ty3)"
  by (rule ext, rule ext) (auto simp: InterT_def)

lemma InterT_assoc: "InterT (InterT ty1 ty2) ty3  = InterT ty1 (InterT ty2 ty3)"
  by (rule ext, rule ext) (auto simp: InterT_def)


lemmas InterT_ac = InterT_assoc InterT_left_absorb InterT_commute InterT_left_commute
  -- {* Type intersection is an AC-operator *}


subsubsection{* Type Membership *}


text{* Special types *}

text{* The rules for SumT are special, as their usage currently
depends on the combination of SumT and KnownT.
*}
lemma in_SumTE:
  "\<lbrakk> m \<in> SumT ty1 ty2 i q; m \<in> ty1 i q \<Longrightarrow> R; m \<in> ty2 i q \<Longrightarrow> R 
   \<rbrakk> \<Longrightarrow> R"
  by(auto simp: SumT_def)

lemma notin_SumTE [elim!]: 
  "\<lbrakk> m \<notin> SumT ty1 ty2 i q; 
     \<lbrakk> m \<notin> ty1 i q; m \<notin> ty2 i q \<rbrakk> \<Longrightarrow> R
   \<rbrakk> \<Longrightarrow> R"
  by(auto simp: SumT_def)

lemma notin_KnownT_append_StepE [dest!]:
  "m \<notin> KnownT step i (t@ [Step (i, step)], r, s) \<Longrightarrow>
   m \<notin> knows t"
  by(auto simp: KnownT_def)

lemma in_SumT_NonceT_NonceTE [elim!]:
  "\<lbrakk> m \<in> SumT (NonceT Ro n) (NonceT Ro' n') i q; 
     m \<in> NonceT Ro n i q \<Longrightarrow> R; 
     m \<in> NonceT Ro' n' i q \<Longrightarrow> R 
   \<rbrakk> \<Longrightarrow> R"
  by(auto simp: SumT_def)

(* TODO: Add more of the restricted SumT unfoldings analogous to the ones above.
   We don't unfold SumT eagerly, as this would result in too many branches being created.
   The above lemma is a hack to get triple types of the form SumT KnownT (SumT NonceT NonceT)
   to work. The proper way would be to only expand types of variables that are being analyzed
   by the decrChain function.
*)

text{* Direct unfoldings *}

lemma in_ConstT_simp [iff]:
  "(m \<in> ConstT c i q) = (m = LC c)"
  by(auto simp: ConstT_def)

lemma in_KnownTD [dest!]:
  "(x \<in> KnownT step i (t,r,s)) \<Longrightarrow> (predOrd t (Ln x) (St (i, step)))"
  by(simp add: KnownT_def)


text{* To be used together with if\_splits in a well-typedness
proof *}
lemma in_NonceT [simp]: 
  "(LN n i \<in> NonceT R n i' (t,r,s)) = (roleMap r i = Some R)"
  by(simp add: NonceT_def)

lemma in_NonceTE [elim!]:
  "\<lbrakk> m \<in> NonceT R n i (t,r,s); 
    \<And> nTid. \<lbrakk> m = LN n nTid; roleMap r nTid = Some R \<rbrakk> \<Longrightarrow> Q 
   \<rbrakk> \<Longrightarrow> Q"
  by(auto simp: NonceT_def)

lemma notin_NonceT_thenonceE [elim!]:
  "\<lbrakk> LN n nTid \<notin> NonceT nR n i (t, r(i \<mapsto> (done,todo,skipped)), s);
     nTid = i \<Longrightarrow> Q;
     \<lbrakk> nTid \<noteq> i; roleMap r nTid \<noteq> Some nR \<rbrakk> \<Longrightarrow> Q
   \<rbrakk> \<Longrightarrow> Q"
  by(auto simp: NonceT_def split: if_splits)


text{* These rules ensure that type information is exploited
when a match impossible without intruder activity happening.
*}
lemma Tup_in_SumT_KnownT_NonceTD [dest!]:
  "Tup x y \<in> SumT (KnownT step) (NonceT R n) i (t, r, s)
   \<Longrightarrow> predOrd t (Ln (Tup x y)) (St (i, step))"
  by(auto simp: KnownT_def SumT_def)

lemma Hash_in_SumT_KnownT_NonceTD [dest!]:
  "Hash x \<in> SumT (KnownT step) (NonceT R n) i (t, r, s)
   \<Longrightarrow> predOrd t (Ln (Hash x)) (St (i, step))"
  by(auto simp: KnownT_def SumT_def)

lemma Enc_in_SumT_KnownT_NonceTD [dest!]:
  "Enc x y \<in> SumT (KnownT step) (NonceT R n) i (t, r, s)
   \<Longrightarrow> predOrd t (Ln (Enc x y)) (St (i, step))"
  by(auto simp: KnownT_def SumT_def)

text{* TODO: Extend these lemmas for further combinations. This requires
some more thinking. However, for a well-designed protocols the message
structure is not required for disambiguation because the encryptions
contain tags that identify them.
*}

text{* Structural types *}

text{* The following rules are used in well-typedness proofs *}
lemma Hash_in_HashT [simp]: 
  "(Hash x \<in> HashT ty i q) = (x \<in> ty i q)"
  by (simp add: HashT_def)

lemma Tup_in_TupT [simp]: 
  "(Tup x y \<in> TupT ty1 ty2 i q) = (x \<in> ty1 i q \<and> y \<in> ty2 i q)"
  by (simp add: TupT_def)

lemma Enc_in_EncT [simp]: 
  "(Enc x y \<in> EncT ty1 ty2 i q) = (x \<in> ty1 i q \<and> y \<in> ty2 i q)"
  by (simp add: EncT_def)

lemma PK_in_PKT [simp]: "(PK x \<in> PKT ty i q) = (x \<in> ty i q)"
  by (simp add: PKT_def)

lemma SK_in_SKT [simp]: "(SK x \<in> SKT ty i q) = (x \<in> ty i q)"
  by (simp add: SKT_def)

lemma K_in_KT [simp]: 
  "(K x y \<in> KT ty1 ty2 i q) = (x \<in> ty1 i q \<and> y \<in> ty2 i q)"
  by (simp add: KT_def)



text{* The following rules ensure that messages are expanded
automatically in when applying the sources rule.
*}

lemma in_HashTE [elim!]:
  "\<lbrakk> m \<in> HashT ty i q;
     \<And> x. \<lbrakk> m = Hash x; x \<in> ty i q \<rbrakk> \<Longrightarrow> Q
   \<rbrakk> \<Longrightarrow> Q"
  by(auto simp: HashT_def)

lemma in_EncTE [elim!]:
  "\<lbrakk> m \<in> EncT ty1 ty2 i q;
     \<And> x k. \<lbrakk> m = Enc x k; x \<in> ty1 i q; k \<in> ty2 i q \<rbrakk> \<Longrightarrow> Q
   \<rbrakk> \<Longrightarrow> Q"
  by(auto simp: EncT_def)

lemma in_TupTE [elim!]:
  "\<lbrakk> m \<in> TupT ty1 ty2 i q;
     \<And> x y. \<lbrakk> m = \<lbrace> x, y \<rbrace>; x \<in> ty1 i q; y \<in> ty2 i q \<rbrakk> \<Longrightarrow> Q
   \<rbrakk> \<Longrightarrow> Q"
  by(auto simp: TupT_def)

lemma in_KTE [elim!]:
  "\<lbrakk> m \<in> KT ty1 ty2 i q;
     \<And> x y. \<lbrakk> m = K x y; x \<in> ty1 i q; y \<in> ty2 i q \<rbrakk> \<Longrightarrow> Q
   \<rbrakk> \<Longrightarrow> Q"
  by(auto simp: KT_def)

lemma in_PKTE [elim!]:
  "\<lbrakk> m \<in> PKT ty i q;
     \<And> x. \<lbrakk> m = PK x; x \<in> ty i q \<rbrakk> \<Longrightarrow> Q
   \<rbrakk> \<Longrightarrow> Q"
  by(auto simp: PKT_def)

lemma in_SKTE [elim!]:
  "\<lbrakk> m \<in> SKT ty i q;
     \<And> x. \<lbrakk> m = SK x; x \<in> ty i q \<rbrakk> \<Longrightarrow> Q
   \<rbrakk> \<Longrightarrow> Q"
  by(auto simp: SKT_def)


subsection{* Specialization of the Chain Rule *}

text{* We prove the case distinction on messages known to the
  intruder with respect to an typed state, because we need
  a sufficiently precise invariant when reasoning about the
  contents of a variable.
*}
lemma (in typed_state) knows_cases:
  assumes known: "m' \<in> knows t"
  shows "
   (m' \<in> IK0 \<and> 
    hint ''case_name'' ''ik0''
   ) \<or>
   (\<exists> m. m' = Hash m \<and> Ln m \<prec> Ln (Hash m) \<and>
         hint ''case_name'' ''fake''
   ) \<or>
   (\<exists> m k. m' = Enc m k \<and> 
           Ln m \<prec> Ln (Enc m k) \<and> Ln k \<prec> Ln (Enc m k) \<and>
           hint ''case_name'' ''fake''
   ) \<or>
   (\<exists> x y. m' = Tup x y \<and> 
           Ln x \<prec> Ln (Tup x y) \<and> Ln y \<prec> Ln (Tup x y) \<and>
           hint ''case_name'' ''fake''
   ) \<or>
   (\<exists> R \<in> P. \<exists> i. roleMap r i = Some R \<and> 
      (\<exists> step \<in> set R.
         (sendStep step \<or> noteStep step) \<and>
         (\<exists> m. Some m = inst s i (stepPat step) \<and> decrChain [] t {St (i, step)} m m') \<and>
         prefixClose s t R step i \<and>
         (\<forall> v \<in> FV (stepPat step). \<forall> n. v = MVar n \<longrightarrow> 
            s (MVar n, i) \<in> typing (R, n) i (t,r,s) \<and>
            hint ''case_name_subst'' n) \<and>
         hint ''decrChainFrom'' (i, R, step) \<and>
         hint ''case_name'' ''decrypt''
      )

   ) \<or>
   (\<exists> a. m' = SK a \<and> LKR a \<prec> Ln m' \<and> hint ''case_name'' ''asym_lkr'') \<or>
   (\<exists> a b. m' = K a b \<and> LKR a \<prec> Ln m' \<and> hint ''case_name'' ''sym_lkr1'') \<or>
   (\<exists> a b. m' = K a b \<and> LKR b \<prec> Ln m' \<and> hint ''case_name'' ''sym_lkr2'') \<or>
   (\<exists> A. \<exists> a \<in> A. m' = KShr A \<and> LKR (LAg a) \<prec> Ln m' \<and> hint ''case_name'' ''shr_lkr'')
   "
  (is "?ik0 \<or> ?hash \<or> ?encr \<or> ?tup \<or> ?decr \<or> ?keys")
proof -
  from known have
   "(m' \<in> IK0) \<or>
    (\<exists> m.   m' = Hash m   \<and> Ln m \<prec> Ln (Hash m)) \<or>
    (\<exists> m k. m' = Enc  m k \<and> Ln m \<prec> Ln (Enc m k) \<and> Ln k \<prec> Ln (Enc m k)) \<or>
    (\<exists> x y. m' = Tup  x y \<and> Ln x \<prec> Ln (Tup x y) \<and> Ln y \<prec> Ln (Tup x y)) \<or>
    (\<exists> i done todo skipped. r i = Some (done, todo, skipped) \<and> 
       (\<exists> l pt m. 
          Send l pt \<in> set done \<and> Some m = inst s i pt \<and> 
          decrChain [] t {St (i, Send l pt)} m m'
       )
    ) \<or>
    (\<exists> i done todo skipped. r i = Some (done, todo, skipped) \<and> 
       (\<exists> l ty pt m. 
          Note l ty pt \<in> set done \<and> Note l ty pt \<notin> skipped \<and> 
          Some m = inst s i pt \<and> 
          decrChain [] t {St (i, Note l ty pt)} m m'
       )
    ) \<or>
   (\<exists> a. m' = SK a \<and> LKR a \<prec> Ln m') \<or>
   (\<exists> a b. m' = K a b \<and> LKR a \<prec> Ln m') \<or>
   (\<exists> a b. m' = K a b \<and> LKR b \<prec> Ln m') \<or> 
   (\<exists> A. \<exists> a \<in> A. m' = KShr A \<and> LKR (LAg a) \<prec> Ln m')
   "
    (is "?ik0_raw \<or> ?hash_raw \<or> ?encr_raw \<or> ?tup_raw \<or> ?decr_raw \<or> ?note_raw \<or> ?keys_raw")
    by (rule knows_cases_raw)
  moreover 
  {
    assume "?ik0_raw" 
    hence ?thesis by( simp add: remove_hints)
  }
  moreover 
  {
    assume "?hash_raw" 
    hence ?thesis by( simp add: remove_hints)
  }
  moreover 
  {
    assume "?encr_raw" 
    hence ?thesis by( simp add: remove_hints)
  }
  moreover 
  {
    assume "?tup_raw" 
    hence ?thesis by( simp add: remove_hints)
  }
  moreover 
  {
    assume "?keys_raw" 
    hence ?thesis by( simp add: remove_hints)
  }
  moreover
  { assume ?decr_raw then
    obtain i "done" todo l msg skipped m
      where thread_exists: "r i = Some (done, todo,skipped)"
      and send_done: "Send l msg \<in> set done"
      and msg:       "Some m = inst s i msg"
      and decrChain: "decrChain [] t {St (i, Send l msg)} m m'"
      by fast
    then interpret th1: typed_thread P t r s i "done" todo skipped "typing"
      using approximates by unfold_locales
    from send_done have send_step: "(i, Send l msg) \<in> steps t" 
      by (rule th1.in_steps_send[THEN iffD1])
    moreover
    have "prefixClose s t (done@todo) (Send l msg) i" using send_step
      by(auto intro!: prefixCloseI th1.roleMap)
    moreover
    have send_in_role: "Send l msg \<in> set (done @ todo)"
      using send_done by simp
    moreover
    note in_approxD[OF th1.approximates send_step th1.roleMap, simplified]
    ultimately
    have ?decr using decrChain msg
      apply -
      apply(rule bexI[OF _ th1.role_in_P])
      apply(rule exI)
      apply(rule conjI[OF th1.roleMap])
      apply(rule bexI[OF _ send_in_role])
      by(auto simp: remove_hints)
    hence ?thesis by blast 
  }
  moreover
  {
    assume ?note_raw
    then obtain i "done" todo skipped l ty pt m
      where thread_exists: "r i = Some (done, todo,skipped)"
      and inDone: "Note l ty pt \<in> set done"
      and notinSkipped:  "Note l ty pt \<notin> skipped"
      and msg:       "Some m = inst s i pt"
      and decrChain: "decrChain [] t {St (i, Note l ty pt)} m m'"
      by fast
    then interpret th1: typed_thread P t r s i "done" todo skipped "typing"
      using approximates by unfold_locales
    from inDone and notinSkipped have note_step: "(i, Note l ty pt) \<in> steps t" 
      by (fastforce dest!: th1.in_steps_eq_in_done)
    moreover
    have "prefixClose s t (done@todo) (Note l ty pt) i" using note_step
      by(auto intro!: prefixCloseI th1.roleMap)
    moreover
    have note_in_role: "Note l ty pt \<in> set (done @ todo)"
      using inDone by simp
    moreover
    note in_approxD[OF th1.approximates note_step th1.roleMap, simplified]
    ultimately
    have ?decr using decrChain msg
      apply -
      apply(rule bexI[OF _ th1.role_in_P])
      apply(rule exI)+
      apply(rule conjI[OF th1.roleMap])
      apply(rule bexI[OF _ note_in_role])
      by(auto simp: remove_hints)
    hence ?thesis by blast 
  }
  ultimately
  show ?thesis by fastforce
qed


lemma (in reachable_state) decrChain_AgentE:
  assumes decrChain: "decrChain path t from m m'"
  and         Agent: "m \<in> Agent"
  and      nonempty: "from = {} \<Longrightarrow> Q"
  shows "Q"
  using decrChain Agent nonempty
  by (auto simp: Agent_def)

(*
lemma (in reachable_state) decrChain_AgentTE:
  assumes decrChain: "decrChain path t from m m'"
  and        AgentT: "m \<in> AgentT i (t,r,s)" 
  and          elim: "m = m' \<Longrightarrow> Q"
  shows "Q"
  using decrChain AgentT elim
  by (auto simp: AgentT_def)
*)

lemma (in reachable_state) decrChain_imp_predOrd:
  "\<lbrakk> decrChain path t from m m' \<rbrakk> \<Longrightarrow>
  \<exists> im \<in> pairParts m. (\<forall> f \<in> from. f \<prec> Ln im) \<and> Ln im \<preceq> Ln m'"
proof(induct m arbitrary: path "from")
  case (Tup x y) thus ?case
    apply(simp)
    apply(erule disjE)
    apply(clarsimp)
    apply(rule disjI2)
    apply(fastforce intro: less_le_trans)
    done
qed fastforce+

lemma (in reachable_state) decrChain_KnownT:
  assumes decrChain: "decrChain path t from m m'"
  and        KnownT: "predOrd t (Ln m) (St (i, step))"
  shows "\<exists> im \<in> pairParts m. 
           (\<forall> f \<in> from. f \<prec> Ln im) \<and> Ln im \<prec> St (i, step)"
proof -
  obtain im
    where "im \<in> pairParts m" and "\<forall>f \<in> from. f \<prec> Ln im"
    using decrChain by (fast dest!: decrChain_imp_predOrd)
  with KnownT show ?thesis
    by (fastforce intro: pairParts_before)
qed

lemma (in reachable_state) decrChain_KnownTE:
  assumes decrChain: "decrChain path t from m m'"
  and        KnownT: "predOrd t (Ln m) (St (i, step))"
  and elim: "\<And> im. \<lbrakk> im \<in> pairParts m; 
                      \<forall> f \<in> from. f \<prec> Ln im;
                      Ln im \<prec> St (i, step)
                    \<rbrakk> \<Longrightarrow> Q"
  shows "Q"
  using decrChain KnownT
  by(auto dest!: decrChain_KnownT elim)

lemma (in reachable_state) decrChain_SumT_KnownTE:
  assumes KnownT: "m \<in> SumT (KnownT step) ty i (t,r,s)" 
  and  decrChain: "decrChain path t from m m'"
  and elimK: "\<And> im. \<lbrakk> im \<in> pairParts m; 
                       \<forall> f \<in> from. f \<prec> Ln im;
                       Ln im \<prec> St (i, step)
                     \<rbrakk> \<Longrightarrow> Q"
  and elimTy: "m \<in> ty i (t,r,s) \<Longrightarrow> Q"
  shows "Q"
  using decrChain KnownT elimK elimTy
  by(auto elim!: in_SumTE decrChain_KnownTE)


lemma (in reachable_state) AV_in_Agent [iff]: 
  "s (AV a aTid) \<in> Agent"
using inst_AVar_cases 
by (auto simp: Agent_def)


end

(* TODO: 
    - Remove agent variables from protocol model by 
      replacing them with type annotations. 

      [General version will require us to reintroduce create event.
       But composition becomes nicer, as we can now model protocols, which
       use parameters that are secret values and so on.
      ]


    - Put decryption chain case into recursion of chain
      predicate to make more information available locally.
*)


