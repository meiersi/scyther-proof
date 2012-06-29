theory UnpairedLogic
imports
  UnpairedExecution
begin


subsection{* Input Terms *}

fun inp :: "wt_subst \<Rightarrow> execevent \<Rightarrow> execmsg set"
where
  "inp s (MkStep tid (Send l msg)) = {}"
| "inp s (MkStep tid (Recv l msg)) = unpair (subst s (s2e msg tid))"
| "inp s (FromIK0 m)               = {}"
| "inp s (MkHash m)                = unpair m"
| "inp s (MkTup x y)               = unpair x \<union> unpair y"
| "inp s (MkFst x y)               = {Tup x y}"
| "inp s (MkSnd x y)               = {Tup x y}"
| "inp s (MkEncr m k)              = unpair m \<union> unpair k"
| "inp s (MkDecr m k)              = insert (Enc m k) (unpair (inv k))"

lemma inp_ground_by_eventMsg_ground:
  "\<lbrakk> m \<in> inp s e; ground (eventMsg s e) \<rbrakk> \<Longrightarrow> ground m"
  apply(induct e rule: inp.induct)
  apply(auto intro: ground_unpaired)
  apply(rule_tac m="inv k" in ground_unpaired, auto) 
  done

fun ucUnpairMsg :: "execmsg \<Rightarrow> knevent list"
where
  "ucUnpairMsg (Tup x y) =
    \<Delta> MkFst x y # \<star> x # ucUnpairMsg x @
    \<Delta> MkSnd x y # \<star> y # ucUnpairMsg y"
| "ucUnpairMsg m = []"


lemma set_unpairMsg_subset_set_ucUnpairMsg: 
  "set (unpairMsg knows m) \<subseteq> set (ucUnpairMsg m)"
  by(induct m arbitrary: knows, auto split: if_splits)

lemmas set_unpairMsg_subset_set_ucUnpairMsgD =
  subsetD[OF set_unpairMsg_subset_set_ucUnpairMsg, rule_format]


declare reachable_state.intro[intro!, simp]

context reachable_state begin

lemma ground_by_eventMsg:
  "\<lbrakk> \<Delta>(e) \<in> set t; eventMsg s e = m \<rbrakk> \<Longrightarrow> ground m"
  by(auto dest!: eventMsg_ground)

lemma inp_extend_wts:
  "\<Delta>(e) \<in> set t \<Longrightarrow> inp (extend_wts s s') e = inp s e"
  apply(insert reachable)
  apply(induct rule: inp.induct)
  apply(simp_all add: extend_wts_conv_subst)
  apply(subst subst_ground_msg)
  apply(auto intro!: reachable_state.ground_by_eventMsg)
  done

declare reachable_state.inp_extend_wts
          [OF reachable_state.intro, simp]


lemma MkFst_unpairMsg_inp_known:
  "\<Delta> (MkFst x y) \<in> set (unpairMsg knows m) \<Longrightarrow> 
   Tup x y \<in> knows \<or> Tup x y \<in> pairParts m"
  by(induct m arbitrary: knows, auto split: if_splits)

lemma MkSnd_unpairMsg_inp_known:
  "\<Delta> (MkSnd x y) \<in> set (unpairMsg knows m) \<Longrightarrow> 
   Tup x y \<in> knows \<or> Tup x y \<in> pairParts m"
  by(induct m arbitrary: knows, auto split: if_splits)

lemma Knows_inp_unpairMsg:
  "\<lbrakk> \<Delta> e \<in> set (unpairMsg knows m); m' \<in> inp s' e; m' \<notin> knows; m' \<noteq> m \<rbrakk> \<Longrightarrow> 
   \<star> m' \<in> set (unpairMsg knows m)"
  apply(frule in_set_unpairMsg_casesD)
  apply(auto dest!: MkFst_unpairMsg_inp_known MkSnd_unpairMsg_inp_known
             elim!: Knows_in_set_unpairMsgI)
  done

lemma Knows_mostly_unpaired:
  "\<lbrakk> t = t' @ \<Delta> e # t''; \<star> m \<in> set t'; m' \<in> pairParts m \<rbrakk> \<Longrightarrow> 
   \<star> m' \<in> set t'"
  apply(insert reachable, rotate_tac -1)
proof(induct arbitrary: e m m' t' t'' rule: reachable.induct)
  case (hash t r s m e m' x t' t'')
  show ?case using prems(4-9)
thm prems(3)
    apply(subst (asm) append_eq_append_conv2)
    apply(clarsimp)
    apply(erule disjE)
    apply(simp)
    apply(erule disjE)
    apply(rule prems(3))
    apply(subst (asm) append_eq_Cons_conv)
    apply(clarsimp)
    apply(erule disjE)
    apply(auto)
  thus ?case


  case (send t r s l msg tid m e m') 
  show ?case using prems(4,6-7)
    by(auto dest: Knows_inp_unpairMsg
           elim!: prems(3))
next



lemma Knows_inp:
  "\<lbrakk> \<Delta>(e) \<in> set t; m \<in> inp s e \<rbrakk> \<Longrightarrow> \<star>(m) \<in> set t"
  apply(insert reachable, rotate_tac -1)
proof(induct arbitrary: e m rule: reachable.induct)
  case (send t r s l msg tid m e m') 
  show ?case using prems(4,6-7)
    by(auto dest: Knows_inp_unpairMsg
           elim!: prems(3))
next
  case (hash t r s m e m')
  show ?case using prems(4-8)
    apply(simp)
    apply(erule disjE)
    apply(simp)
    apply(auto dest: prems(3))
thm prems(3)

lemma Knows_before_inp:
  "\<lbrakk> \<Delta>(e) \<in> set t; m \<in> inp s e \<rbrakk> \<Longrightarrow> \<star>(m) \<prec> \<Delta>(e)"
  apply(simp add: pred_def)
  apply(insert reachable, rotate_tac -1)
  apply(induct arbitrary: e m rule: reachable.induct)
  apply(simp)
  apply(case_tac "\<Delta>(e) \<in> set t",simp,simp)
  apply(case_tac "\<Delta>(e) \<in> set t",simp,force split: if_splits)
  apply(case_tac "\<Delta>(e) \<in> set t",simp,force)+
  done

end

subsection{* Learning from a message *}


fun fromMsg_raw :: "wt_subst \<Rightarrow> kntrace \<Rightarrow> specmsg \<Rightarrow> tid \<Rightarrow> execmsg \<Rightarrow> bool"
where
  "fromMsg_raw s t (Enc msg key) tid m = 
   (
     (subst s (s2e (Enc msg key) tid) = m) \<or>
     ( (nextRel t (\<Delta>(MkDecr (subst s (s2e msg tid)) 
                            (subst s (s2e key tid))))
                  (\<star>(subst s (s2e msg tid)))
       ) \<and>
       fromMsg_raw s t msg tid m
     )
   )"
| "fromMsg_raw s t (Tup x y) tid m = 
   (
     (subst s (s2e (Tup x y) tid) = m) \<or>
     ( (nextRel t (\<Delta>(MkFst (subst s (s2e x tid))
                           (subst s (s2e y tid))))
                  (\<star>(subst s (s2e x tid)))
       ) \<and>
       fromMsg_raw s t x tid m
     ) \<or>
     ( (nextRel t (\<Delta>(MkSnd (subst s (s2e x tid))
                           (subst s (s2e y tid))))
                  (\<star>(subst s (s2e y tid)))
       ) \<and>
       fromMsg_raw s t y tid m
     )
   )"
| "fromMsg_raw s t msg tid m =
     (subst s (s2e msg tid) = m)"

lemma nextRel_appendI1:
  "nextRel xs x y \<Longrightarrow> nextRel (xs@ys) x y"
  by(induct xs, simp, case_tac xs, auto)

lemma fromMsg_raw_appendI1:
  "fromMsg_raw s t msg tid m \<Longrightarrow> 
   fromMsg_raw s (t@t') msg tid m"
  apply(induct arbitrary: s t rule: fromMsg_raw.induct)
  by(auto intro!: nextRel_appendI1)

lemma fromMsg_rawI1:
  "\<lbrakk> subst s (s2e msg tid) = m; ground m \<rbrakk> 
   \<Longrightarrow> fromMsg_raw s t msg tid m"
  by(induct arbitrary: s rule: fromMsg_raw.induct, auto)

lemma fromMsg_raw_Snoc_MkDecrI:
  "\<lbrakk> ground m; fromMsg_raw s t msg tid (Enc m k) \<rbrakk> \<Longrightarrow> 
   fromMsg_raw s (t @ [\<Delta> MkDecr m k, \<star> m]) msg tid m"
  apply(induct arbitrary: m k s t rule: fromMsg_raw.induct)
  apply(auto intro: nextRelI fromMsg_rawI1 nextRel_appendI1)
  apply(case_tac v, auto)
  done

lemma fromMsg_raw_Snoc_MkFstI:
  "\<lbrakk> ground x; fromMsg_raw s t msg tid (Tup x y) \<rbrakk> \<Longrightarrow> 
   fromMsg_raw s (t @ [\<Delta> MkFst x y, \<star> x]) msg tid x"
  apply(induct arbitrary: x y s t rule: fromMsg_raw.induct)
  apply(auto intro: nextRelI fromMsg_rawI1 nextRel_appendI1)
  apply(case_tac v, auto)
  done

lemma fromMsg_raw_Snoc_MkSndI:
  "\<lbrakk> ground y; fromMsg_raw s t msg tid (Tup x y) \<rbrakk> \<Longrightarrow> 
   fromMsg_raw s (t @ [\<Delta> MkSnd x y, \<star> y]) msg tid y"
  apply(induct arbitrary: x y s t rule: fromMsg_raw.induct)
  apply(auto intro: nextRelI fromMsg_rawI1 nextRel_appendI1)
  apply(case_tac v, auto)
  done

definition eruns :: "rolestep threadpool \<Rightarrow> tid \<Rightarrow> role \<Rightarrow> bool"
where "eruns r tid R \<equiv> (case r tid of
                         Some (todo,done) \<Rightarrow> Rep_role R = rev done @ todo
                       | None             \<Rightarrow> False)"

lemma eruns_nextStep [simp]: 
  "eruns (nextStep r tid) tid' R = eruns r tid' R"
  by(simp add: nextStep_def eruns_def split: option.splits list.splits)


context reachable_state begin

lemma fromMsg_raw_extend_wtsI:
  "\<lbrakk> fromMsg_raw s t msg tid m; ground (subst s (s2e msg tid)) \<rbrakk>
   \<Longrightarrow> fromMsg_raw (extend_wts s s') t msg tid m"
  apply(induct arbitrary: s rule: fromMsg_raw.induct)
  apply(simp_all add: extend_wts_conv_subst)
  apply(auto simp: extend_wts_def)
  done

lemma nextRel_rev:
  "nextRel (rev xs) x y = nextRel xs y x"
  apply(simp add: nextRel_conv)
  apply(auto)
  apply(drule_tac f=rev in arg_cong, simp)
  apply(rule_tac x="rev zs" in exI, simp)+
  done

lemma nextRel_Snoc_simps:
  "nextRel (xs@[a])   x y = nextRel (a#rev xs)   y x"
  "nextRel (xs@[a,b]) x y = nextRel (b#a#rev xs) y x"
  by(subst nextRel_rev[symmetric], simp)+

lemma nextRel_Cons_simps:
  "x \<noteq> y \<Longrightarrow> nextRel (x#xs) y z = nextRel xs y z"
  "x' \<noteq> z \<Longrightarrow> nextRel (x#x'#xs) y z = nextRel (x'#xs) y z"
  by(case_tac xs, simp+)

lemmas nextRel_simps [simp] = nextRel_rev nextRel_Snoc_simps nextRel_Cons_simps

lemma nextRel_FromIK0D: "nextRel t (\<Delta> FromIK0 m) (\<star> m') \<Longrightarrow> m' \<in> IK0"
  apply(insert reachable, rotate_tac -1)
  by(induct rule: reachable.induct, auto split: if_splits)
  
lemma nextRelI [simp,intro!]: "nextRel (xs@x#y#ys) x y"
  by(auto simp: nextRel_conv)

lemma notin_IK0 [iff]:
  "Enc m k \<notin> IK0"
  "Hash m \<notin> IK0"
  "Lit (ENonce n tid) \<notin> IK0"
  "Tup x y \<notin> IK0"
  by(auto simp: IK0_def)
(* TODO: Move and add K Eve Eve *)

lemma knows_cases_raw:
  "\<star>(m') \<in> set t \<Longrightarrow>
   (\<Delta>(FromIK0 m') \<prec>\<^sub>1 \<star>(m')) \<or>
   (\<exists> m.   m' = Hash m   \<and> \<Delta>(MkHash m)   \<prec>\<^sub>1 \<star>(Hash m)) \<or>
   (\<exists> m k. m' = Enc  m k \<and> \<Delta>(MkEncr m k) \<prec>\<^sub>1 \<star>(Enc m k)) \<or>
   (\<exists> x y. m' = Tup  x y \<and> \<Delta>(MkTup x y)  \<prec>\<^sub>1 \<star>(Tup x y)) \<or>
   (\<exists> R \<in> P. \<exists> tid. eruns r tid R \<and> 
      (\<exists> l msg. 
         Send l msg \<in> roleEvs R \<and>
         \<Delta>(MkStep tid (Send l msg)) \<prec>\<^sub>1 \<star>(subst s (s2e msg tid)) \<and>
         fromMsg_raw s t msg tid m'
      )
   )"
  apply(simp add: next_def)
  apply(insert reachable, rotate_tac -1)
proof (induct arbitrary: m' rule: reachable.induct)
  case init thus ?case by simp
next
  case (hash t r s m) show ?case using prems(4-7)
    apply(simp)
    apply(erule disjE, simp)
    apply(drule_tac m'=m' in prems(3))
    apply(erule disjE, clarsimp)+
    apply(rule disjI2)+
    apply(auto intro!: fromMsg_raw_appendI1)
    done
next
  case (tuple t r s x y) thus ?case
    apply(simp)
    apply(erule disjE, simp)
    apply(drule_tac m'=m' in prems(3))
    apply(erule disjE, clarsimp)+
    apply(rule disjI2)+
    apply(auto intro!: fromMsg_raw_appendI1)
    done
(*
    apply(case_tac "\<star>(m') \<in> set t", simp)
    apply(rule knows_cases_appendI1)
    apply(erule prems)
    apply(simp)
    done
*)
next
  case (encr t r s m k) thus ?case
    apply(simp)
    apply(erule disjE, simp)
    apply(drule_tac m'=m' in prems(3))
    apply(erule disjE, clarsimp)+
    apply(rule disjI2)+
    apply(auto intro!: fromMsg_raw_appendI1)
    done
next
  case (ik0 t r s m) thus ?case
    apply(simp)
    apply(erule disjE, simp)
    apply(drule_tac m'=m' in prems(3))
    apply(erule disjE, clarsimp)+
    apply(rule disjI2)+
    apply(auto intro!: fromMsg_raw_appendI1)
    done
next
  case (send t r s l msg tid m m') 
    then interpret old_state: reachable_state P t r s by unfold_locales
    show ?case using prems(4-6)
    apply(simp split: if_splits)
    apply(drule_tac m'=m' in prems(3))
    apply(erule disjE, clarsimp)+
    apply(rule disjI2)+
    apply(force intro!: fromMsg_raw_appendI1)

    apply(erule disjE)
    apply(drule_tac m'=m' in prems(3))
    apply(erule disjE, clarsimp)+
    apply(rule disjI2)+
    apply(force intro!: fromMsg_raw_appendI1)

    apply(rule disjI2)+
    apply(simp)
    apply(drule Some_curStepD)
    apply(clarsimp)
    apply(frule old_state.proto_roles)
    apply(clarsimp)
    apply(rule_tac x=R in bexI)
    apply(rule_tac x=tid in exI)
    apply(rule conjI)
    apply(simp add: eruns_def)
    apply(rule_tac x=l in exI)
    apply(rule_tac x=msg in exI)
    apply(rule conjI)
    apply(simp add: roleEvs_def)
    apply(simp)
    apply(rule fromMsg_rawI1)
    apply(simp)
    apply(rule old_state.Send_ground)
    apply(simp add: curStep_def)
    apply(simp)
    done
next
  case (decr t r s m k m') 
    then interpret old_state: reachable_state P t r s by unfold_locales
    show ?case using prems(4-8)
    apply(subgoal_tac "ground m'")
    apply(case_tac "\<star>(m') \<in> set t", simp)
    apply(drule_tac m'=m' in prems(3))
    apply(erule disjE, clarsimp)+
    apply(rule disjI2)+
    apply(force intro!: fromMsg_raw_appendI1)

    apply(drule prems(3), simp)

    apply(erule disjE)
    apply(drule old_state.nextRel_FromIK0D, simp)

    apply(erule disjE)
    apply(drule in_set_nextRel1)
    apply(drule old_state.Knows_inp)
    apply(force,simp)

    apply(rule disjI2)+
    apply(clarsimp)
    apply(rule_tac x=R in bexI)
    apply(rule_tac x=tid in exI)
    apply(simp)
    apply(rule exI)+
    apply(rule conjI, simp+)
    apply(rule fromMsg_raw_Snoc_MkDecrI)
    apply(simp)+
    apply(force dest!: old_state.Knows_ground 
                 simp: old_state.Knows_ground)
    done
next
  case (fst t r s x y m') 
    then interpret old_state: reachable_state P t r s by unfold_locales
    show ?case using prems(4-7)
    apply(subgoal_tac "ground m'")
    apply(case_tac "\<star>(m') \<in> set t", simp)
    apply(drule_tac m'=m' in prems(3))
    apply(erule disjE, clarsimp)+
    apply(rule disjI2)+
    apply(force intro!: fromMsg_raw_appendI1)

    apply(drule prems(3), simp)

    apply(erule disjE)
    apply(drule old_state.nextRel_FromIK0D, simp)

    apply(erule disjE)
    apply(drule in_set_nextRel1)
    apply(drule old_state.Knows_inp)
    apply(force,simp)

    apply(rule disjI2)+
    apply(clarsimp)
    apply(rule_tac x=R in bexI)
    apply(rule_tac x=tid in exI)
    apply(simp)
    apply(rule exI)+
    apply(rule conjI, simp+)
    apply(rule fromMsg_raw_Snoc_MkFstI)
    apply(simp)+
    apply(force dest!: old_state.Knows_ground 
                 simp: old_state.Knows_ground)
    done
next
  case (snd t r s x y m') 
    then interpret old_state: reachable_state P t r s by unfold_locales
    show ?case using prems(4-7)
    apply(subgoal_tac "ground m'")
    apply(case_tac "\<star>(m') \<in> set t", simp)
    apply(drule_tac m'=m' in prems(3))
    apply(erule disjE, clarsimp)+
    apply(rule disjI2)+
    apply(force intro!: fromMsg_raw_appendI1)

    apply(drule prems(3), simp)

    apply(erule disjE)
    apply(drule old_state.nextRel_FromIK0D, simp)

    apply(erule disjE)
    apply(drule in_set_nextRel1)
    apply(drule old_state.Knows_inp)
    apply(force,simp)

    apply(rule disjI2)+
    apply(clarsimp)
    apply(rule_tac x=R in bexI)
    apply(rule_tac x=tid in exI)
    apply(simp)
    apply(rule exI)+
    apply(rule conjI, simp+)
    apply(rule fromMsg_raw_Snoc_MkSndI)
    apply(simp)+
    apply(force dest!: old_state.Knows_ground 
                 simp: old_state.Knows_ground)
    done
next
  case (create t r s tid R \<alpha> m')
    then interpret old_state: reachable_state P t r s by unfold_locales
    show ?case using prems(4,5,8)
      apply(simp)
      apply(drule prems)
      apply(erule disjE, clarsimp)+
      apply(rule disjI2)+
      apply(erule bexE, erule exE, erule conjE)
      apply(erule exE, erule exE, (erule conjE)+)
      apply(rule_tac x=Ra in bexI)
      apply(rule_tac x=tida in exI)
      apply(rule conjI)
      apply(clarsimp simp: eruns_def newThread_def split: option.splits)
      apply(rule_tac x=l in exI, rule_tac x=msg in exI)
      apply(frule in_set_nextRel2)
      apply(drule old_state.Knows_ground)
      apply(auto simp: extend_wts_conv_subst old_state.fromMsg_raw_extend_wtsI)
      done
next
  case (recv t r s l msg tid \<alpha> m')
    then interpret old_state: reachable_state P t r s by unfold_locales
    show ?case using prems(4,6,7)
      apply(subgoal_tac "ground m'")
      apply(simp)
      apply(drule_tac m'=m' in prems(3))
      apply(erule disjE, clarsimp)+
      apply(rule disjI2)+
      apply(erule bexE, erule exE, erule conjE)
      apply(erule exE, erule exE, (erule conjE)+)
      apply(rule_tac x=R in bexI)
      apply(rule_tac x=tida in exI)
      apply(rule conjI)
      apply(clarsimp simp: eruns_def newThread_def split: option.splits)
      apply(rule_tac x=la in exI, rule_tac x=msga in exI)
      apply(frule in_set_nextRel2)
      apply(auto simp: extend_wts_conv_subst old_state.fromMsg_raw_extend_wtsI
               intro!: fromMsg_raw_appendI1
                dest!: old_state.Knows_ground 
                 simp: old_state.Knows_ground)
      done
qed

end


fun fromMsg :: "wt_subst \<Rightarrow> kntrace \<Rightarrow> specmsg \<Rightarrow> tid \<Rightarrow> execmsg \<Rightarrow> bool"
where
  "fromMsg s t (Enc msg key) tid m = 
   (
     (subst s (s2e (Enc msg key) tid) = m) \<or>
     (listOrd t (\<star> Enc (subst s (s2e msg tid)) (subst s (s2e key tid)))
                (\<star> subst s (s2e msg tid))
      \<and>
      listOrd t (\<star> subst s (s2e (inv key) tid))
                (\<star> subst s (s2e msg tid))
      \<and>
      fromMsg s t msg tid m
     )
   )"
| "fromMsg s t (Tup x y) tid m = 
   (
     (subst s (s2e (Tup x y) tid) = m) \<or>
     (listOrd t (\<star> Tup (subst s (s2e x tid)) (subst s (s2e y tid)))
                (\<star> subst s (s2e x tid))
      \<and>
      fromMsg s t x tid m
     ) \<or>
     (listOrd t (\<star> Tup (subst s (s2e x tid)) (subst s (s2e y tid)))
                (\<star> subst s (s2e y tid))
      \<and>
      fromMsg s t y tid m
     )
   )"
| "fromMsg s t msg tid m = (subst s (s2e msg tid) = m)"


context reachable_state begin


lemma fromMsg_raw_imp_fromMsg:
  "fromMsg_raw s t msg tid m \<Longrightarrow> fromMsg s t msg tid m"
  apply(induct msg)
  apply(simp_all add: next_def[symmetric] pred_def[symmetric])
  apply(erule disjE, simp)
  apply(erule disjE, simp)
  apply(erule conjE)
  apply(drule next_imp_less)
  apply(frule Knows_before_inp[OF in_set_less1])
  apply(simp, force)
  apply(erule conjE)
  apply(drule next_imp_less)
  apply(frule Knows_before_inp[OF in_set_less1])
  apply(simp)
  apply(force intro: less_trans)
  apply(erule disjE, simp)
  apply(erule conjE)
  apply(drule next_imp_less)
  apply(rule disjI2, rule conjI)
  apply(frule Knows_before_inp[OF in_set_less1]) prefer 3
  apply(frule Knows_before_inp[OF in_set_less1])
  apply(simp, rule disjI2)
  apply(auto intro: less_trans)
  done

lemma knows_cases:
  "\<star>(m') \<in> set t \<Longrightarrow>
   (m' \<in> IK0) \<or>
   (\<exists> m. m' = Hash m \<and>  \<star> m \<prec> \<star> Hash m ) \<or>
   (\<exists> m k. m' = Enc  m k \<and> \<star> m \<prec> \<star> Enc m k \<and> \<star> k \<prec> \<star> Enc m k) \<or>
   (\<exists> x y. m' = Tup  x y \<and> \<star> x \<prec> \<star> Tup x y \<and> \<star> y \<prec> \<star> Tup x y) \<or>
   (\<exists> R \<in> P. \<exists> tid. eruns r tid R \<and> 
      (\<exists> l msg. 
         Send l msg \<in> roleEvs R \<and>
         \<Delta>(MkStep tid (Send l msg)) \<prec> \<star>(subst s (s2e msg tid)) \<and>
         fromMsg s t msg tid m'
      )
   )"
  apply(drule knows_cases_raw)
  apply(erule disjE)
  apply(rule disjI1, rule nextRel_FromIK0D)
  apply(simp add: next_def)
  apply(erule disjE)
  apply(rule disjI2, rule disjI1)
  apply(clarify)
  apply(drule next_imp_less)
  apply(frule in_set_less1)
  apply(force dest: Knows_before_inp)
  apply(erule disjE)
  apply(rule disjI2, rule disjI2, rule disjI1)
  apply(clarify)
  apply(drule next_imp_less)
  apply(frule in_set_less1)
  apply(force dest: Knows_before_inp)
  apply(erule disjE)
  apply(rule disjI2, rule disjI2, rule disjI2, rule disjI1)
  apply(clarify)
  apply(drule next_imp_less)
  apply(frule in_set_less1)
  apply(force dest: Knows_before_inp)
  apply(rule disjI2)+
  apply(auto dest!: next_imp_less intro!: fromMsg_raw_imp_fromMsg)
  done

lemmas Knows_less_cases = knows_cases[OF in_set_less1, rule_format]


lemma Recv_before_Send:
  "\<lbrakk> \<Delta> MkStep tid (Send l msg) \<prec> \<star> m; eruns r tid R; 
     (Recv l' msg', Send l msg) \<in> roleOrd R \<rbrakk> \<Longrightarrow>
   \<star> subst s (s2e msg' tid) \<prec> \<star> m"
  apply(clarsimp simp: eruns_def roleOrd_def split: option.splits)
  apply(erule disjE)
  apply(drule roleOrd)
  apply(simp)
  apply(frule_tac x="\<Delta> MkStep tid (Recv l' msg')" in in_set_less1)
  apply(force dest: Knows_before_inp)
  apply(auto dest!: in_set_less1 in_set_listOrd2 todo_notin_trace)
  done

(*

(* OLD Developments *)


lemma listOrd_in_listOrdD: "x \<sqsubset>\<^bsub>t\<^esub> y \<Longrightarrow> (x,y) \<in>listOrd t"
  by(induct t arbitrary: x y, simp, case_tac t, auto)

lemma listOrd_distinct_conv_predOrd: 
  "distinct t \<Longrightarrow> listOrd t = {(x, y) |x y. x \<sqsubset>\<^bsub>t\<^esub> y}\<^sup>+"
  apply(rule set_ext, auto)
  apply(induct t rule: listOrd.induct)
  apply(simp)
  apply(simp)
  apply(erule disjE)
  apply(clarify)
  apply(case_tac "xs")
  apply(simp)
  apply(simp)
  apply(erule disjE)
  apply(rule trancl.intros)
  apply(simp)
  apply(rule trancl_trans)
  apply(rule trancl.intros)
  apply(force)
  apply(rule_tac r="{(x, y). x \<sqsubset>\<^bsub>(aa # list)\<^esub> y}" in trancl_mono)
  apply(simp)
  apply(force)
  apply(rule_tac r="{(x, y). x \<sqsubset>\<^bsub>xs\<^esub> y}" in trancl_mono)
  apply(force)
  apply(case_tac xs)
  apply(simp)
  apply(force)

  apply(erule trancl.induct)
  apply(auto dest!: predOrd_in_listOrdD intro: listOrd_distinct_trans)
  done




fun predOrd :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "predOrd []       a b = False"
| "predOrd [x]      a b = False"
| "predOrd (x#y#xs) a b = ((a = x \<and> b = y) \<or> (predOrd (y#xs) a b))"

locale partial_ord = 
  fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50) 
  assumes refl [intro, simp]: "x \<sqsubseteq> x" 
  and       anti_sym [intro]: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> x \<rbrakk> \<Longrightarrow> x = y" 
  and          trans [trans]: "\<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> z \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"

definition (in partial_ord) 
  less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubset>" 50) 
  where "(x \<sqsubset> y) = (x \<sqsubseteq> y \<and> x \<noteq> y)"
 

locale distinct_list = 
  fixes   xs :: "knevent list"
  assumes distinct: "distinct xs"

sublocale distinct_list \<subseteq> partial_ord "predOrd xs"
  apply(unfold_locales)
  apply(induct xs arbitrary: x, simp)



locale REACHABLE =
  fixes P :: proto
  and   t :: kntrace
  and   r :: "rolestep threadpool"
  and   s :: wt_subst
  assumes reachable [simp,intro!]: "(t,r,s) \<in> reachable P"

sublocale REACHABLE \<subseteq> distinct_list t
  apply(unfold_locales)
  apply(rule reachable_distinct_trace[OF reachable])
  done

context REACHABLE begin
  

lemmas distinct_trace [simp,intro!] = reachable_distinct_trace[OF reachable]

lemma knI: "\<star>(subst s m) \<in> set t \<Longrightarrow> kn (kntrace2trace t,r,s) m"
  by(auto simp: kn_def intro!: reachable_Knows_spies_kntrace2trace)

end



print_locale! REACHABLE


thm reachable
  


lemma kn_reachableI:
  "\<lbrakk> (t,r,s) \<in> reachable P; \<star>(subst s m) \<in> set t \<rbrakk>
  \<Longrightarrow> kn (kntrace2trace t,r,s) m"
  by(simp add: kn_def reachable_Knows_spies_kntrace2trace)


lemma st_conv_kntrace:
  "st (kntrace2trace t,r,s) (tid,step) =  
   (\<Delta>(MkStep tid step) \<in> set t)"
  by(simp add: st_def)



(* MOVE *)

syntax "@listOrd" :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" 
       ("_ \<prec>\<^bsub>_\<^esub>/ _" [900, 900, 900] 900)

thm listOrd_def

translations
  "x \<prec>\<^bsub>t\<^esub> y" == "(x,y) \<in> ListOrd.listOrd t"


lemma stepOrd_conv_kntrace:
  "((tid,step) \<prec>\<^bsub>kntrace2trace t\<^esub> (tid',step')) =
   (\<Delta>(MkStep tid step) \<prec>\<^bsub>t\<^esub>  \<Delta>(MkStep tid' step'))"
  by(induct t rule: kntrace2trace.induct, auto)

*)

end

end
