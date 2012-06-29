theory PureLogic
imports 
  Execution
  FirstOccOrd
begin

section{* Knowledge Event Traces *}

datatype knevent = "Knows" "execmsg"   ("\<star>_" [900] 900)
                 | "Event" "execevent" ("\<Delta>_" [900] 900)

types knev_trace = "knevent list"

fun injectKn :: "wt_subst \<Rightarrow> trace \<Rightarrow> knev_trace"
where
  "injectKn s []     = []"
| "injectKn s (FromIK0 m) = 
     \<Delta>(FromIK0 m) # \<star>(m) # injectKn s es"
| "injectKn s (MkStep tid (Send lbl msg)#es) = 
     \<Delta>(MkStep tid (Send lbl msg)) # 
     \<star>(subst s (spec2exec msg tid)) # 
     injectKn s es"
| "injectKn s (MkStep tid (Recv lbl msg) # es) = 
     \<Delta>(MkStep tid (Recv lbl msg)) # injectKn s es"
| "injectKn s (MkTup x y # es) = 
     \<Delta>(MkTup x y) # \<star>(Tup x y)  # injectKn s es"
| "injectKn s (MkUnt x y # es) = 
     \<Delta>(MkUnt x y) # \<star>(x) # \<star>(y) # injectKn s es"
| "injectKn s (MkEncr m k # es) = 
     \<Delta>(MkEncr m k) # \<star>(Enc m k) # injectKn s es"
| "injectKn s (MkDecr m k # es) = 
     \<Delta>(MkDecr m k) # \<star>(m) # injectKn s es"
| "injectKn s (MkHash m # es) = 
     \<Delta>(MkHash m) # \<star>(Hash m) # injectKn s es"



definition stateOrd :: "knevent \<Rightarrow> state \<Rightarrow> knevent \<Rightarrow> bool" ("_ \<prec>\<^bsub>_\<^esub>/ _" [100, 100, 100] 100)
where "stateOrd ke q ke' = (case q of (t,r,s) \<Rightarrow> 
                             (ke' \<notin> { \<star>m | m. m \<in> IK0}) \<and>
                             (ke  \<in> { \<star>m | m. m \<in> IK0} \<and> ke' \<in> set (injectKn s t) \<or>
                              (ke,ke') \<in> firstOccOrd (injectKn s t))
                           )"

definition stateKnEvs :: "state \<Rightarrow> knevent set"
where "stateKnEvs q = (case q of (t,r,s) \<Rightarrow> { \<star>m | m. m \<in> IK0} \<union> set (injectKn s t))"

lemma stateOrd_trans: "\<lbrakk> ke \<prec>\<^bsub>q\<^esub> ke'; ke' \<prec>\<^bsub>q\<^esub> ke'' \<rbrakk> \<Longrightarrow> ke \<prec>\<^bsub>q\<^esub> ke''"
  by(auto simp: stateOrd_def dest: in_set_firstOccOrd1 in_set_firstOccOrd2 intro: firstOccOrd_trans)

(* MISSSING: previous event must only be present, if later event is present 
    \<Longrightarrow> sacrifices irreflexivity 
*)

lemma stateOrd_irr: "\<not>( ke \<prec>\<^bsub>q\<^esub> ke )"
  by(auto simp: stateOrd_def intro: firstOccOrd_irr)



section{* Secrecy and Authentication Logic *}

text{* 
  This version tries to be more complete with respect to
  the operator definitions.
*}

subsection{* Abstract Events *}

fun substEv :: "wt_subst \<Rightarrow> execevent \<Rightarrow> execevent"
where
  "substEv s (MkStep tid step) = MkStep tid step"
| "substEv s (MkHash m)        = MkHash (subst s m)"
| "substEv s (MkTup x y)       = MkTup  (subst s x) (subst s y)"
| "substEv s (MkUnt x y)       = MkUnt  (subst s x) (subst s y)"
| "substEv s (MkEncr m k)      = MkEncr (subst s m) (subst s k)"
| "substEv s (MkDecr m k)      = MkDecr (subst s m) (subst s k)"

subsection{* Predicates *}


definition kn :: "state \<Rightarrow> execmsg \<Rightarrow> bool"
where "kn q m = (case q of (t,r,s) \<Rightarrow> subst s m \<in> knows s t)"

definition ev :: "state \<Rightarrow> execevent \<Rightarrow> bool"
where "ev q e \<equiv> (case q of (t,r,s) \<Rightarrow> substEv s e \<in> set t)"

definition evBev :: "execevent \<Rightarrow> state \<Rightarrow> execevent \<Rightarrow> bool" ("_/ \<triangleleft>[_]\<triangleleft>/ _" [100,100,100] 100)
where "e' \<triangleleft>[q]\<triangleleft> e = (case q of (t,r,s) \<Rightarrow>  
                      substEv s e \<in> set t \<longrightarrow>
                      (substEv s e', substEv s e) \<in> firstOccOrd t)"

definition knBev :: "execmsg \<Rightarrow> state \<Rightarrow> execevent \<Rightarrow> bool" ("_/ \<star>[_]\<triangleleft>/ _" [100,100,100] 100)
where "m \<star>[q]\<triangleleft> e = (case q of (t,r,s) \<Rightarrow>  
                      subst s m \<in> IK0 \<or>
                      (substEv s e \<in> set t \<longrightarrow>
                        (\<exists> e' \<in> set t. (e', substEv s e) \<in> firstOccOrd t \<and>
                                       subst s m \<in> eout s e'
                        )
                      )
                    )"

definition evBkn :: "execevent \<Rightarrow> state \<Rightarrow> execmsg \<Rightarrow> bool" ("_/ \<triangleleft>[_]\<star>/ _" [100,100,100] 100)
where "e \<triangleleft>[q]\<star> m = (case q of (t,r,s) \<Rightarrow>  
                      subst s m \<notin> IK0 \<and>
                      (\<forall> e' \<in> set t. subst s m \<in> eout s e' \<longrightarrow>
                                    (substEv s e, e') \<in> firstOccOrd t
                      )
                    )"

definition knBkn :: "execmsg \<Rightarrow> state \<Rightarrow> execmsg \<Rightarrow> bool" ("_/ \<star>[_]\<star>/ _" [100,100,100] 100)
where "m' \<star>[q]\<star> m = (case q of (t,r,s) \<Rightarrow>  
                       subst s m \<notin> IK0 \<and>
                       (\<forall> e \<in> set t. subst s m \<in> eout s e \<longrightarrow>
                          (\<exists> e' \<in> set t. subst s m' \<in> eout s e' \<and>
                                         (e', e) \<in> firstOccOrd t
                          )
                       )
                     )"

lemma knBkn_trans [trans]: "\<lbrakk> m \<star>[q]\<star> m'; m' \<star>[q]\<star> m'' \<rbrakk> \<Longrightarrow> m \<star>[q]\<star> m''"
  by(force simp: knBkn_def intro: firstOccOrd_trans)

lemma evBev_trans [trans]: "\<lbrakk> e \<triangleleft>[q]\<triangleleft> e'; e' \<triangleleft>[q]\<triangleleft> e'' \<rbrakk> \<Longrightarrow> e \<triangleleft>[q]\<triangleleft> e''"
  by(auto simp: evBev_def intro: firstOccOrd_trans
          dest: in_set_firstOccOrd1 in_set_firstOccOrd2)

lemma knBev_evBkn_trans: "\<lbrakk> 




lemma test: "x \<or> y \<longrightarrow> z"
  apply(rule impI)

lemma test: "f e \<triangleleft>[q]\<triangleleft> g e \<and> P"

definition learn :: "state \<Rightarrow> execevent \<Rightarrow> execmsg \<Rightarrow> bool"
where "learn q e m \<equiv> (case q of (t,r,s) \<Rightarrow>  
                       substEv s e \<in> set t \<and>                      
                       subst s m \<in> eout s (substEv s e) \<and>
                       subst s m \<notin> IK0 \<and>
                       (\<forall> e' \<in> set t. (e',substEv s e) \<in> firstOccOrd t \<longrightarrow>
                                       subst s m \<notin> eout s e')
                     )"



\<star>[q]\<star>

\<triangleleft>[q]\<star>

\<triangleleft>[q]\<triangleleft>

\<star>[q]\<triangleleft>

definition evbefore :: "state \<Rightarrow> execevent \<Rightarrow> execevent \<Rightarrow> bool"
where "evbefore q e e' \<equiv> (case q of (t,r,s) \<Rightarrow>  
                           (substEv s e, substEv s e') \<in> firstOccOrd t)"

definition knbefore :: "state \<Rightarrow> execmsg \<Rightarrow> execevent \<Rightarrow> bool"
where "knbefore q m e \<equiv> (case q of (t,r,s) \<Rightarrow> 
                          substEv s e \<in> set t \<and>
                          (subst s m \<in> IK0 \<or>
                           (\<exists> e' \<in> set t. (e',substEv s e) \<in> firstOccOrd t \<and>
                                          subst s m \<in> eout s e')
                          )
                        )"


definition runs :: "state \<Rightarrow> tid \<Rightarrow> role \<Rightarrow> bool"
where "runs q tid R \<equiv> (case q of (t,r,s) \<Rightarrow> 
                        (case r tid of
                          Some (todo,done) \<Rightarrow> Rep_role R = rev done @ todo
                        | None             \<Rightarrow> False))"

subsection{* Rules *}

subsubsection{* Simplification *}

lemma kn_simps [simp]:
  "kn q (Lit (EConst c))"
  "kn q (Lit (EHonest a))"
  "kn q (Lit (EveNonce n))"
  "kn q (SK (Lit Eve))"
  "kn q (PK (Lit (EHonest a)))"
  "kn q (K (Lit (EHonest a)) (Lit Eve))"
  "kn q (K (Lit Eve) (Lit (EHonest a)))"
  by(cases q, simp add: IK0_def kn_def knows_conv_eout image_def)+

lemma knbefore_simps:
  "ev q e \<Longrightarrow> knbefore q (Lit (EConst c)) e"
  "ev q e \<Longrightarrow> knbefore q (Lit (EHonest a)) e"
  "ev q e \<Longrightarrow> knbefore q (Lit (EveNonce n)) e"
  "ev q e \<Longrightarrow> knbefore q (SK (Lit Eve)) e"
  "ev q e \<Longrightarrow> knbefore q (PK (Lit (EHonest a))) e"
  "ev q e \<Longrightarrow> knbefore q (K (Lit (EHonest a)) (Lit Eve)) e"
  "ev q e \<Longrightarrow> knbefore q (K (Lit Eve) (Lit (EHonest a))) e"
  by(cases q, simp add: IK0_def knbefore_def image_def ev_def)+


subsubsection{* Purely Execal *}

lemma evbeforeD1: "evbefore q e1 e2 \<Longrightarrow> ev q e1"
  by(auto dest: in_set_firstOccOrd1 simp: evbefore_def ev_def)

lemma evbeforeD2: "evbefore q e1 e2 \<Longrightarrow> ev q e2"
  by(auto dest: in_set_firstOccOrd2 simp: evbefore_def ev_def)

lemma knbeforeD1: "knbefore q m e \<Longrightarrow> kn q m"
  by(auto simp: knbefore_def knows_conv_eout kn_def)

lemma knbeforeD2: "knbefore q m e \<Longrightarrow> ev q e"
  by(auto simp: knbefore_def  ev_def)

lemma learnD1: "learn q e m \<Longrightarrow> ev q e"
  by(auto simp: learn_def ev_def)

lemma learnD2: "learn q e m \<Longrightarrow> kn q m"
  by(auto simp add: learn_def knows_conv_eout kn_def)

lemma ebefore_irr: "\<not>evbefore q e e"
  by(auto simp: evbefore_def)

lemma ebefore_trans: "\<lbrakk> evbefore q e1 e2; evbefore q e2 e3 \<rbrakk> \<Longrightarrow> evbefore q e1 e3"
  by(auto simp: evbefore_def intro: firstOccOrd_trans)

lemma learn_fun: 
  "\<lbrakk> learn q e1 m; learn q e2 m \<rbrakk> 
  \<Longrightarrow> substEv (sts q) e1 = substEv (sts q) e2"
  apply(clarsimp simp: learn_def)
  by(auto dest: firstOccOrd_cases in_set_firstOccOrd1 in_set_firstOccOrd2)

lemma learn_knbefore_evbefore:
  "\<lbrakk> learn q e m; knbefore q m e' \<rbrakk> \<Longrightarrow> evbefore q e e'"
  by(auto dest: firstOccOrd_cases intro: firstOccOrd_trans
          simp: learn_def knbefore_def evbefore_def)

lemma runs_fun: "\<lbrakk> runs q tid R; runs q tid R' \<rbrakk> \<Longrightarrow> R = R'"
  by(auto simp: runs_def Rep_role_inject[symmetric] split: option.splits )

