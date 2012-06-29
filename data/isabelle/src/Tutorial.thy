theory Tutorial
imports
  ESPLogic
begin

chapter{* A Short Tutorial on the Theories *}

text{*
  Here, we explain the differences to the presentation given in
  the submitted paper. Furthermore, we illustrate the usage of
  the Isabelle theories on the running example of the paper.

  There are two syntaxes for specifying patterns and 
  messages. For one there is the syntax given by their construction
  as algebraic datatypes. This syntax is used for specifying and
  proving inference rules and all the other infrastructure. Then,
  in the theory Syntax, we define an alternative syntax which
  is used for the definition of actual protocols and their proofs.
  We introduce this additional syntax because otherwise to shorten
  the representation of patterns and messages.
  
  The following example pattern represents the first
  message of the client role of the CR protocol in the paper.
*}

definition somePt :: pattern
where "somePt = PEnc (PFresh ''n'') (PAsymPK (PVar (AVar ''s'')))"

text{*
  The atomic sets $\textit{Const}$, $\textit{Fresh}$, and $\textit{Var}$ 
  from the paper, are represented explicitely using the constructors
  @{const PConst}, @{const PFresh}, @{const PVar}. The injection of 
*}


lemma inst_example: 
  "inst \<sigma> i somePt = Some (Enc (LN ''n'' i) (PK (\<sigma>(AV ''s'' i))))"
  unfolding somePt_def by simp

text{*
  Roles and protocols are modeled according to the types
  given in the paper. However, the assumptions about
  duplicate-freeness and no sending of message variables
  before receiving them is handled using the following
  two locales.
*}

print_locale wf_role
print_locale wf_proto

text{*
  Roles are defined using the custom ``role'' command.

  \begin{quote}\bf
    If this command doesn't work for you (outer syntax error),
    then you forgot to replace the ``isar-keywords.el'' file.
    Check the README file for instructions.
  \end{quote}

  The benefit of these commands is that they prove a number
  of simple theorems which are later used for automation. Typical
  things include distinctness of role steps in a role and no
  sending of non-received message variables. 

  Here, the running example from the paper. (Due to a name-clash
  with existing constants, we call the $C$ role client and 
  the $S$ role server.
*}

role client
where "client =
  [ Send ''1'' (PEnc (sLN ''k'') (sPK ''s''))
  , Recv ''2'' (PHash (sLN ''k''))
  ]"

thm client.unfold
thm client_1.sendStep_conv

role server
where "server =
  [ Recv ''1'' (PEnc (sLMV ''v'') (sPK ''s''))
  , Send ''2'' (PHash (sLMV ''v''))
  ]"

protocol CR
where "CR = {client,server}"

text{* 
  The role command also defines constants representing
  the individual role steps and their patterns. 
  They are labelled according
  to the label. Hence, labels must be distinct for these
  constants to be definable. For example @{const client_1} is
  the first role step of the @{const client} role. @{const client_1_pt} 
  is the pattern of this role step.

  The protocol definition command also introduces a locale CR\_state
  that provides a convenient way for proving theorems under
  the assumption that @{term "(t,r,s)"} is a reachable state.
  The construction is based on the
  function @{const reachable} (cf. ExecutionModel.thy).
  Most theorems are derived under the assumption that
  we are reasoning about a reachable state of some 
  protocol $P$. In Isabelle, we model this using the
  following locale.
*}

print_locale reachable_state

text{* We adapt notation a bit more to the paper.*}

abbreviation (in reachable_state) "th \<equiv> r"
abbreviation (in reachable_state) "tr \<equiv> t"
abbreviation (in reachable_state) "\<sigma> \<equiv> s"
abbreviation (in reachable_state) "role \<equiv> roleMap"

text{*
  Note that the naming convention is a bit different from
  the paper. The default reachable state is $(t,r,s)$ which
  corresponds to the reachable state $(tr,th,\<sigma>)$ in the
  paper.

  The functions @{const knows} and @{const steps} are defined
  as in the paper. The event order relation is modelled by
  the function @{const predOrd}. In the locale 
  reachable\_state it is abbreviated as $\prec$. The
  inference rules are derived in the theory InferenceRules.
  As an example, we show the chain rule.
*}

lemma (in reachable_state) chain_rule:
  assumes known: "m' \<in> knows t"
  shows
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
   (\<exists> A. \<exists> a \<in> A. m' = KShr A \<and> LKR (Lit (EAgent a)) \<prec> Ln m')
   "
  using known by (rule knows_cases_raw)

text{*
  Note that learn events have to be represented explicitely.
  We are using the constructors @{const St} for step events
  and @{const Ln} for learn events. Basic learn events are
  marked with @{const Step} and @{const Learns}. The confusion
  with respect to the paper version comes from the desire
  to have short names.
*}

text{* 
  Weak atomicity is a special type invariant defined
  in the WeakTyping theory. We prove that every reachable state
  of the @{const CR} is also weakly atomic by specifying 
  the following type invariant.
*}


type_invariant atomic_CR for CR
where "atomic_CR = weakly_atomic"

(* declare (in CR_state) event_predOrdI[intro] *)

sublocale CR_state \<subseteq> atomic_CR_state
proof -
  have "(tr, th, \<sigma>) \<in> approx weakly_atomic"
  proof(cases rule: reachable_in_approxI_ext
         [OF monoTyp_weakly_atomic, completeness_cases_rule])
    case (server_1_v tr th \<sigma> tid)
    then interpret state: atomic_CR_state tr th \<sigma>
      by unfold_locales auto
    show ?case using server_1_v
      by (sources "Enc (\<sigma> (MV ''v'' tid)) (PK (\<sigma> (AV ''s'' tid)))") 
         (auto intro: event_predOrdI)
  qed
  thus "atomic_CR_state tr th \<sigma>" by unfold_locales simp
qed

text{*
  We can now use the "sources" method to prove security
  properties for reachable states of the @{const CR} protocol.
*}

lemma (in CR_state) nonce_after_lkr:
  assumes asms: 
    "role th i = Some client"
    "LN ''k'' i \<in> knows tr"
  shows "LKR (\<sigma>(AV ''s'' i)) \<prec>  Ln (LN ''k'' i)" (is "?lkrbef")
using asms
proof(sources "LN ''k'' i")
  case client_1_k
   thus "?thesis" by(sources "SK (\<sigma> (AV ''s'' i))") auto
thm noteStep_def
qed

lemma (in CR_state) client_k_secrecy:
  assumes asms:
    "role th i = Some client"
    "RLKR (\<sigma>(AV ''s'' i)) \<notin> reveals tr"
  shows  "LN ''k'' i \<notin> knows tr"
using asms
by(auto dest!: nonce_after_lkr intro: compr_predOrdI)

lemma (in CR_state) client_k_secrecy_old:
  assumes asms:
    "role th i = Some client"
    "LN ''k'' i \<in> knows tr"
    "RLKR (\<sigma>(AV ''s'' i)) \<notin> reveals tr"
  shows "False"
using asms
proof(sources "LN ''k'' i")
  case client_1_k thus False by  (sources "SK (\<sigma> (AV ''s'' i))") (auto intro: compr_predOrdI)
qed

lemma (in CR_state) client_nisynch:
  assumes asms:  "(i, client_2) \<in> steps tr"
                  "roleMap th i = Some client"
  and reveal_after: "\<sigma>(AV ''s'' i) \<in> lkreveals tr \<Longrightarrow> St (i, client_2) \<prec> LKR (\<sigma>(AV ''s'' i))"
  shows
    "\<exists> j. role th j = Some server \<and>
          \<sigma>(AV ''s'' i) = \<sigma>(AV ''s'' j) \<and>
          LN ''k'' i = s(MV ''v'' j) \<and>
          St(i, client_1) \<prec> St (j, server_1) \<and>
          St(j, server_2) \<prec> St (i, client_2)" (is "?syncWith")
proof -
  note_prefix_closed facts = asms
  thus ?thesis
  proof(sources! "Hash (LN ''k'' i)")
    case fake
      thus "?thesis" using facts and reveal_after 
        apply -
        apply(frule_tac x = "LN ''k'' i" in in_knows_predOrd1)

        apply(frule nonce_after_lkr)
          apply(assumption)
        apply(frule_tac x = "\<sigma> (AV ''s'' i)" in in_lkreveals_predOrd1)
        apply(simp)
      done
  next
    case (server_2_hash j)
      note facts_s2h = this 
      thus "?thesis" using facts and reveal_after 
        proof (sources! "Enc (\<sigma> (MV ''v'' j)) (PK (\<sigma> (AV ''s'' j)))")
         case fake 
           thus "?thesis" using facts and facts_s2h and reveal_after
             apply -
             apply(frule_tac x = "\<sigma> (MV ''v'' j)"  in in_knows_predOrd1)
             apply(frule nonce_after_lkr)
               apply(simp)
             apply(frule in_lkreveals_predOrd1)
             apply(simp)
           done
       next           
         case client_1_enc thus "?thesis" using facts_s2h and facts and reveal_after by auto
       qed
  qed
qed 
         

text{*
  Please note that the easiest way to construct machine-checked
  security proofs is to use the 'scyther-proof' tool, as described
  in the accompanying README file.

  The only exception are security proofs with respect to compromising
  adversaries, as described in Martin Schaub, ``Efficient Interactive
  Construction of Machine-Checked Protocol Security Proofs in the Context of
  Dynamically Compromising Adversaries''. Master Thesis. ETH Zurich, 2011.
  See the corresponding publication in the 'publications' directory and
  the corresponding examples in 'compromising_adversaries'.
*}


end



  
  
