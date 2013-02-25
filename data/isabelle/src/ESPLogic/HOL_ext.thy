(*****************************************************************************
 * ESPL --- an embedded security protocol logic
 *          http://people.inf.ethz.ch/meiersi/espl/
 *
 *   Copyright (c) 2009-2011, Simon Meier, ETH Zurich, Switzerland
 *
 * All rights reserved. See file LICENCE for more information.
 ******************************************************************************)
(* Extensions to the standard HOL library *)
theory HOL_ext
imports
  Main
begin


section{* Maps *}

lemma dom_upd [simp]: 
  "dom (\<lambda> a. if a = x then Some y else m a) = insert x (dom m)"
  by(fastforce simp: dom_if)

lemma map_leD: "\<lbrakk> m \<subseteq>\<^sub>m m'; m x = Some y \<rbrakk> \<Longrightarrow> m' x = Some y"
  by(force simp: map_le_def)

lemma rev_map_leD: "\<lbrakk>  m x = Some y; m \<subseteq>\<^sub>m m' \<rbrakk> \<Longrightarrow> m' x = Some y"
  by(force simp: map_le_def)

lemma map_leI: 
  "\<lbrakk> \<And> x y. m x = Some y \<Longrightarrow> m' x = Some y \<rbrakk> \<Longrightarrow>  m \<subseteq>\<^sub>m m'"
  by(force simp: map_le_def)

section{* Finite Sets *}

text{* 
  Automating the simplification of differences of finite sets. 
*}
lemma eq_conj_neq: 
  "y \<noteq> z \<Longrightarrow> (x = y \<and> x \<noteq> z) = (x = y)"
  "y \<noteq> z \<Longrightarrow> (x = y \<and> (x \<noteq> z \<and> P)) = ((x = y) \<and> P)"
  "y \<noteq> z \<Longrightarrow> (x = y \<and> (P \<and> x \<noteq> z)) = ((x = y) \<and> P)"
  "y \<noteq> z \<Longrightarrow> (x \<noteq> z \<and> x = y) = (x = y)"
  "y \<noteq> z \<Longrightarrow> ((x \<noteq> z \<and> P) \<and> x = y) = ((x = y) \<and> P)"
  "y \<noteq> z \<Longrightarrow> ((P \<and> x \<noteq> z) \<and> x = y) = ((x = y) \<and> P)"
  by(auto)

lemmas finite_setdiff_compute =
  conj_disj_distribL 
  conj_disj_distribR 
  ex_disj_distrib
  eq_conj_neq
  disj_ac


subsection{* Extensions to ML infrastructure for HOL *}

lemma HOL_concl_revcut_rl:
  "\<lbrakk> PROP V; PROP V \<Longrightarrow> W \<rbrakk> \<Longrightarrow> W"
  by simp


ML{*
signature HOL_EXT =
sig
  (* Gather bound variables *)
  val add_bound_list : term -> int list -> int list

  (* Permutations of all quantifiers *)
  val invert_perm : int list -> int list
  val forall_permute : Proof.context -> int list -> cterm -> thm
  val forall_permute_conv : Proof.context -> int list -> cterm -> thm

  (* Theorem modifications *)
  val beta_norm_thm : thm -> thm
  val make_HOL_elim : thm -> thm
  val protect_concl : thm -> thm
  val lift_ground_thm_mod 
    : Proof.context -> (Proof.context -> thm -> thm) -> thm -> thm

  (* Applying tactics to theorems *)
  val rule_by_tactic 
    : Proof.context -> (Proof.context -> thm -> thm Seq.seq) -> thm -> thm
  val refine_rule 
    : Proof.context -> (Proof.context -> thm -> thm Seq.seq) -> thm -> thm
  val track_HOL_term 
    : Proof.context -> term -> (thm * (thm -> thm)) * Proof.context
end;

*}

ML{*

structure HOL_Ext: HOL_EXT =
struct

(* gather a list of bound variables *)
val add_bound_list =
  (fn f => rev o f) o fold_aterms (fn Bound i => (fn is => i::is) | _ => I);


(* invert a permutation *)
fun invert_perm p =
  p ~~ (0 upto (length p - 1))
  |> sort (int_ord o pairself fst)
  |> map snd


(* Prove the permutation of the outermost all quantifiers:
 
   !!x0 .. x(n-1). A |- !!x[p0] .. x[p(n-1)]. A

   PRE: No meta-variables in the given cterm.
*)
fun forall_permute ctxt p ct =
  let
    val cert = Thm.cterm_of (Proof_Context.theory_of ctxt);
    fun mk_cv (_, ty) n = cert (Free (n, ty));
    val string_of_perm = commas o map string_of_int;
    fun err msg = raise CTERM
      ( "forall_permute: " ^ msg ^ " [" ^ string_of_perm p ^ "]"
      , [ct] );

    val t = Thm.term_of ct;
    val n = length p;
    val vs = t |> Term.strip_all_vars |> #1 o chop n;

    val () = if n <> length vs
             then err "too many variables referenced"
             else ();

    val (vns', _) = Variable.variant_fixes (map fst vs) ctxt;
    val cvs'  = map2 mk_cv vs vns';
    val cpvs' = 
      map (nth cvs') p
      handle Subscript => err "wrong subscript in permutation";
  in
    ct
    |> Thm.assume
    |> forall_elim_list cvs'
    |> forall_intr_list cpvs'
  end

(* Prove the conversion permuting the variables:

   (!!x0 .. x(n-1). A) == (!!x[p0] .. x[p(n-1)]. A)
*)
fun forall_permute_conv ctxt p ct =
  let
    val lr  = forall_permute ctxt p ct;
    val ct' = Thm.cprop_of lr;
    val rl  = forall_permute ctxt (invert_perm p) ct';
  in
    Thm.equal_intr (Thm.implies_intr ct  lr) 
                   (Thm.implies_intr ct' rl)
  end;


(* Beta-normal form of a theorem *)
fun beta_norm_thm th =
  Thm.equal_elim (Thm.beta_conversion true (Thm.cprop_of th)) th

(* make an elim rule with a "Trueprop ?R" concluion *)
fun make_HOL_elim rl = 
  zero_var_indexes (rl RS @{thm HOL_concl_revcut_rl})


(*
  A ==> ... ==>  C
  ---------------- (protect_concl)
  A ==> ... ==> #C
*)
fun protect_concl th = 
  Drule.comp_no_flatten (th, Thm.nprems_of th) 1 Drule.protectI;


(* Modify a theorem using a function thm -> thm that requires the theorem
   to contain no schematic variables.
*)
fun lift_ground_thm_mod ctxt f th =
  let
    val ((_, [th']), ctxt') = Variable.import true [th] ctxt;
  in
    f ctxt' th'
    |> singleton (Variable.export ctxt' ctxt)
    |> zero_var_indexes
  end;


(*Makes a rule by applying a tactic to an existing rule.

  Copied from 'tactic.ML' and fixed such that the current context
  is taken as an argument to avoid clashes with free variables referenced 
  by facts used by the tactic.
*)
fun rule_by_tactic ctxt tac rl =
  lift_ground_thm_mod ctxt 
    (fn ctxt' => fn st => 
       case Seq.pull (tac ctxt' st) of
         NONE => raise THM ("rule_by_tactic", 0, [rl])
       | SOME (st', _) => st')
    rl;

(* Apply a tactic to the premises of an elim rule *)
fun refine_rule ctxt tac =
  Goal.conclude o rule_by_tactic ctxt tac o protect_concl


(* Returns a theorem of the for "Q x |- Q x" together with
   a removal function that can be used to eliminate the "Q x"
   assumption by replacing it with (\y. x = y). The given
   theorem can be used to track the conversions of "x" that
   happen when using automatic tools. Just insert the given
   theorem.
*)
fun track_HOL_term ctxt x_t =
  let
    val thy  = Proof_Context.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    val x_ty = Term.fastype_of x_t; 

    val ([Q_n],ctxt') = Variable.variant_fixes ["Q"] ctxt;
    val Q_ty = x_ty --> HOLogic.boolT;
    val Q_t  = Free (Q_n, Q_ty);
    
    val Q_ct    = cert Q_t;
    val Qx_ct   = cert (HOLogic.mk_Trueprop (Q_t $ x_t));
    val eq_x_ct = cert 
      (Abs ("y", x_ty, 
            Const (@{const_name "HOL.eq"}, x_ty --> x_ty --> HOLogic.boolT)
            $ x_t $ Bound 0));

    fun remove_tracking th' =
      th' 
      |> Thm.implies_intr Qx_ct 
      |> Thm.forall_intr Q_ct
      |> Thm.forall_elim eq_x_ct
      |> curry (op RS) @{thm refl}
      |> beta_norm_thm
  in
    ((Thm.assume Qx_ct, remove_tracking), ctxt')
  end;


end;
*}


end
