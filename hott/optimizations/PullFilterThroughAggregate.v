Require Import HoTT. 
Require Import UnivalenceAxiom. 
Require Import HoTTEx. 
Require Import Denotation. 
Require Import UnivalentSemantics. 
Require Import AutoTactics. 
Require Import CQTactics. 
 
Open Scope type. 
 
Module Optimization (T : Types) (S : Schemas T) (R : Relations T S)  (A : Aggregators T S). 
  Import T S R A. 
  Module SQL_TSRA := SQL T S R A. 
  Import SQL_TSRA. 
  Module AutoTac := AutoTactics T S R A. 
  Import AutoTac. 
  Module CQTac := CQTactics T S R A. 
  Import CQTac. 
 
  Notation combine' := combineGroupByProj.
 
  Parameter count : forall {T}, aggregator T int. 
  Notation "'COUNT' ( e )" := (aggregatorGroupByProj count e). 
  Parameter sum : forall {T}, aggregator T int. 
  Notation "'SUM' ( e )" := (aggregatorGroupByProj sum e). 
  Parameter max : forall {T}, aggregator T int. 
  Notation "'MAX' ( e )" := (aggregatorGroupByProj max e). 
  Parameter min : forall {T}, aggregator T int. 
  Notation "'MIN' ( e )" := (aggregatorGroupByProj min e). 
  Parameter avg : forall {T}, aggregator T int. 
  Notation "'AVG' ( e )" := (aggregatorGroupByProj avg e).
 
  Parameter gt: Pred (node (leaf int) (leaf int)). 
 
  Variable integer_5000: constant int. 


  Definition Rule: Type. 
    refine (forall ( Γ scm_t scm_account scm_bonus scm_dept scm_emp: Schema) (rel_t: relation scm_t) (rel_account: relation scm_account) (rel_bonus: relation scm_bonus) (rel_dept: relation scm_dept) (rel_emp: relation scm_emp) (t_k0 : Column int scm_t) (t_c1 : Column int scm_t) (t_f1_a0 : Column int scm_t) (t_f2_a0 : Column int scm_t) (t_f0_c0 : Column int scm_t) (t_f1_c0 : Column int scm_t) (t_f0_c1 : Column int scm_t) (t_f1_c2 : Column int scm_t) (t_f2_c3 : Column int scm_t) (account_acctno : Column int scm_account) (account_type : Column int scm_account) (account_balance : Column int scm_account) (bonus_ename : Column int scm_bonus) (bonus_job : Column int scm_bonus) (bonus_sal : Column int scm_bonus) (bonus_comm : Column int scm_bonus) (dept_deptno : Column int scm_dept) (dept_name : Column int scm_dept) (emp_empno : Column int scm_emp) (emp_ename : Column int scm_emp) (emp_job : Column int scm_emp) (emp_mgr : Column int scm_emp) (emp_hiredate : Column int scm_emp) (emp_comm : Column int scm_emp) (emp_sal : Column int scm_emp) (emp_deptno : Column int scm_emp) (emp_slacker : Column int scm_emp), _). 
    refine (⟦ Γ ⊢ DISTINCT (SELECT1 (combine (right⋅left) (combine (right⋅right⋅left) (right⋅right⋅right))) FROM1 ((SELECT1 (combine (right⋅emp_ename) (combine (right⋅emp_sal) (right⋅emp_deptno))) FROM1 (table rel_emp) )) WHERE (castPred (combine (right⋅right⋅left) (e2p (constantExpr integer_5000)) ) gt)) : _ ⟧ =  ⟦ Γ ⊢ (SELECT1 (combine (right⋅left) (combine (right⋅right⋅left) (right⋅right⋅right))) FROM1 (DISTINCT (SELECT1 (combine (right⋅emp_ename) (combine (right⋅emp_sal) (right⋅emp_deptno))) FROM1 (table rel_emp) )) WHERE (castPred (combine (right⋅right⋅left) (e2p (constantExpr integer_5000)) ) gt)) : _ ⟧). 
  Defined. 
  Arguments Rule /.      
  
  Definition hprop_prod_trunc {A B} `{IsHProp A}:
    A * Trunc(-1) B <~> Trunc(-1) (A * B).
    apply equiv_iff_hprop_uncurried.
    constructor.
    + intros [a b].
      strip_truncations.
      apply tr.
      exact (a, b).
    + intros ab.
      strip_truncations.
      destruct ab as [a b].
      refine (a, tr b).
  Defined.

  Definition hprop_prod_trunc_r {A B} `{IsHProp B}:
    Trunc (-1) A * B <~> Trunc(-1) (A * B).
    apply equiv_iff_hprop_uncurried.
    constructor.
    + intros [a b].
      strip_truncations.
      apply tr.
      exact (a, b).
    + intros ab.
      strip_truncations.
      destruct ab as [a b].
      refine (tr a, b).
  Defined.
  
  Definition hprop_prod_trunc_in_sig {A:Type} {B: A -> hProp} {C D: A -> Type}:
    {a:A & B a * Trunc (-1) (C a) * D a} <~> {a:A & Trunc (-1) (B a * C a) * D a}.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried hprop_prod_trunc).
    reflexivity.
  Defined.

  Definition hprop_prod_trunc_in_sig_r {A:Type} {B: A -> Type} {C: A -> hProp}:
    {a:A & Trunc (-1) (B a) * C a} <~> {a:A & Trunc (-1) (B a * C a)}.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried hprop_prod_trunc_r).
    reflexivity.
  Defined.

  Definition equiv_sig_break_pair_f {A B C D} `{IsHSet A} `{IsHSet C} `{IsHSet D}:
  forall (f: A -> C * D) (t:C * D), {a: A & B a * (f a = t)} = {a: A & B a * ((fst (f a)) = fst t) * ((snd (f a)) = snd t)}.
  intros.
  f_ap.
  by_extensionality a.
  rewrite (path_universe_uncurried (equiv_pair_assemble _)).
  rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
  reflexivity.
Defined.
  
  Lemma ruleStand: Rule.
    start.
    destruct t as [t1 [t2 t3]].
    rewrite (path_universe_uncurried hprop_prod_trunc_in_sig).
    rewrite (path_universe_uncurried (equiv_sigma_eq_subst' (t1, (t2, t3)))).
    rewrite (path_universe_uncurried (equiv_sigma_eq_subst' (t1, (t2, t3)))).
    reflexivity.
  Qed. 
 
End Optimization. 
