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
 
  Variable integer_1: constant int. 

  Lemma sum2_pair_split {D A B C}:
    {d: D & {ab: A * B & C d ab}} <~> {d:D & {a:A & {b:B & C d (a, b)}}}.
  Proof.
  apply equiv_path.
  f_ap.
  by_extensionality d.
  exact (path_universe_uncurried sum_pair_split').
  Defined.

  Lemma sigma_path_trans_l {A B E f} `{IsHSet B}:
    forall (b c:B),
      {a:A & (b = c) * (b = f a) * E a } <~> {a:A & (b = c) * (b = f a) * (c = f a) * E a}.
  Proof.
    intros.
    apply equiv_path.
    f_ap.
    by_extensionality a0.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    symmetry.
    exact (path_universe_uncurried (path_trans b c _)).
  Defined.

 
  Lemma sigma_path_trans_l' {A B E f} `{IsHSet B}:
    forall (b c:B),
      {a:A & (b = c) * (c = f a) * E a } <~> {a:A & (b = c) * (b = f a) * (c = f a) * E a}.
  Proof.
    intros.
    apply equiv_path.
    f_ap.
    by_extensionality a0.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor;
    break_and_rewrite.
  Defined.

  Lemma sigma_prod_path_symm' {A B D} `{IsHSet B}:
    forall (b: B) (f: A -> B), {a:A & (b = f a) * D a} <~> {a:A & (f a = b) * D a}.
  Proof.
    intros.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor;
    break_and_rewrite.
  Defined.

  Lemma equiv_sigma_prod_symm_f {A B C D}:
    {a: A & B a * C a * D a} <~> {a:A & C a * B a * D a}.
  Proof.
    apply equiv_path.
    f_ap.
    by_extensionality a.    
    rewrite (path_universe_uncurried (equiv_prod_symm (B a) (C a))).
    reflexivity.
  Defined.
  
  Definition Rule: Type. 
    refine (forall ( Γ scm_dept scm_emp: Schema) (rel_dept: relation scm_dept) (rel_emp: relation scm_emp) (dept_deptno : Column int scm_dept) (dept_name : Column int scm_dept) (emp_empno : Column int scm_emp) (emp_ename : Column int scm_emp) (emp_job : Column int scm_emp) (emp_mgr : Column int scm_emp) (emp_hiredate : Column int scm_emp) (emp_comm : Column int scm_emp) (emp_sal : Column int scm_emp) (emp_deptno : Column int scm_emp) (emp_slacker : Column int scm_emp) (k1: isKey emp_empno rel_emp) (k2: isKey dept_deptno rel_dept), _). 
    refine (⟦ Γ ⊢ (SELECT1 (e2p (constantExpr integer_1)) FROM1 (product (table rel_emp) (table rel_dept)) WHERE (equal (variable (right⋅left⋅emp_deptno)) (variable (right⋅right⋅dept_deptno)))) : _ ⟧ =  ⟦ Γ ⊢ (SELECT1 (e2p (constantExpr integer_1)) FROM1 (product (table rel_emp) (product (table rel_dept) (table rel_dept))) WHERE (and (equal (variable (right⋅left⋅emp_deptno)) (variable (right⋅right⋅left⋅dept_deptno))) (equal (variable (right⋅left⋅emp_deptno)) (variable (right⋅right⋅right⋅dept_deptno))))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule. 
    start.
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried sum2_pair_split).
    simpl.
    f_ap.
    by_extensionality a.
    f_ap.
    by_extensionality b.
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (sigma_path_trans_l _ _)).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_prod_sigma_r _ _ _)).
    f_ap.
    rewrite <- (path_universe_uncurried (sigma_path_trans_l' _ _)).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite <- (path_universe_uncurried (equiv_prod_sigma _ _ _)).
    f_ap.
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_prod_sigma_r _ _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    rewrite (path_universe_uncurried (sigma_prod_path_symm' _ _)).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_f).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    specialize (k2 b).
    rewrite <- k2.
    reflexivity.
  Qed.    
    
End Optimization. 
