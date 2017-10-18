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
 
  Variable integer_10: constant int. 


  Definition Rule: Type. 
    refine (forall ( Γ scm_dept scm_emp: Schema) (rel_dept: relation scm_dept) (rel_emp: relation scm_emp) (dept_deptno : Column int scm_dept) (dept_name : Column int scm_dept) (emp_empno : Column int scm_emp) (emp_ename : Column int scm_emp) (emp_job : Column int scm_emp) (emp_mgr : Column int scm_emp) (emp_hiredate : Column int scm_emp) (emp_comm : Column int scm_emp) (emp_sal : Column int scm_emp) (emp_deptno : Column int scm_emp) (emp_slacker : Column int scm_emp), _). 
    refine (⟦ Γ ⊢ (SELECT * FROM1 ((SELECT1 (combine (right⋅right⋅dept_deptno) (right⋅left⋅emp_ename)) FROM1 (product (table rel_emp) (table rel_dept)) WHERE (and (equal (variable (right⋅left⋅emp_deptno)) (variable (right⋅right⋅dept_deptno))) (equal (variable (right⋅right⋅dept_deptno)) (constantExpr integer_10))))) WHERE (equal (variable (right⋅left)) (constantExpr integer_10))) : _ ⟧ =  ⟦ Γ ⊢ (SELECT1 (combine (right⋅right⋅dept_deptno) (right⋅left⋅emp_ename)) FROM1 (product (table rel_emp) ((SELECT * FROM1 (table rel_dept) WHERE (equal (variable (right⋅dept_deptno)) (constantExpr integer_10))))) WHERE (equal (variable (right⋅left⋅emp_deptno)) (variable (right⋅right⋅dept_deptno)))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 

  Definition eq_prod_trans {A} `{IsHSet A}:
    forall a b c:A, (a = b) * (a = c) <~> (a = b) * (a = c) * (c = b). 
    intros.
    apply equiv_iff_hprop_uncurried.
    constructor.
    + intros.
      destruct X as [x1 x2].
      destruct x1.
      repeat constructor;
      first [ simp_solve | symmetry; simp_solve].
    + intros.
      destruct X as [[x1 x2] x3].
      destruct x1.
      constructor;
      simp_solve.
  Defined.
    
  Lemma ruleStand: Rule. 
    start.
    rewrite (path_universe_uncurried (equiv_prod_sigma _ _ _)).
    f_ap.
    by_extensionality i.
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    destruct i.
    destruct t.
    simpl.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    repeat rewrite <- (path_universe_uncurried (equiv_path_prod _ _)).
    simpl.
    repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (eq_prod_trans _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    symmetry.
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    reflexivity.
  Qed. 
 
End Optimization. 
