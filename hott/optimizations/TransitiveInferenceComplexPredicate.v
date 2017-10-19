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
  Variable integer_2: constant int. 
  Variable integer_7: constant int. 


  Definition Rule: Type. 
    refine (forall ( Γ scm_t scm_account scm_bonus scm_dept scm_emp: Schema) (rel_t: relation scm_t) (rel_account: relation scm_account) (rel_bonus: relation scm_bonus) (rel_dept: relation scm_dept) (rel_emp: relation scm_emp) (t_k0 : Column int scm_t) (t_c1 : Column int scm_t) (t_f1_a0 : Column int scm_t) (t_f2_a0 : Column int scm_t) (t_f0_c0 : Column int scm_t) (t_f1_c0 : Column int scm_t) (t_f0_c1 : Column int scm_t) (t_f1_c2 : Column int scm_t) (t_f2_c3 : Column int scm_t) (account_acctno : Column int scm_account) (account_type : Column int scm_account) (account_balance : Column int scm_account) (bonus_ename : Column int scm_bonus) (bonus_job : Column int scm_bonus) (bonus_sal : Column int scm_bonus) (bonus_comm : Column int scm_bonus) (dept_deptno : Column int scm_dept) (dept_name : Column int scm_dept) (emp_empno : Column int scm_emp) (emp_ename : Column int scm_emp) (emp_job : Column int scm_emp) (emp_mgr : Column int scm_emp) (emp_hiredate : Column int scm_emp) (emp_comm : Column int scm_emp) (emp_sal : Column int scm_emp) (emp_deptno : Column int scm_emp) (emp_slacker : Column int scm_emp), _). 
    refine (⟦ Γ ⊢ (SELECT1 (e2p (constantExpr integer_1)) FROM1 (product ((SELECT * FROM1 (table rel_emp) WHERE (and (and (castPred (combine (right⋅emp_deptno) (e2p (constantExpr integer_7)) ) gt) (equal (variable (right⋅emp_comm)) (variable (right⋅emp_deptno)))) (castPred (combine (e2p (binaryExpr add_ (variable (right⋅emp_comm)) (variable (right⋅emp_deptno)))) (e2p (binaryExpr divide_ (variable (right⋅emp_comm)) (constantExpr integer_2))) ) gt)))) ((SELECT * FROM1 (table rel_emp) WHERE (equal (variable (right⋅emp_sal)) (variable (right⋅emp_deptno)))))) WHERE (equal (variable (right⋅left⋅emp_deptno)) (variable (right⋅right⋅emp_deptno)))) : _ ⟧ =  ⟦ Γ ⊢ (SELECT1 (e2p (constantExpr integer_1)) FROM1 (product ((SELECT * FROM1 (table rel_emp) WHERE (and (and (castPred (combine (right⋅emp_deptno) (e2p (constantExpr integer_7)) ) gt) (equal (variable (right⋅emp_comm)) (variable (right⋅emp_deptno)))) (castPred (combine (e2p (binaryExpr add_ (variable (right⋅emp_comm)) (variable (right⋅emp_deptno)))) (e2p (binaryExpr divide_ (variable (right⋅emp_comm)) (constantExpr integer_2))) ) gt)))) ((SELECT * FROM1 ((SELECT * FROM1 (table rel_emp) WHERE (equal (variable (right⋅emp_sal)) (variable (right⋅emp_deptno))))) WHERE (castPred (combine (right⋅emp_deptno) (e2p (constantExpr integer_7)) ) gt)))) WHERE (equal (variable (right⋅left⋅emp_deptno)) (variable (right⋅right⋅emp_deptno)))) : _ ⟧). 
  Defined. 
  Arguments Rule /.   
  
  Definition path_trans_in_prod {A B} `{IsHSet A}:
    forall (a b c:A), B * (a = b) * (a = c) <~> B * (a = b) * (a = c) * (b = c).
    intros a b c.
    apply equiv_path.
    repeat rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    f_ap.
    repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    exact (path_universe_uncurried (path_trans _ _ _)).
  Defined.
  
  Lemma ruleStand: Rule. 
    start.
    f_ap.
    by_extensionality t0.
    destruct t0 as [a b].
    simpl.
    f_ap.
    repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    f_ap.
    f_ap.
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    symmetry.
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor; break_and_rewrite.
  Qed. 
 
End Optimization. 
