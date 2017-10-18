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
 

  Variable str_foo_: constant int. 

  Definition Rule: Type. 
    refine (forall ( Γ scm_dept scm_emp: Schema) (rel_dept: relation scm_dept) (rel_emp: relation scm_emp) (dept_deptno : Column int scm_dept) (dept_name : Column int scm_dept) (emp_empno : Column int scm_emp) (emp_ename : Column int scm_emp) (emp_job : Column int scm_emp) (emp_mgr : Column int scm_emp) (emp_hiredate : Column int scm_emp) (emp_comm : Column int scm_emp) (emp_sal : Column int scm_emp) (emp_deptno : Column int scm_emp) (emp_slacker : Column int scm_emp), _). 
    refine (⟦ Γ ⊢ (SELECT1 (right⋅left⋅emp_ename) FROM1 (product (table rel_emp) (product (table rel_dept) (table rel_emp))) WHERE (and (and (equal (variable (right⋅left⋅emp_deptno)) (variable (right⋅right⋅left⋅dept_deptno))) (equal (variable (right⋅right⋅left⋅dept_deptno)) (variable (right⋅right⋅right⋅emp_deptno)))) (equal (variable (right⋅right⋅left⋅dept_name)) (constantExpr str_foo_)))) : _ ⟧ =  ⟦ Γ ⊢ (SELECT1 (right⋅left⋅emp_ename) FROM1 (product (table rel_emp) (product ((SELECT * FROM1 (table rel_dept) WHERE (equal (variable (right⋅dept_name)) (constantExpr str_foo_)))) (table rel_emp))) WHERE (and (equal (variable (right⋅left⋅emp_deptno)) (variable (right⋅right⋅left⋅dept_deptno))) (equal (variable (right⋅right⋅left⋅dept_deptno)) (variable (right⋅right⋅right⋅emp_deptno))))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule. 
    start.
    f_ap.
    by_extensionality t0.
    destruct t0 as [a [b c]].
    simpl.
    f_ap.
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    reflexivity.
  Qed. 
 
End Optimization. 
