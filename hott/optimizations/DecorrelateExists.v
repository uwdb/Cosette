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


  Definition Rule: Type. 
    refine (forall ( Γ scm_emp: Schema) (rel_emp: relation scm_emp) (emp_empno : Column int scm_emp) (emp_ename : Column int scm_emp) (emp_job : Column int scm_emp) (emp_mgr : Column int scm_emp) (emp_hiredate : Column int scm_emp) (emp_comm : Column int scm_emp) (emp_sal : Column int scm_emp) (emp_deptno : Column int scm_emp) (emp_slacker : Column int scm_emp), _). 
    refine (⟦ Γ ⊢ (SELECT * FROM1 (table rel_emp) WHERE (EXISTS (SELECT * FROM1 (table rel_emp) WHERE (equal (variable (left⋅right⋅emp_deptno)) (variable (right⋅emp_deptno)))))) : _ ⟧ =  ⟦ Γ ⊢ (SELECT1 (right⋅left⋅star) FROM1 (product (table rel_emp) (DISTINCT (SELECT1 (combine (right⋅emp_deptno) (e2p (constantExpr integer_1))) FROM1 (table rel_emp) ))) WHERE (equal (variable (right⋅left⋅emp_deptno)) (variable (right⋅right⋅left)))) : _ ⟧). 
  Defined. 
  Arguments Rule /.
  
  Lemma ruleStand: Rule. 
    start.
    symmetry.
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    rewrite (equiv_2sigma_eq_subst' _).
    simpl.
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm).
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    rewrite equiv_2sigma_eq_subst_r'.
    rewrite equiv_sig_trunc_break_pair_f'.
    rewrite <- (path_universe_uncurried equiv_prod_2sigma_trunc_r).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    rewrite <- (path_universe_uncurried (equiv_sig_trunc_prod_hset _ _)).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_sigma_eq_subst_r' _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    f_ap.
    f_ap.
    by_extensionality b.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    rewrite (path_universe_uncurried (hset_eq_symm (denoteProj emp_deptno b) _)).
    reflexivity.
  Qed. 
 
End Optimization. 
