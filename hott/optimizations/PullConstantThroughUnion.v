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
 
  Variable integer_2: constant int.
  
  Definition Rule: Type. 
    refine (forall ( Γ scm_emp: Schema) (rel_emp: relation scm_emp) (emp_empno : Column int scm_emp) (emp_ename : Column int scm_emp) (emp_job : Column int scm_emp) (emp_mgr : Column int scm_emp) (emp_hiredate : Column int scm_emp) (emp_comm : Column int scm_emp) (emp_sal : Column int scm_emp) (emp_deptno : Column int scm_emp) (emp_slacker : Column int scm_emp), _). 
    refine (⟦ Γ ⊢ ((SELECT1 (combine (e2p (constantExpr integer_2)) (combine (right⋅emp_deptno) (right⋅emp_job))) FROM1 (table rel_emp) )) UNION ALL ((SELECT1 (combine (e2p (constantExpr integer_2)) (combine (right⋅emp_deptno) (right⋅emp_job))) FROM1 (table rel_emp) )) : _ ⟧
            = ⟦ Γ ⊢ (SELECT1 (combine (e2p (constantExpr integer_2)) (combine (right⋅left) (right⋅right))) FROM1 (((SELECT1 (combine (right⋅emp_deptno) (right⋅emp_job)) FROM1 (table rel_emp) )) UNION ALL ((SELECT1 (combine (right⋅emp_deptno) (right⋅emp_job)) FROM1 (table rel_emp) ))) ) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule.
    start.
    rewrite (path_universe_uncurried equiv_sig_sum_prod_distr_r).
    rewrite <- (path_universe_uncurried (equiv_sum_sigma _ _ _)).
    f_ap.
    + symmetry.
      rewrite (equiv_sig_break_pair _ _).
      rewrite (path_universe_uncurried (equiv_sigma_eq_subst' _)).
      rewrite <- (path_universe_uncurried (equiv_prod_sigma_r _ _ _)).
      f_ap.
      by_extensionality i.
      symmetry.
      rewrite (path_universe_uncurried (equiv_pair_assemble _)).
      symmetry.
      rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
      f_ap.
      rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
      reflexivity.
    + symmetry.
      rewrite (equiv_sig_break_pair _ _).
      rewrite (path_universe_uncurried (equiv_sigma_eq_subst' _)).
      rewrite <- (path_universe_uncurried (equiv_prod_sigma_r _ _ _)).
      f_ap.
      by_extensionality i.
      symmetry.
      rewrite (path_universe_uncurried (equiv_pair_assemble _)).
      symmetry.
      rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
      f_ap.
      rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
      reflexivity. 
   Qed.
 
End Optimization. 
