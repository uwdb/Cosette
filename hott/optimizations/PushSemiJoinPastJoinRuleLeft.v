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
 


  Definition Rule: Type. 
    refine (forall ( Γ scm_dept scm_emp: Schema) (rel_dept: relation scm_dept) (rel_emp: relation scm_emp) (dept_deptno : Column int scm_dept) (dept_name : Column int scm_dept) (emp_empno : Column int scm_emp) (emp_ename : Column int scm_emp) (emp_job : Column int scm_emp) (emp_mgr : Column int scm_emp) (emp_hiredate : Column int scm_emp) (emp_comm : Column int scm_emp) (emp_sal : Column int scm_emp) (emp_deptno : Column int scm_emp) (emp_slacker : Column int scm_emp) (ik1: isKey emp_empno rel_emp) (ik2: isKey dept_deptno rel_dept), _). 
    refine (⟦ Γ ⊢ (SELECT1 (right⋅left⋅emp_ename) FROM1 (product (table rel_emp) (product (table rel_dept) (table rel_emp))) WHERE (and (equal (variable (right⋅left⋅emp_deptno)) (variable (right⋅right⋅left⋅dept_deptno))) (equal (variable (right⋅left⋅emp_empno)) (variable (right⋅right⋅right⋅emp_empno))))) : _ ⟧ =  ⟦ Γ ⊢ (SELECT1 (right⋅left⋅emp_ename) FROM1 (product (table rel_emp) (product (table rel_dept) (product (table rel_emp) (product (table rel_dept) (table rel_emp))))) WHERE (and (and (and (equal (variable (right⋅left⋅emp_deptno)) (variable (right⋅right⋅left⋅dept_deptno))) (equal (variable (right⋅left⋅emp_empno)) (variable (right⋅right⋅right⋅left⋅emp_empno)))) (equal (variable (right⋅left⋅emp_deptno)) (variable (right⋅right⋅right⋅right⋅left⋅dept_deptno)))) (equal (variable (right⋅left⋅emp_empno)) (variable (right⋅right⋅right⋅right⋅right⋅emp_empno))))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 

  
  Lemma ruleStand: Rule. 
    start.
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried sum2_pair_split).
    rewrite (path_universe_uncurried sum2_pair_split).
    simpl.
    f_ap.
    by_extensionality d.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried sum2_pair_split).
    f_ap.
    by_extensionality b.
    unfold isKey in ik1.
    (* work on RHS *)
    symmetry.
    repeat rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm).
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm_h).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm).
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc_m).
    rewrite (path_universe_uncurried (equiv_2sigma_path_trans_reduce_r _ _ _)).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm_m).
    repeat rewrite (path_universe_uncurried equiv_2sigma_prod_assoc_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    repeat rewrite (path_universe_uncurried equiv_2sigma_prod_assoc_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm_h).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm).
    repeat rewrite (path_universe_uncurried equiv_2sigma_prod_assoc_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm_h).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm).
    repeat rewrite (path_universe_uncurried equiv_2sigma_prod_assoc_m).
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    rewrite <- (iskey_reduce_2sigma' ik2 a). (* remove one relation *)
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_f).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    repeat rewrite (path_universe_uncurried equiv_sigma_prod_assoc_h).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_f).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    repeat rewrite (path_universe_uncurried equiv_sigma_prod_assoc_h).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_f).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    repeat rewrite (path_universe_uncurried equiv_sigma_prod_assoc_h).
    rewrite <- (iskey_reduce' ik1).
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _ )).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _ )).
    f_ap.
    f_ap.
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _ )).
    rewrite (path_universe_uncurried (equiv_prod_symm (⟦ rel_dept ⟧ a) _)).
    symmetry.
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _ )).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    reflexivity.
  Qed.
  
End Optimization. 
