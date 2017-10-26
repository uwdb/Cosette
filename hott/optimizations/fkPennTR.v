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
 
  Variable str_security_: constant int. 

  Definition Rule: Type. 
    refine (forall ( Γ scm_payroll scm_teams scm_depts: Schema) (rel_payroll: relation scm_payroll) (rel_teams: relation scm_teams) (rel_depts: relation scm_depts) (payroll_pdept : Column int scm_payroll) (payroll_empl : Column int scm_payroll) (teams_tproj : Column int scm_teams) (teams_tmember : Column int scm_teams) (depts_dname : Column int scm_depts) (depts_dproj : Column int scm_depts) (k: isKey payroll_empl rel_payroll) (fk: fKey payroll_empl teams_tmember rel_payroll rel_teams k), _). 
    refine (⟦ Γ ⊢ (SELECT1 (right⋅right⋅teams_tmember) FROM1 (product (table rel_depts) (table rel_teams)) WHERE (and (equal (variable (right⋅left⋅depts_dproj)) (variable (right⋅right⋅teams_tproj))) (equal (variable (right⋅left⋅depts_dname)) (constantExpr str_security_)))) : _ ⟧ =  ⟦ Γ ⊢ (SELECT1 (right⋅left⋅right⋅right) FROM1 (product ((SELECT1 (combine (right⋅left⋅depts_dname) (combine (right⋅left⋅depts_dproj) (right⋅right⋅payroll_empl))) FROM1 (product (table rel_depts) (table rel_payroll)) WHERE (equal (variable (right⋅left⋅depts_dname)) (variable (right⋅right⋅payroll_pdept))))) ((SELECT1 (combine (right⋅left⋅teams_tmember) (combine (right⋅right⋅payroll_pdept) (right⋅left⋅teams_tproj))) FROM1 (product (table rel_teams) (table rel_payroll)) WHERE (equal (variable (right⋅left⋅teams_tmember)) (variable (right⋅right⋅payroll_empl)))))) WHERE (and (and (and (equal (variable (right⋅left⋅left)) (constantExpr str_security_)) (equal (variable (right⋅left⋅right⋅left)) (variable (right⋅right⋅right⋅right)))) (equal (variable (right⋅left⋅right⋅right)) (variable (right⋅right⋅left)))) (equal (variable (right⋅left⋅left)) (variable (right⋅right⋅right⋅left))))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule.
    start.
    symmetry. (* work on the original RHS *)
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried sum_pair_split').
    simpl.
    repeat rewrite <- (path_universe_uncurried equiv_3sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_prod_3sigma).
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    rewrite equiv_2sigma_eq_subst. (*remove 1st layer of sigma *)
    rewrite (path_universe_uncurried sum_pair_split').
    repeat rewrite (path_universe_uncurried equiv_3sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_3sigma_prod_symm).
    rewrite (path_universe_uncurried equiv_prod_3sigma).
    rewrite equiv_2sigma_eq_subst. (*remove 2nd layer of sigma *)
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    repeat rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite equiv_2sigma_eq_subst.  (*remove 3rd layer of sigma *)
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    rewrite equiv_2sigma_eq_subst_r. (*remove 4th layer of sigma *)
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    rewrite equiv_2sigma_eq_subst_r. (*remove 5th layer of sigma *)
    rewrite (path_universe_uncurried equiv_prod_2sigma_l).
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc).
    repeat rewrite equiv_2sigma_break_pair.
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    rewrite equiv_2sigma_eq_subst_r'. (*remove 6th layer of sigma *)
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried sum_pair_split').
    repeat rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    simpl.
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm).
    rewrite <- (path_universe_uncurried equiv_prod_3sigma).
    rewrite (path_universe_uncurried equiv_sigma_symm_t).
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    rewrite (path_universe_uncurried sum_pair_split').
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    f_ap.
    by_extensionality b.
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite equiv_2sigma_break_pair.
    rewrite equiv_2sigma_break_pair.
    (* transitivity of equalities *)
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm_h).
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm_h).
    rewrite (path_universe_uncurried (equiv_2sigma_path_trans_l _ _ _)).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm_h).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_2sigma_prod_path_symm _ _)).
    repeat rewrite (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm).
    rewrite (path_universe_uncurried (equiv_2sigma_prod_path_symm _ _)).
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_2sigma_path_trans_l _ _ _)).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm_h).
    repeat rewrite (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    repeat rewrite (path_universe_uncurried equiv_2sigma_prod_assoc_m).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm_m).
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc_m).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm_m).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm_m).
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    rewrite <- (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (key_pred_trans_2sigma k _).
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm).
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc_m).
    rewrite <- (iskey_reduce_2sigma_func k). (* remove payroll using key *)
    unfold fKey in fk.
  Admitted.
  
End Optimization. 
