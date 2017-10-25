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
 
  Variable integer_0: constant int. 
  Variable integer_468: constant int. 
  
  Definition Rule: Type. 
    refine (forall ( Γ scm_itl scm_itp: Schema) (rel_itl: relation scm_itl) (rel_itp: relation scm_itp) (itl_itemn : Column int scm_itl) (itl_wkcen : Column int scm_itl) (itl_locan : Column int scm_itl) (itp_itemn : Column int scm_itp) (itp_ponum : Column int scm_itp) (ik: isKey itp_itemn rel_itp), _). 
    refine (⟦ Γ ⊢ (SELECT * FROM1 (table rel_itp) WHERE (EXISTS (SELECT * FROM1 (table rel_itl) WHERE (and (and (equal (variable (right⋅itl_itemn)) (variable (left⋅right⋅itp_itemn))) (equal (variable (right⋅itl_wkcen)) (constantExpr integer_468))) (equal (variable (right⋅itl_locan)) (constantExpr integer_0)))))) : _ ⟧ =  ⟦ Γ ⊢ DISTINCT (SELECT1 (right⋅left⋅star) FROM1 (product (table rel_itp) (table rel_itl)) WHERE (and (and (equal (variable (right⋅left⋅itp_itemn)) (variable (right⋅right⋅itl_itemn))) (equal (variable (right⋅right⋅itl_wkcen)) (constantExpr integer_468))) (equal (variable (right⋅right⋅itl_locan)) (constantExpr integer_0)))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule. 
    start.
    symmetry.
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    rewrite (equiv_2sigma_eq_subst' _).
    simpl.
    pose (keyAxiom3 ik t).
    rewrite (path_universe_uncurried hprop_prod_trunc_r).
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor.
    + intros h.
      strip_truncations.
      destruct h as [a [[[b c] d] [e f]]].
      apply tr.
      constructor; try assumption.
      refine (a; _).
      break_and_rewrite.
    + intros h.
      strip_truncations.
      destruct h as [[a [[[b c] d] e]] f].
      apply tr.
      refine (a; _).
      break_and_rewrite.
  Qed. 
 
End Optimization. 
