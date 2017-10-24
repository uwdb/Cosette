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
 
  Variable integer_1000: constant int.

  Definition Rule: Type. 
    refine (forall ( Γ scm_itm scm_itp: Schema) (rel_itm: relation scm_itm) (rel_itp: relation scm_itp) (itm_itemno : Column int scm_itm) (itm_type : Column int scm_itm) (itp_itemno : Column int scm_itp) (itp_np : Column int scm_itp) (ik: isKey itm_itemno rel_itm), _). 
    refine (⟦ Γ ⊢ (SELECT1 (combine (right⋅left⋅right) (combine (right⋅right⋅itm_type) (right⋅right⋅itm_itemno))) FROM1 (product (DISTINCT (SELECT1 (combine (right⋅itp_itemno) (right⋅itp_np)) FROM1 (table rel_itp) WHERE (castPred (combine (right⋅itp_np) (e2p (constantExpr integer_1000)) ) gt))) (table rel_itm)) WHERE (equal (variable (right⋅left⋅left)) (variable (right⋅right⋅itm_itemno)))) : _ ⟧ =  ⟦ Γ ⊢ DISTINCT (SELECT1 (combine (right⋅left⋅itp_np) (combine (right⋅right⋅itm_type) (right⋅right⋅itm_itemno))) FROM1 (product (table rel_itp) (table rel_itm)) WHERE (and (castPred (combine (right⋅left⋅itp_np) (e2p (constantExpr integer_1000)) ) gt) (equal (variable (right⋅left⋅itp_itemno)) (variable (right⋅right⋅itm_itemno))))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule.
    start.
    rewrite (equiv_sig_break_pair_f _ _).
    rewrite (equiv_sig_break_pair_f _ _).
    destruct t as [t1 [t2 t3]].
    simpl.
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc_h).
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_t).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc_h).
    rewrite <- (equiv_sig_break_pair_f' _ _ _ _).
    rewrite (path_universe_uncurried sum_pair_split').
    simpl.
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    rewrite (equiv_2sigma_eq_subst' _).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc_h).
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_m).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc_h).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_f).
    rewrite (path_universe_uncurried (hprop_prod_path_trunc_in_sig _ _)).   specialize (keyAxiom2 ik).
    intros pf.
    rewrite (path_universe_uncurried (equiv_trunc_sigma_prod _)).
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor.
    + intros h.
      strip_truncations.
      destruct h as [a [b [c d]]].
      strip_truncations.
      destruct b as [b [e [[f h] i]]].
      rewrite <- (path_universe_uncurried (equiv_path_prod _ _)) in i.
      destruct i as [i j].
      simpl in *.
      apply tr.
      refine ((e, a); _).
      break_and_rewrite.
    + intros h.
      strip_truncations.
      destruct h as [a [[[c d] e] f]].
      rewrite <- (path_universe_uncurried (equiv_path_prod _ _)) in f.
      rewrite <- (path_universe_uncurried (equiv_path_prod _ _)) in f.
      simpl in f.
      destruct f as [f [i j]].
      apply tr.
      destruct a as [a0 a1].
      refine (a1; _).
      repeat constructor.
      { apply tr.
        constructor.
        - break_and_rewrite.
        - refine (a0; _).
          rewrite <- (path_universe_uncurried (equiv_path_prod _ _)).
          break_and_rewrite. }
      { break_and_rewrite. }
      { break_and_rewrite. }
   Qed. 
 
End Optimization. 
