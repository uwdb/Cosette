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
  Variable integer_20: constant int. 
  Variable integer_85: constant int. 

  Definition hset_sig_prod_eq_symm {A B C} `{IsHSet C}:
    forall (f1 f2:A -> C), {a:A & B a * (f1 a = f2 a)} <~>  {a:A & B a * (f2 a = f1 a)}.
    intros.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    f_ap.
    rewrite (path_universe_uncurried (hset_eq_symm (f1 a) _)).
    reflexivity.
  Defined.

  Definition Rule: Type. 
    refine (forall ( Γ scm_pur scm_itm scm_itp: Schema) (rel_pur: relation scm_pur) (rel_itm: relation scm_itm) (rel_itp: relation scm_itp) (pur_ponum : Column int scm_pur) (pur_odate : Column int scm_pur) (pur_vendn : Column int scm_pur) (itm_itemn : Column int scm_itm) (itm_type : Column int scm_itm) (itp_itemn : Column int scm_itp) (itp_ponum : Column int scm_itp) (ik: isKey itm_itemn rel_itm), _). 
    refine (⟦ Γ ⊢ (SELECT1 (combine (right⋅left⋅itm_itemn) (right⋅right⋅right)) FROM1 (product (table rel_itm) (DISTINCT (SELECT1 (combine (right⋅left⋅itp_itemn) (right⋅right⋅pur_vendn)) FROM1 (product (table rel_itp) (table rel_pur)) WHERE (and (equal (variable (right⋅left⋅itp_ponum)) (variable (right⋅right⋅pur_ponum))) (castPred (combine (right⋅right⋅pur_odate) (e2p (constantExpr integer_85)) ) gt))))) WHERE (and (and (equal (variable (right⋅left⋅itm_itemn)) (variable (right⋅right⋅left))) (castPred (combine (right⋅left⋅itm_itemn) (e2p (constantExpr integer_1)) ) gt)) (castPred (combine (e2p (constantExpr integer_20)) (right⋅left⋅itm_itemn) ) gt))) : _ ⟧ =  ⟦ Γ ⊢ DISTINCT (SELECT1 (combine (right⋅left⋅itm_itemn) (right⋅right⋅right⋅pur_vendn)) FROM1 (product (table rel_itm) (product (table rel_itp) (table rel_pur))) WHERE (and (and (and (and (equal (variable (right⋅right⋅left⋅itp_ponum)) (variable (right⋅right⋅right⋅pur_ponum))) (equal (variable (right⋅left⋅itm_itemn)) (variable (right⋅right⋅left⋅itp_itemn)))) (castPred (combine (right⋅right⋅right⋅pur_odate) (e2p (constantExpr integer_85)) ) gt)) (castPred (combine (right⋅left⋅itm_itemn) (e2p (constantExpr integer_1)) ) gt)) (castPred (combine (e2p (constantExpr integer_20)) (right⋅left⋅itm_itemn) ) gt))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule. 
    start.
    rewrite (equiv_sig_break_pair_f _ _).
    simpl.
    repeat rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    rewrite (path_universe_uncurried (hset_sig_prod_eq_symm _ _)).
    repeat rewrite (path_universe_uncurried equiv_sigma_prod_assoc_h).
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_t).
    rewrite <- (equiv_sig_break_pair_f' _ _ _ _).
    rewrite (path_universe_uncurried sum_pair_split').
    simpl.
    rewrite (equiv_2sigma_eq_subst' _).  (* simplifed LHS *)
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_m).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc_h).
    repeat rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc_h).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried hprop_prod_trunc_in_sig).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried hprop_prod_trunc_in_sig). (* pred into trunc *)
    specialize (keyAxiom2 ik).  intros pf.
    rewrite (path_universe_uncurried (equiv_trunc_sigma_prod _)). (* trunc LHS *)
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor.
    + intros h.
      strip_truncations.
      destruct h as [a [b [c d]]].
      strip_truncations.
      destruct b as [b [e [[f h] i]]].
      destruct i as [[[i j] [k l]] m].
      rewrite <- (path_universe_uncurried (equiv_path_prod _ _)) in m.
      destruct m as [m n].
      simpl in *.
      apply tr.
      refine ((a, (f, h)); _).
      rewrite <- (path_universe_uncurried (equiv_path_prod _ _)).
      break_and_rewrite.
    + intros h.
      strip_truncations.
      destruct h as [a [c [d [e [f h]]]]].
      destruct h as [h [[i [j k]] l]].
      rewrite <- (path_universe_uncurried (equiv_path_prod _ _)) in l.
      destruct l as [l m].
      destruct a as [a1 [a2 a3]].
      simpl in *.
      apply tr.
      refine (a1; _).
      constructor.
      { apply tr.
        constructor; try assumption.
        constructor; try assumption.
        refine ((a2, a3); _).
        break_and_rewrite. }
      { break_and_rewrite. }
  Qed. 
 
End Optimization. 
