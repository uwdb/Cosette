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
    refine (forall ( Γ scm_dept: Schema) (rel_dept: relation scm_dept) (dept_deptno : Column int scm_dept) (dept_name : Column int scm_dept), _). 
    refine (⟦ Γ ⊢ (SELECT1 (combine (right⋅left) (right⋅right)) FROM1 ((SELECT  (combine' PLAIN(variable (right⋅dept_name)) (COUNT(variable (right⋅dept_name)))) FROM1  (table rel_dept)  GROUP BY  (right⋅dept_name))) WHERE (equal (variable (right⋅left)) (constantExpr integer_10))) : _ ⟧ =  ⟦ Γ ⊢ (SELECT  (combine' PLAIN(variable (right)) (COUNT(variable right))) FROM1  ((SELECT1 (right⋅dept_name) FROM1 (table rel_dept) )) WHERE (equal (variable right) (constantExpr integer_10)) GROUP BY  (right)) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule. 
    start.
    destruct t as [a b].
    rewrite (path_universe_uncurried (equiv_sigma_eq_subst' _)).
    repeat rewrite (equiv_sig_break_pair_f _ _).
    simpl.
    symmetry.
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_sigma_eq_subst' _)).
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor.
    + intros.
      strip_truncations.
      break_and_rewrite.
      apply tr.
      destruct snd as [t [h1 h2]].
      refine (t; _).
      refine ((h1, h2), _).
      f_ap.
      destruct h2.
      by_extensionality t1.
      symmetry.
      rewrite (path_universe_uncurried (equiv_sigma_eq_subst' _)).
      rewrite (path_universe_uncurried (equiv_prod_sigma _ _ _)).
      rewrite (path_universe_uncurried (equiv_prod_sigma _ _ _)).
      f_ap.
      by_extensionality t0.
      repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
      rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
      symmetry.
      rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
      repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
      f_ap.
      apply path_universe_uncurried.
      apply equiv_iff_hprop_uncurried.
      constructor;
      break_and_rewrite.
    + intros.
      destruct X as [h1 h2].
      destruct h1.
      strip_truncations.
      apply tr.
      destruct h2 as [c [[h3 h4] h5]].
      destruct h4.
      refine (_, _).
      { destruct h5.
        f_ap.
        by_extensionality t.
        rewrite (path_universe_uncurried (equiv_sigma_eq_subst' _)).
        repeat rewrite (path_universe_uncurried (equiv_prod_sigma _ _ _)).
        f_ap.
        by_extensionality t0.
        repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
        rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
        symmetry.
        rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
        repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
        f_ap.
        apply path_universe_uncurried.
        apply equiv_iff_hprop_uncurried.
        constructor;
        break_and_rewrite. }
      { break_and_rewrite.
        refine (c; _).
        refine (h3, _).
        reflexivity. }
  Qed. 
 
End Optimization. 
