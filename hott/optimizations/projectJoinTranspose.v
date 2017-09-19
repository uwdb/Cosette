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
 
  Parameter int: type. 
  Parameter add: binary int int int. 
  Parameter minus: binary int int int. 
 
  Notation combine' := combineGroupByProj.
 
  Parameter count : forall {T}, aggregator T int. 
  Notation "'COUNT' ( e )" := (aggregatorGroupByProj count e). 
 
  Parameter gt: Pred (node (leaf int) (leaf int)). 

  Definition Rule: Type. 
    refine (forall ( Γ scm_s2 scm_s1: Schema) (rel_r2: relation scm_s2) (rel_r1: relation scm_s1) (s2_a : Column int scm_s2) (s2_b : Column int scm_s2)  (s1_a : Column int scm_s1) (s1_b : Column int scm_s1) , _). 
    refine (⟦ Γ ⊢ (SELECT1 (combine (right⋅left⋅s1_b) (right⋅right⋅s2_b)) FROM1 (product (table rel_r1) (table rel_r2)) ) : _ ⟧ =
            ⟦ Γ ⊢ (SELECT1 (combine (right⋅left) (right⋅right)) FROM1 (product ((SELECT1 (right⋅s1_b) FROM1 (table rel_r1) )) ((SELECT1 (right⋅s2_b) FROM1 (table rel_r2) ))) ) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule.
    start.
    rewrite (path_universe_uncurried (equiv_sigma_eq_subst' _)).
    rewrite <- (path_universe_uncurried (equiv_prod_sigma_r _ _ _)).
    rewrite equiv_sigma_sigma_prod.
    rewrite (path_universe_uncurried sum_pair_split').
    f_ap.
    by_extensionality a.
    f_ap.
    by_extensionality b.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    rewrite (path_universe_uncurried (equiv_pair_assemble _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    reflexivity.
  Defined.
 
End Optimization. 
