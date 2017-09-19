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
    refine (forall ( Γ scm_s2 scm_s1: Schema) (rel_b: relation scm_s2) (rel_a: relation scm_s1) (s2_b1 : Column int scm_s2) (s2_b2 : Column int scm_s2) (s1_a1 : Column int scm_s1) (s1_a2 : Column int scm_s1), _). 
    refine (⟦ Γ ⊢ (SELECT1 (combine (right⋅left⋅s1_a1) (combine (right⋅left⋅s1_a2) (combine (right⋅right⋅s2_b1) (right⋅right⋅s2_b2)))) FROM1 (product (table rel_a) (table rel_b)) WHERE (equal (variable (right⋅left⋅s1_a1)) (variable (right⋅right⋅s2_b1)))) : _ ⟧ =
            ⟦ Γ ⊢ (SELECT1 (combine (right⋅right⋅s1_a1) (combine (right⋅right⋅s1_a2) (combine (right⋅left⋅s2_b1) (right⋅left⋅s2_b2)))) FROM1 (product (table rel_b) (table rel_a)) WHERE (equal (variable (right⋅right⋅s1_a1)) (variable (right⋅left⋅s2_b1)))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule. 
    start.
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_m).
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    reflexivity.
  Qed.
 
End Optimization. 
