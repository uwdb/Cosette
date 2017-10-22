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

  Parameter keyAxiomNew:
    forall {s ty} {k: Column ty s} {R: SQL empty s} (kp: isKey k R) (t t':Tuple s),
      (denoteProj k t' = denoteProj k t) * (denoteSQL R tt t') * (denoteSQL R tt t) 
      = (denoteProj k t' = denoteProj k t) * (denoteSQL R tt t') * (denoteSQL R tt t) * ( t = t') .
  


  Definition Rule: Type. 
    refine (forall ( Γ scm_r2 scm_r1: Schema) (rel_r2: relation scm_r2) (rel_r1: relation scm_r1) (r2_a : Column int scm_r2) (r2_b : Column int scm_r2) (r1_a : Column int scm_r1) (r1_b : Column int scm_r1) (ik: isKey r2_a (table rel_r2)), _). 
    refine (⟦ Γ ⊢ (SELECT1 (combine (right⋅right⋅right⋅r2_a) (right⋅right⋅right⋅r2_b)) FROM1 (product (table rel_r1) (product (table rel_r2) (table rel_r2))) WHERE (and (and (and (equal (variable (right⋅left⋅r1_a)) (variable (right⋅right⋅left⋅r2_a))) (equal (variable (right⋅right⋅left⋅r2_a)) (variable (right⋅right⋅right⋅r2_a)))) (equal (variable (right⋅left⋅r1_a)) (variable (right⋅right⋅right⋅r2_a)))) (equal (variable (right⋅right⋅left⋅r2_b)) (variable (right⋅right⋅right⋅r2_b))))) : _ ⟧ =  ⟦ Γ ⊢ (SELECT1 (combine (right⋅right⋅right⋅r2_a) (right⋅right⋅right⋅r2_b)) FROM1 (product (table rel_r1) (product (table rel_r2) (table rel_r2))) WHERE (and (and (equal (variable (right⋅left⋅r1_a)) (variable (right⋅right⋅left⋅r2_a))) (equal (variable (right⋅right⋅left⋅r2_a)) (variable (right⋅right⋅right⋅r2_a)))) (equal (variable (right⋅left⋅r1_a)) (variable (right⋅right⋅right⋅r2_a))))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule.
    start.
    f_ap.
    by_extensionality t0.
    destruct t0 as [a [b c]].
    destruct t as [ta tb].
    simpl.
    pose (keyAxiomNew ik) as pf. 
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    symmetry.
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    specialize (pf c b).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ (denoteProj r2_a b = denoteProj r2_a c))).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).    
    rewrite pf.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor.
    + intros [p1 p2].
      destruct p1.
      destruct p2.
      constructor. constructor; reflexivity. reflexivity.
    + intros [[p1 p2] p3].
      destruct p1.
      constructor; reflexivity.
  Qed. 
 
End Optimization. 
