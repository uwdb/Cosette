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
    refine (forall ( Γ scm_r3 scm_r2 scm_r1: Schema) (rel_r3: relation scm_r3) (rel_r2: relation scm_r2) (rel_r1: relation scm_r1) (r3_a : Column int scm_r3) (r3_b : Column int scm_r3) (r2_a : Column int scm_r2) (r2_b : Column int scm_r2) (r1_a : Column int scm_r1) (r1_b : Column int scm_r1), _). 
    refine (⟦ Γ ⊢ (SELECT1 (combine (right⋅right⋅right⋅r3_a) (right⋅right⋅right⋅r3_b)) FROM1 (product (table rel_r1) (product (table rel_r2) (table rel_r3))) WHERE (and (and (and (equal (variable (right⋅left⋅r1_a)) (variable (right⋅right⋅left⋅r2_a))) (equal (variable (right⋅right⋅left⋅r2_a)) (variable (right⋅right⋅right⋅r3_a)))) (equal (variable (right⋅left⋅r1_a)) (variable (right⋅right⋅right⋅r3_a)))) (equal (variable (right⋅right⋅left⋅r2_b)) (variable (right⋅right⋅right⋅r3_b))))) : _ ⟧ =  ⟦ Γ ⊢ (SELECT1 (combine (right⋅right⋅right⋅r3_a) (right⋅right⋅right⋅r3_b)) FROM1 (product (table rel_r1) (product (table rel_r2) (table rel_r3))) WHERE (and (and (equal (variable (right⋅left⋅r1_a)) (variable (right⋅right⋅left⋅r2_a))) (equal (variable (right⋅right⋅left⋅r2_a)) (variable (right⋅right⋅right⋅r3_a)))) (equal (variable (right⋅left⋅r1_a)) (variable (right⋅right⋅right⋅r3_a))))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule. 
    start.
    f_ap.
    by_extensionality t0.
    destruct t0 as [a [b c]].
    simpl.
    Admitted. 
 
End Optimization. 
