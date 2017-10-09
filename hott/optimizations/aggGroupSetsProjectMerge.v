Require Import HoTT. 
Require Import UnivalenceAxiom. 
Require Import HoTTEx. 
Require Import Denotation. 
Require Import UnivalentSemantics. 
Require Import AutoTactics. 
Require Import CQTactics. 

(* manual proof of the rule similar to: 
   examples/caclite/testAggregateGroupingSetsProjectMerge.cos *)

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
  Notation "'max' ( e )" := (aggregatorGroupByProj max e). 
  Parameter min : forall {T}, aggregator T int. 
  Notation "'min' ( e )" := (aggregatorGroupByProj min e).
 
  Parameter gt: Pred (node (leaf int) (leaf int)). 
 

  Definition Rule: Type. 
    refine (forall ( Γ scm_s: Schema) (rel_r: relation scm_s) (s_a : Column int scm_s) (s_b : Column int scm_s) (s_c : Column int scm_s), _). 
    refine (⟦ Γ ⊢ (SELECT  (combine' PLAIN(variable (right⋅s_a)) (combine' PLAIN(variable (right⋅s_b)) (COUNT(variable (right⋅s_c))))) FROM1  (table rel_r)  GROUP BY  (combine (right⋅s_a) (right⋅s_b))) : _ ⟧ =  ⟦ Γ ⊢ (SELECT  (combine' PLAIN(variable (right⋅s_a)) (combine' PLAIN(variable (right⋅s_b)) (COUNT(variable (right⋅s_c))))) FROM1  (table rel_r)  GROUP BY  (combine (right⋅s_b) (right⋅s_a))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule.
    start.
    repeat f_ap.
    by_extensionality t0.
    repeat f_ap.
    by_extensionality t'.
    f_ap.
    by_extensionality t1.
    f_ap.
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _ )).
    reflexivity.
  Qed. 
 
End Optimization. 