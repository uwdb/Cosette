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
  
  Definition Rule: Type. 
    refine (forall ( Γ s1: Schema) (a: relation s1) (x : Column int s1) (y : Column int s1), _).
    refine (⟦ Γ ⊢ (SELECT1 (e2p (binaryExpr add (variable (right⋅x)) (variable (right⋅x)))) FROM1 (table a) WHERE (equal (variable (right⋅x)) (variable (right⋅y)))) : _ ⟧ =  ⟦ Γ ⊢ (SELECT1 (e2p (binaryExpr add (variable (right⋅x)) (variable (right⋅y)))) FROM1 (table a) WHERE (equal (variable (right⋅x)) (variable (right⋅y)))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule.
    start.
    f_ap.
    by_extensionality t0.
    apply path_universe_uncurried.
    apply hprop_prod_r_eq.
    intros [b c].
    rewrite b.
    reflexivity.
  Qed. 
 
End Optimization. 
