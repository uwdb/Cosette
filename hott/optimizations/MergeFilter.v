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
    refine (⟦ Γ ⊢ (SELECT1 (right⋅dept_name) FROM1 ((SELECT * FROM1 (table rel_dept) WHERE (equal (variable (right⋅dept_deptno)) (constantExpr integer_10)))) WHERE (equal (variable (right⋅dept_deptno)) (constantExpr integer_10))) : _ ⟧ =  ⟦ Γ ⊢ (SELECT1 (right⋅dept_name) FROM1 (table rel_dept) WHERE (equal (variable (right⋅dept_deptno)) (constantExpr integer_10))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule. 
    start.
    f_ap.
    by_extensionality t0.
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    f_ap.
    deductive_proof'.    
  Qed. 
 
End Optimization. 
