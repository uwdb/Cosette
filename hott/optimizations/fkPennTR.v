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
 

  Variable str_security_: constant int. 

  Definition Rule: Type. 
    refine (forall ( Γ scm_payroll scm_teams scm_depts: Schema) (rel_payroll: relation scm_payroll) (rel_teams: relation scm_teams) (rel_depts: relation scm_depts) (payroll_pdept : Column int scm_payroll) (payroll_empl : Column int scm_payroll) (teams_tproj : Column int scm_teams) (teams_tmember : Column int scm_teams) (depts_dname : Column int scm_depts) (depts_dproj : Column int scm_depts), _). 
    refine (⟦ Γ ⊢ (SELECT1 (right⋅right⋅teams_tmember) FROM1 (product (table rel_depts) (table rel_teams)) WHERE (and (equal (variable (right⋅left⋅depts_dproj)) (variable (right⋅right⋅teams_tproj))) (equal (variable (right⋅left⋅depts_dname)) (constantExpr str_security_)))) : _ ⟧ =  ⟦ Γ ⊢ (SELECT1 (right⋅left⋅right⋅right) FROM1 (product ((SELECT1 (combine (right⋅left⋅depts_dname) (combine (right⋅left⋅depts_dproj) (right⋅right⋅payroll_empl))) FROM1 (product (table rel_depts) (table rel_payroll)) WHERE (equal (variable (right⋅left⋅depts_dname)) (variable (right⋅right⋅payroll_pdept))))) ((SELECT1 (combine (right⋅left⋅teams_tmember) (combine (right⋅right⋅payroll_pdept) (right⋅left⋅teams_tproj))) FROM1 (product (table rel_teams) (table rel_payroll)) WHERE (equal (variable (right⋅left⋅teams_tmember)) (variable (right⋅right⋅payroll_empl)))))) WHERE (and (and (and (equal (variable (right⋅left⋅left)) (constantExpr str_security_)) (equal (variable (right⋅left⋅right⋅left)) (variable (right⋅right⋅right⋅right)))) (equal (variable (right⋅left⋅right⋅right)) (variable (right⋅right⋅left)))) (equal (variable (right⋅left⋅left)) (variable (right⋅right⋅right⋅left))))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule.
    Admitted. 
 
End Optimization. 
