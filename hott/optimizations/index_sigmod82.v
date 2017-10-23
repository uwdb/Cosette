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
 
  Variable integer_29: constant int. 

  Lemma equiv_2sigma_eq_subst' {A B : Type} {C : A -> B -> Type}:
    forall f, {a:A & {b:B & C a b * (b = f a)}} = ∑ a, C a (f a).
  Proof.
    intro f.
    f_ap.
    by_extensionality a.
    exact (path_universe_uncurried (equiv_sigma_eq_subst' _)).
  Defined.

  Lemma equiv_2sigma_eq_subst_r' {A B : Type} {C : A -> B -> Type}:
    forall f, {a:A & {b:B & C a b * (f a = b)}} = ∑ a, C a (f a).
  Proof.
    intro f.
    f_ap.
    by_extensionality a.
    exact (path_universe_uncurried (equiv_sigma_eq_subst_r' _)).
  Defined.

  Definition equiv_prod_2sigma_l {A B C D}:
    {a: A & D a * {b:B & C a b} } <~> {a: A & {b:B & D a * C a b}}.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried (equiv_prod_sigma _ _ _)).
    reflexivity.
  Defined.

  Lemma equiv_sigma_prod_symm_m {A B C D E}:
    {a: A & (B a) * (C a * D a) * E a} <~> {a:A & (B a) * (D a * C a) * E a}.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    reflexivity.
  Defined.

  Definition hset_eq_symm {A} `{IsHSet A}:
    forall (a b:A), (a = b) <~> (b = a).
    intros.
    apply equiv_iff_hprop_uncurried.
    constructor; break_and_rewrite.
  Defined.
  
  Definition Rule: Type. 
    refine (forall ( Γ scm_applicant scm_payroll: Schema) (rel_applicant: relation scm_applicant) (rel_payroll: relation scm_payroll) (applicant_ssno : Column int scm_applicant) (applicant_jobtitile : Column int scm_applicant) (applicant_officeno : Column int scm_applicant) (payroll_ssno : Column int scm_payroll) (payroll_deptno : Column int scm_payroll) (ik: isKey payroll_ssno rel_payroll), _). 
    refine (⟦ Γ ⊢ (SELECT1 (right⋅right⋅star) FROM1 (product (table rel_payroll) (table rel_applicant)) WHERE (and (equal (variable (right⋅left⋅payroll_ssno)) (variable (right⋅right⋅applicant_ssno))) (equal (variable (right⋅left⋅payroll_deptno)) (constantExpr integer_29)))) : _ ⟧ =  ⟦ Γ ⊢ (SELECT1 (right⋅right⋅right⋅star) FROM1 (product (table rel_payroll) (product ((SELECT1 (combine (right⋅payroll_ssno) (right⋅payroll_deptno)) FROM1 (table rel_payroll) )) (table rel_applicant))) WHERE (and (and (equal (variable (right⋅left⋅payroll_ssno)) (variable (right⋅right⋅left⋅left))) (equal (variable (right⋅right⋅right⋅applicant_ssno)) (variable (right⋅left⋅payroll_ssno)))) (equal (variable (right⋅right⋅left⋅right)) (constantExpr integer_29)))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 
 
  Lemma ruleStand: Rule. 
    start.
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried sum2_pair_split).
    simpl.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried (equiv_sigma_eq_subst' _)).
    rewrite (equiv_2sigma_eq_subst' _).
    repeat rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    repeat rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_prod_2sigma_l).
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    repeat rewrite (path_universe_uncurried equiv_2sigma_prod_assoc).
    rewrite (equiv_2sigma_eq_subst_r' _).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite <- (path_universe_uncurried (equiv_prod_sigma _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    repeat rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite <- (path_universe_uncurried (equiv_prod_sigma _ _ _)).
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    f_ap.
    + apply path_universe_uncurried.
      apply equiv_iff_hprop_uncurried.
      constructor; break_and_rewrite.
    + rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
      rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
      rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
      rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
      rewrite (path_universe_uncurried equiv_sigma_prod_symm_f).
      rewrite (path_universe_uncurried equiv_sigma_prod_symm_m).
      rewrite (path_universe_uncurried equiv_sigma_prod_assoc_h).
      repeat rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
      rewrite (path_universe_uncurried (sigma_prod_path_symm' _ _)).
      repeat rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
      rewrite (keyLemma2 ik).
      rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
      rewrite <- (path_universe_uncurried (equiv_prod_sigma _ _ _)).
      f_ap.
  Qed.
  
End Optimization. 
