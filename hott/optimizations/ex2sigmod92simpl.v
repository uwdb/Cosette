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
    refine (forall ( Γ scm_itm scm_itp: Schema) (rel_itm: relation scm_itm) (rel_itp: relation scm_itp) (itm_itemno : Column int scm_itm) (itm_type : Column int scm_itm) (itp_itemno : Column int scm_itp) (itp_np : Column int scm_itp) (ik: isKey itm_itemno rel_itm), _). 
    refine (⟦ Γ ⊢ (SELECT1 (combine (right⋅right⋅itm_itemno) (right⋅left⋅right)) FROM1 (product (DISTINCT (SELECT1 (combine (right⋅itp_itemno) (right⋅itp_np)) FROM1 (table rel_itp) )) (table rel_itm)) WHERE (equal (variable (right⋅left⋅left)) (variable (right⋅right⋅itm_itemno)))) : _ ⟧ =  ⟦ Γ ⊢ DISTINCT (SELECT1 (combine (right⋅right⋅itm_itemno) (right⋅left⋅itp_np)) FROM1 (product (table rel_itp) (table rel_itm)) WHERE (equal (variable (right⋅left⋅itp_itemno)) (variable (right⋅right⋅itm_itemno)))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 

  
  Lemma ruleStand: Rule. 
    start.
    rewrite (equiv_sig_break_pair_f _ _).
    simpl.
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc_h).
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_t).
    destruct t as [a b].
    simpl.
    rewrite <- (equiv_sig_break_pair_f' (fun a => fst (fst a)) (fun a => snd (fst a)) _ _).
    rewrite (path_universe_uncurried sum_pair_split').
    simpl.
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    rewrite (equiv_2sigma_eq_subst' _).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    specialize (keyAxiom2 ik).
    intro pf.
    rewrite (path_universe_uncurried (equiv_trunc_sigma_prod _)).
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor.
    + intros h.
      strip_truncations.
      destruct h as [c [d [e f]]].
      strip_truncations.
      destruct d as [h [i j]].
      apply tr.
      refine ((h, c); _).
      rewrite <- (path_universe_uncurried (equiv_path_prod _ _)) in j.
      destruct j as [j k].
      simpl in *.
      destruct j.
      destruct k.
      destruct f.
      constructor; break_and_rewrite.
    + intros h.
      strip_truncations.
      apply tr.
      destruct h as [[c d] [[e [f h]] i]].
      rewrite <- (path_universe_uncurried (equiv_path_prod _ _)) in i.
      destruct i as [i j].
      simpl in *.
      refine (d; _).
      constructor.
      {  apply tr.
         refine (c; _).
         break_and_rewrite. }
      constructor; break_and_rewrite.
  Qed.
 
End Optimization. 
