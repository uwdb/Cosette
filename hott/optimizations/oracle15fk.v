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
 
  Variable integer_2014: constant int. 


  Definition Rule: Type.
    refine (forall ( Γ scm_product scm_customers scm_times scm_sales: Schema) (rel_product: relation scm_product) (rel_customers: relation scm_customers) (rel_times: relation scm_times) (rel_sales: relation scm_sales) (product_prod_id : Column int scm_product) (product_prod_cat : Column int scm_product) (customers_cust_id : Column int scm_customers) (customers_cust_name : Column int scm_customers) (times_time_id : Column int scm_times) (times_calendar_year : Column int scm_times) (sales_prod_id : Column int scm_sales) (sales_cust_id : Column int scm_sales) (sales_time_id : Column int scm_sales) (sales_amount_sold : Column int scm_sales) (kp: isKey product_prod_id rel_product) (kt: isKey times_time_id rel_times) (kc: isKey customers_cust_id rel_customers) (fk: fKey customers_cust_id sales_cust_id rel_customers rel_sales kc), _). 
    refine (⟦ Γ ⊢ (SELECT1 (combine (right⋅right⋅left⋅product_prod_cat) (right⋅left⋅sales_amount_sold)) FROM1 (product (table rel_sales) (product (table rel_product) (product (table rel_customers) (table rel_times)))) WHERE (and (and (and (equal (variable (right⋅left⋅sales_prod_id)) (variable (right⋅right⋅left⋅product_prod_id))) (equal (variable (right⋅left⋅sales_cust_id)) (variable (right⋅right⋅right⋅left⋅customers_cust_id)))) (equal (variable (right⋅left⋅sales_time_id)) (variable (right⋅right⋅right⋅right⋅times_time_id)))) (equal (variable (right⋅right⋅right⋅right⋅times_calendar_year)) (constantExpr integer_2014)))) : _ ⟧ =  ⟦ Γ ⊢ (SELECT1 (combine (right⋅right⋅left⋅product_prod_cat) (right⋅left⋅sales_amount_sold)) FROM1 (product (table rel_sales) (product (table rel_product) (table rel_times))) WHERE (and (and (equal (variable (right⋅left⋅sales_prod_id)) (variable (right⋅right⋅left⋅product_prod_id))) (equal (variable (right⋅left⋅sales_time_id)) (variable (right⋅right⋅right⋅times_time_id)))) (equal (variable (right⋅right⋅right⋅times_calendar_year)) (constantExpr integer_2014)))) : _ ⟧). 
  Defined. 
  Arguments Rule /. 

    Lemma equiv_sigma_prod_symm_m' {A B C D E}:
    {a: A & B a * C a * D a * E a} <~> {a:A & B a * D a * C a * E a}.
  Proof.
    repeat rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc_h).
    exact equiv_sigma_prod_symm_m.
  Defined.
  
  Lemma ruleStand: Rule.
    start.
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried sum2_pair_split).
    rewrite (path_universe_uncurried sum_pair_split').
    simpl.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried sum_pair_split').
    f_ap.
    by_extensionality b.
    rewrite (path_universe_uncurried sum_pair_split').
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    f_ap.
    by_extensionality c.
    repeat rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_f).
    repeat rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    repeat rewrite (path_universe_uncurried equiv_sigma_prod_assoc_h).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_m').
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_m').
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc_h).
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_m').
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_m').
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_m').
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc_h).
    rewrite (path_universe_uncurried (equiv_prod_sigma_r _ _ _)).
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (sigma_prod_path_symm _ _)).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite <- fk.
    repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)). 
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)). 
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)). 
    reflexivity.
  Qed.
End Optimization. 
