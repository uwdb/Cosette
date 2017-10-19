Require Import HoTT.
Require Import UnivalenceAxiom.

Require Import HoTTEx.
Require Import UnivalentSemantics.
Require Import CQTactics.

Module AutoTactics (T : Types) (S : Schemas T) (R : Relations T S)  (A : Aggregators T S).
  
  Import T S R A.
  Module SQL_TSRA := SQL T S R A.
  Import SQL_TSRA.
  Module CQTac := CQTactics T S R A.
  Import CQTac.

  Ltac ring1 :=
    repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _));
    try f_ap;
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).

  Ltac ring2 :=
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _));
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).

  Ltac ring3 :=
    repeat (rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)));
    f_ap;
    repeat  rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _));
    f_ap;
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).

  Ltac transform :=
    try ring1;
    try rewrite (path_universe_uncurried (hprop_prod_prod _)).

  Ltac transform1 :=
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_m);
    rewrite (path_universe_uncurried sum_pair_split');
    rewrite (path_universe_uncurried sum_pair_split');
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).

  Ltac transform2 :=
    rewrite (path_universe_uncurried (equiv_sigma_eq_subst' _));
    rewrite <- (path_universe_uncurried (equiv_prod_sigma_r _ _ _));
    rewrite equiv_sigma_sigma_prod;
    rewrite (path_universe_uncurried sum_pair_split');
    f_ap;
    let a := fresh "a" in
    by_extensionality a;
    f_ap;
    let b := fresh "b" in
    by_extensionality b;
    rewrite (path_universe_uncurried (equiv_prod_symm _ _));
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _));
    rewrite (path_universe_uncurried (equiv_prod_symm _ _));
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _));
    symmetry;
    rewrite (path_universe_uncurried (equiv_prod_symm _ _));
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _));
    rewrite (path_universe_uncurried (equiv_prod_symm _ _));
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _));
    f_ap;
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _));
    rewrite (path_universe_uncurried (equiv_prod_symm _ _));
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _));
    symmetry;
    rewrite (path_universe_uncurried (equiv_prod_symm _ _));
    f_ap;
    rewrite (path_universe_uncurried (equiv_pair_assemble _));
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).


  Ltac hott_ring' :=
    repeat rewrite (path_universe_uncurried (sum_distrib_l _ _ _));
    try first [ simp_solve | (ring1; simp_solve) | (ring2; simp_solve) | (ring3; simp_solve) | (transform; simp_solve) | (transform1; simp_solve) | (transform2; simp_solve)].
  
  (* Poor men's ring tactic *)
  Ltac hott_ring :=
    start;
    hott_ring'.

  Ltac solve_disjunction :=
    match goal with
    | |- ?A -> ?B => intros; solve_disjunction
    | t: Trunc (-1) ?A |- Trunc (-1) ?B => strip_truncations; solve_disjunction
    | |- Trunc (-1) ?A => apply tr; solve_disjunction
    | t: ?A * ?B |- _ => destruct t; solve_disjunction
    | t: _ + _ |- _ => destruct t; solve_disjunction
    | |- ?A + ?B => first [(refine (inl _); solve_disjunction) | (refine (inr _); solve_disjunction)]
    | |- ?A * ?B => constructor; solve_disjunction
    | _ => simp_solve
    end.

  Ltac deductive_proof' :=
    apply path_universe_uncurried;
    apply equiv_iff_hprop_uncurried;
    constructor; solve_disjunction.

  Ltac deductive_proof :=
    start;
    deductive_proof'.

  (*try hprop_prod_l. *)
  Ltac sum_heuristic1 :=
    apply path_universe_uncurried;
    refine (hprop_prod_l _);
    intro;
    apply tr;
    searchInstantiation solveInstantiatedConjuctiveQuery.

  (*try hprop_prod_r_eq *)
  Ltac prod_heuristic1 :=
    f_ap;
    let t := fresh "t" in
    by_extensionality t;
    apply path_universe_uncurried;
    apply hprop_prod_r_eq;
    intros;
    solve_disjunction;
    solveInstantiatedConjuctiveQuery.
  
  
  (* try to apply heuristcs to solve summation *)
  (* TODO: add more heuristics *)
  Ltac solve_summation :=
    start;
    sum_heuristic1.
  
End AutoTactics.