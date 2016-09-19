Require Import HoTT.
Require Import UnivalenceAxiom.
Require Import UnivalentSemantics.

Module CQTactics (T : Types) (S : Schemas T) (R : Relations T S)  (A : Aggregators T S).
  
  Import T S R A.
  Module SQL_TSRA := SQL T S R A.
  Import SQL_TSRA.

  Definition Tuple2Sum {A B P} : {a : A & {b : B & P (a,b)}} -> {ab : A * B & P ab}.
    intros h.
    refine ((h.1,h.2.1); h.2.2).
  Defined.

  Ltac rewriteall :=
    repeat match goal with
           | t: _ = _ |- _ => rewrite t in *; clear t
           end.

  Ltac solveInstantiatedConjuctiveQuery :=
    cbn;
    repeat constructor;
    try apply tr;
    rewriteall;
    first [reflexivity | assumption].

  Ltac searchInstantiation solv :=
    match goal with
    | |- { _ : ?T0 * ?T1 & _ } => refine (Tuple2Sum _); searchInstantiation solv
    | t:Tuple ?T |- { _ : Tuple ?T & _ } => refine (t; _); searchInstantiation solv
    | |- _ => solv
    end.

  Ltac prepareDistinctSQLProof :=
    let g := fresh "g" in
    let t := fresh "t" in
    cbn;
    by_extensionality g;
    by_extensionality t;
    apply path_universe_uncurried;
    apply equiv_iff_hprop_uncurried;
    constructor.

  Ltac prepareConjuctiveQueryProof :=
    let h := fresh "h" in
    let t0 := fresh "t0" in
    intros h;
    strip_truncations;
    destruct h as [t0 h];
    repeat match goal with
           | h:?A * ?B |- _ => destruct h
           end;
    apply tr;
    cbn in *.

  Ltac conjuctiveQueryProof :=
    prepareDistinctSQLProof;
    prepareConjuctiveQueryProof;  
    searchInstantiation solveInstantiatedConjuctiveQuery.

End CQTactics.