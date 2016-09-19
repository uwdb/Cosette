Require Import HoTT.
Require Import UnivalenceAxiom.

Require Import HoTTEx.
Require Import Denotation.
Require Import UnivalentSemantics.

Open Scope type.

Module RelationalAlgebraOptimization (T : Types) (S : Schemas T) (R : Relations T S)  (A : Aggregators T S).
  Import T S R A.
  Module SQL_TSRA := SQL T S R A.
  Import SQL_TSRA.

  Lemma commutativeSelect Γ s a slct0 slct1 :
    ⟦ Γ ⊢ (SELECT * FROM1 (SELECT * FROM1 a WHERE slct1) WHERE slct0) : s ⟧ =
    ⟦ Γ ⊢ (SELECT * FROM1 (SELECT * FROM1 a WHERE slct0) WHERE slct1) : s ⟧.
  Proof.
    simpl.
    by_extensionality g.
    by_extensionality t.
    match goal with
    | |- ?X * (?Y * ?Z) = _ => 
      generalize X Y Z; clear; intros x y z
    end.
    rewrite (path_universe_uncurried (equiv_prod_assoc x y z)).
    rewrite (path_universe_uncurried (equiv_prod_symm x y)).
    rewrite (path_universe_uncurried (equiv_prod_assoc y x z)).
    reflexivity.
  Qed.
 
  Lemma idempotentSelect Γ s a slct :
    ⟦ Γ ⊢ (SELECT * FROM1 (SELECT * FROM1 a WHERE slct) WHERE slct) : s ⟧ =
    ⟦ Γ ⊢ (SELECT * FROM1 a WHERE slct) : s ⟧.
  Proof.
    simpl.
    by_extensionality g.
    by_extensionality t.
    match goal with
    | |- _ = (_ ?X * ?Y) => 
      generalize X Y; clear; intros x y
    end.
    rewrite (path_universe_uncurried (equiv_prod_assoc x x y)).
    rewrite (path_universe_uncurried (hprop_prod_prod x)).
    reflexivity.
  Qed.
 
  Lemma conjunctSelect Γ s a slct0 slct1 :
    ⟦ Γ ⊢ (SELECT * FROM1 a WHERE slct0 AND slct1) : s ⟧ =
    ⟦ Γ ⊢ (SELECT * FROM1 (SELECT * FROM1 a WHERE slct0) WHERE slct1) : s ⟧.
  Proof.
    simpl.
    by_extensionality g.
    by_extensionality t.
    match goal with
    | |- ?X * ?Y * ?Z = _ => 
      generalize X Y Z; clear; intros x y z
    end.
    rewrite (path_universe_uncurried (equiv_prod_assoc y x z)).
    rewrite (path_universe_uncurried (equiv_prod_symm x y)).
    reflexivity.
  Qed.

  Lemma pushdownSelect Γ s1 s2 (r: SQL Γ s1) (s: SQL Γ s2) slct: 
    ⟦ Γ ⊢ (SELECT * FROM r, (SELECT * FROM1 s WHERE slct)) : _ ⟧ =
    ⟦ Γ ⊢ (SELECT * FROM r, s WHERE
           castPred (combine left (right⋅right)) slct) : _ ⟧.
  Proof.
    simpl.
    by_extensionality g.
    by_extensionality t.
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    f_ap.
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
  Qed.

  (* The fact that we cannot rewrite
       (SELECT * FROM a WHERE slct0) UNION (SELECT * FROM a WHERE slct1)
     into
       SELECT * FROM a WHERE slct0 OR slct1
     should inspire us to have WHERE clauses that can influence multiplicity *)
  Lemma disjointSelect Γ s a slct0 slct1 :
    ⟦ Γ ⊢ (DISTINCT SELECT * FROM1 a WHERE slct0 OR slct1) : s ⟧ =
    ⟦ Γ ⊢ (DISTINCT ((SELECT * FROM1 a WHERE slct0) UNION ALL (SELECT * FROM1 a WHERE slct1))) : s ⟧.
  Proof.
    simpl.
    by_extensionality g.
    by_extensionality t.
    match goal with
    | |- _ (_ (_ ?X + _ ?Y) * ?Z) = _ => generalize X Y Z; clear; intros A B C
    end.
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor.
    + intro u.
      strip_truncations.
      destruct u as [u c].
      strip_truncations.
      apply tr.
      destruct u as [a|b].
      - exact (inl (a,c)).
      - exact (inr (b,c)). 
    + intro u.
      strip_truncations.
      apply tr.
      destruct u as [u|u].
      - refine (tr (inl (fst u)), snd u).
      - refine (tr (inr (fst u)), snd u).
  Qed.
  
  Lemma projectionDistributesOverUnionn Γ s a0 a1 slct :
    ⟦ Γ ⊢ (SELECT * FROM1 (a0 UNION ALL a1) WHERE slct) : s ⟧ =
    ⟦ Γ ⊢ ((SELECT * FROM1 a0 WHERE slct) UNION ALL (SELECT * FROM1 a1 WHERE slct)) : s ⟧.
  Proof.
    simpl.
    by_extensionality g.
    by_extensionality t.
    match goal with
    | |- ?X * (?Y + ?Z) = _ => 
      generalize X Y Z; clear; intros x y z
    end.
    rewrite (path_universe_uncurried (sum_distrib_l x y z)).
    reflexivity.
  Qed.
  
  Lemma productDistributesOverUnion Γ s s01 a a0 a1 :
    ⟦ Γ ⊢ (SELECT * FROM2 a, (a0 UNION ALL a1)) : (s ++ s01) ⟧ = 
    ⟦ Γ ⊢ ((SELECT * FROM2 a, a0) UNION ALL (SELECT * FROM2 a, a1)) : (s ++ s01) ⟧.
  Proof.
    simpl.
    by_extensionality g.
    by_extensionality t.
    match goal with
    | |- ?X * (?Y + ?Z) = _ => 
      generalize X Y Z; clear; intros x y z
    end.
    rewrite (path_universe_uncurried (sum_distrib_l _ _ _)).
    reflexivity.
  Qed.

  Lemma joinCommute  Γ s1 s2 (a:SQL Γ s1) (b:SQL Γ s2):
              ⟦ Γ ⊢ (project (combine (right⋅right⋅star) (right⋅left⋅star))
                              (FROM b, a) ) : (s1 ++ s2) ⟧ =
              ⟦ Γ ⊢ (FROM a, b) : (s1 ++ s2) ⟧.
  Proof.
    simpl.
    by_extensionality g.
    by_extensionality t.
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried sumPair).
    rewrite <- (path_universe_uncurried eqSum).
    reflexivity.
  Qed.

  Variable sqlUnit : type.
  Variable sqlTt  : constant sqlUnit.
  Variable denoteSqlUnit : ⟦ sqlUnit ⟧ = Unit.

  Definition DenoteSqlTt : Type.
    refine (⟦ sqlTt ⟧ = _).
    rewrite denoteSqlUnit.
    exact tt.
  Defined.

  Variable denoteSqlTt : DenoteSqlTt. 

  Variable unitTable : relation (leaf sqlUnit).

  Variable denoteUnitTable : ⟦ unitTable ⟧ = (fun _ => Unit).

  Lemma onePlusOneNeqOne : ~(Unit <~> Unit + Unit).
    intros h.
    destruct h as [f [g eq _ _]].
    unfold Sect in eq.
    refine ((fun eql => _) (eq (inl tt))).
    refine ((fun eqr => _) (eq (inr tt))).
    clear eq.
    destruct (g (inl tt)).
    destruct (g (inr tt)).
    clear g.
    rewrite eql in eqr; clear eql f.
    set (P := fun (x : Unit + Unit) => 
            match x with
            | inl _ => Unit
            | inr _ => Empty
            end).
    refine (paths_rec _ P _ _ eqr).
    exact tt.
  Qed.

End RelationalAlgebraOptimization.
