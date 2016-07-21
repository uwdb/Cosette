Require Import HoTT.
Require Import UnivalenceAxiom.

Notation "∑ x , T" := (sigT (fun x => T)) (at level 45) : type_scope.

Definition equiv_sum_sigma I (A B : I -> Type) : (∑ i, A i) + (∑ i, B i) <~> ∑ i, (A i + B i).
  refine (BuildEquiv _ _ _ _). {
    intros [ia|ib].
    + exact (ia.1 ; inl (ia.2)).
    + exact (ib.1 ; inr (ib.2)).
  }
  refine (BuildIsEquiv _ _ _ _ _ _ _). {
    intros iab.
    destruct (iab.2) as [a|b].
    * exact (inl (iab.1; a)).
    * exact (inr (iab.1; b)).
  }
  - intros [i [a|b]]; reflexivity.
  - intros [[i a]|[i b]]; reflexivity.
  - intros [[i a]|[i b]]; reflexivity.
Defined.

Definition equiv_prod_sigma I A (B: I -> Type): (A * ∑ i, B i )  <~> ∑ i, (A * B i).
  intros.
  refine (BuildEquiv _ _ _ _). {
    intro aib.
    destruct aib as [a ib].
    destruct ib as [i b].
    refine (i; (a, b)).
  }
  refine (BuildIsEquiv _ _ _ _ _ _ _). {
    intros iab.
    destruct iab as [i ab].
    destruct ab as [a b].
    refine (a, (i; b)).
  }
  - intros [i j]; reflexivity.
  - intros [i j]; reflexivity.
  - intros [i j]; reflexivity.
Defined.

Definition equiv_sigma_prod_symm :
  forall (A: Type) (P Q: A -> Type),
    ∑ a, (P a * Q a) <~> ∑ a, (Q a * P a).
  intros.
  refine (BuildEquiv _ _ _ _). {
    intros apq.
    destruct apq as [a [p q]].
    refine (a; (q, p)).
  }
  refine (BuildIsEquiv _ _ _ _ _ _ _). {
    intros aqp.
    destruct aqp as [a [q p]].
    refine (a; (p, q)).
  }
  - intros [? ?]; reflexivity.
  - intros [? ?]; reflexivity.
  - intros [? ?]; reflexivity.  
Defined.

Axiom lem : forall P:hProp, P + ~P.

Definition hprop_prod_lem_l {A B} {P:hProp} : (P -> (A <~> B)) -> (~P -> B <~> Empty) -> P * A <~> B.
  intros f g.
  destruct (lem P) as [p|p].
  - rewrite (path_universe_uncurried (if_hprop_then_equiv_Unit _ p)).
    rewrite (path_universe_uncurried (f p)).
    apply prod_unit_l.
  - rewrite (path_universe_uncurried (if_not_hprop_then_equiv_Empty _ p)).
    rewrite (path_universe_uncurried (g p)).
    apply prod_empty_l.
Defined.

Lemma hprop_prod_r_eq {A B P} : (P -> A <~> B) -> P * A <~> P * B.
Proof.
  intros F. 
  exact ((equiv_sigma_prod0 P B) oE (equiv_functor_sigma_id F) oE (equiv_sigma_prod0 P A)^-1). 
Qed.

Lemma hprop_prod_l {A} {P:hProp} (f:A->P) : P * A <~> A.
  refine (BuildEquiv _ _ _ _). {
    exact snd.
  }
  refine (BuildIsEquiv _ _ _ _ _ _ _). {
    exact (fun a => (f a, a)).
  } 
  - intro.
    reflexivity.
  - intros [? ?]. 
    f_ap.
    exact (equiv_hprop_allpath _ _ _ _).
  - intros [? ?].
    cbn.
    match goal with |- context[match ?E with _ => _ end] => destruct E end.
    reflexivity.
Defined.

Lemma hprop_prod_l' {P A} `{IsHProp P} (f: A->P): P*A <~> A.
  apply (@hprop_prod_l A (BuildhProp P) f).
Defined.

Definition hprop_prod_prod (A:hProp) : A * A <~> A.
  exact (hprop_prod_l idmap).
Defined.

Definition merely_prod_l A : (merely A) * A <~> A.
  exact (hprop_prod_l tr).
Defined.

Definition hand (P Q:hProp) : hProp := 
  BuildhProp (P * Q).

Definition hnot (P:hProp) : hProp := 
  BuildhProp (~P).

Definition trunc_prod_l {A}: Trunc (-1) A * Trunc (-1) A = Trunc (-1) A.
  apply path_universe_uncurried.
  apply equiv_iff_hprop_uncurried.
  constructor.
  + intros [a1 a2].
    exact a1.
  + intros a1.
    exact (a1, a1).
Defined.

Definition trunc_eq_refl {A} {a b:A}: Trunc (-1) (a = b) = Trunc (-1) (b = a). 
  apply path_universe_uncurried.
  apply equiv_iff_hprop_uncurried.
  constructor.
  + intro l.
    strip_truncations.
    symmetry in l.
    exact (tr l).
  + intro r.
    strip_truncations.
    symmetry in r.
    exact (tr r).
Defined.

Lemma sumPair {A B C} : {ab : A * B & C ab} <~> {ba : B * A & C (snd ba, fst ba)}.
  refine (BuildEquiv _ _ _ _). {
    intros [[a b] c].
    exists (b,a).
    exact c.
  }
  refine (BuildIsEquiv _ _ _ _ _ _ _). {
    intros [[b a] c].
    exists (a,b).
    exact c.
  }
  - unfold Sect.
    intros [[b a] c].
    reflexivity.
  - unfold Sect.
    intros [[a b] c].
    reflexivity.
  - cbn.
    intros.
    reflexivity.
Qed.


Lemma eqSum {A P} {x:A} : P x <~> ∑ x', P x' * (x' = x).
  refine (BuildEquiv _ _ _ _). {
    intros p.
    exists x.
    refine (p,_).
    reflexivity.
  }
  refine (BuildIsEquiv _ _ _ _ _ _ _). {
    intros [x' [p eq]].
    destruct eq.
    exact p.
  }
  - intros [x' [p eq]].
    cbn in eq.
    destruct eq.
    reflexivity.
  - unfold Sect.
    intros.
    reflexivity.
  - intros.
    cbn.
    reflexivity.
Qed.

 Lemma prod_eq_assoc {B} `{IsHSet B}: forall (A:Type) (ta tb t: B),
      (A -> (ta = tb)) -> (A * (ta = t) = A * (tb = t)).
  Proof.
    intros A ta tb t h.
    assert ((ta = tb) * A = A) as h1. {
      apply path_universe_uncurried.
      apply hprop_prod_l'.
      exact h. }
    rewrite <- h1.
    assert ((ta = t) * (ta = tb) <~> (tb = t) * (ta = tb)) as h2. {
      apply equiv_iff_hprop_uncurried.
      constructor.
      + intros [H1 H2].
        refine (_, H2).
        rewrite <- H2.
        exact H1.
      + intros [H1 H2].
        refine (_, H2).
        rewrite H2.
        exact H1. }
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried h2).
    reflexivity.
  Defined.

  Lemma sum_pair_split {A B C D} :
    {ab: A * B & (C (fst ab) * D (snd ab))}
      <~> {a: A & C a * {b: B & D b}}.
  Proof.
    refine (BuildEquiv _ _ _ _). {
      intros [[a b] [c d]].
      exists a.
      refine (c, _).
      exists b.
      exact d. }
    refine (BuildIsEquiv _ _ _ _ _ _ _). {
      intros [a [c [b d]]].
      exists (a, b).
      exact (c, d).
    }
    + unfold Sect.
      intros [a [c [b d]]].
      reflexivity.
    + unfold Sect.
      intros [[a b] [c d]].
      reflexivity.
    + intros [[a b] [c d]].
      cbn.
      reflexivity.
  Defined.

  Lemma agg_sum {A B C D} :
    {a:A & C a * {b: B & D a b}} <~> {ab: A * B & C (fst ab) * D (fst ab) (snd ab)}.
  Proof.
    refine (BuildEquiv _ _ _ _). {
      intros [a [c [b d]]].
      exists (a, b).
      exact (c, d). }
    refine (BuildIsEquiv _ _ _ _ _ _ _ ). {
      intros [[a b] [c d]].
      exists a.
      exact (c, (b; d)). }
    + unfold Sect.
      intros [[a b] [c d]].
      reflexivity.
    + unfold Sect.
      intros [a [c [b d]]].
      reflexivity.
    + intros [a [c [b d]]].
      cbn.
      reflexivity.
  Defined.

  Lemma binderx {A}: forall f1 f2,
      (forall x:A, f1 x = f2 x) -> (∑ x, f1 x = ∑ x, f2 x).
    intros.
    f_ap.
    by_extensionality x.
  Defined.

  Lemma sum_assoc {A B C D}:
    {abc: A * B * C & D abc } <~> {bc: B * C & {a: A & D (a, (fst bc), (snd bc))}}.
  Proof.
    refine (BuildEquiv _ _ _ _). {
      intros [[[a b] c] d].
      exact ((b, c); (a; d)). }
    refine (BuildIsEquiv _ _ _ _ _ _ _). {
      intros [[b c] [a d]].
      exact ((a, b, c); d). }
    + unfold Sect.
      intros [[b c] [a d]].
      reflexivity.
    + unfold Sect.
      intros [[[a b] c] d].
      reflexivity.
    + intros [[[a b] c] d].
      cbn.
      reflexivity.
  Defined.

  Lemma sum_prod_assoc {A B C D}:
    {a: A & (B a) * ((C a) * (D a))} <~> {a:A & (B a) * (C a) * (D a)}.
  Proof.
    refine (BuildEquiv _ _ _ _). {
      intros [a [b [c d]]].
      exact (a; (b, c, d)). }
    refine (BuildIsEquiv _ _ _ _ _ _ _). {
      intros [a [[b c] d]].
      exact (a; (b, (c, d))). }
    + unfold Sect.
      reflexivity.
    + unfold Sect.
      reflexivity.
    + unfold Sect.
      reflexivity.
   Defined.

  Definition equiv_prod_sigma_r I A (B: I -> Type):
      ∑ i, (B i) * A <~> (∑ i, B i) * A .
  Proof.
    refine (BuildEquiv _ _ _ _). {
      intros [i [b a]].
      exact ((i; b), a). }
    refine (BuildIsEquiv _ _ _ _ _ _ _). {
      intros [[i b] a].
      exact (i; (b, a)). }
    + unfold Sect.
      reflexivity.
    + unfold Sect.
      reflexivity.
    + unfold Sect.
      reflexivity.
  Defined.

  Definition unit_eq: forall g:Unit, g = tt.
    intro.
    apply equiv_path_unit.
    exact g.
  Defined.

  Definition pair_f_eq {A B}: forall (a1 a2: A) (b1 b2: B),
      (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2).
    intros.
    constructor.
    + assert (fst (a1, b1) = fst (a2, b2)).
      * rewrite X.
        reflexivity.
      * assumption.
    + assert (snd (a1, b1) = snd (a2, b2)).
      * rewrite X.
        reflexivity.
      * assumption.
  Defined.
