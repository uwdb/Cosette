Require Import HoTT.
Require Import UnivalenceAxiom.

Notation "∑ x , T" := (sigT (fun x => T)) (at level 45) : type_scope.

Ltac start := 
  let g := fresh "g" in
  let t := fresh "t" in
  simpl;
  by_extensionality g;
  by_extensionality t.

Ltac simp_solve :=
    first [reflexivity | assumption].

Ltac break_and_rewrite :=
  repeat match goal with
    | |- ?A -> ?B => intros
    | t: ?A * ?B |- _ => destruct t
    | t: _ = _ |- _ => destruct t
    | |- ?A * ?B => constructor
    | |- _ => try first [simp_solve | symmetry; simp_solve] 
    end.

Ltac break_and_rewrite_trunc' :=
     match goal with
        | |- ?A -> ?B => intros
        | t: ?A * ?B |- _ => destruct t
        | t: (_, _) = (_, _) |- _ => rewrite <- (path_universe_uncurried (equiv_path_prod _ _)) in t; simpl in *
        | t: _ = _ |- _ => destruct t
        | |- ?A * ?B => constructor
        | t: { _ : ?T & _ } |- _ => destruct t
        | t: Trunc (-1) _ |- _ => strip_truncations
       end.

Ltac simp_solve' := try first [simp_solve | symmetry; simp_solve].

Ltac break_and_rewrite_trunc := repeat first [simp_solve | break_and_rewrite_trunc'].

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

Definition equiv_sum_sigma I (A B : I -> Type) : (∑ i, A i) + (∑ i, B i) <~> ∑ i, (A i + B i).
  simple refine (BuildEquiv _ _ _ _). {
    intros [ia|ib].
    + exact (ia.1 ; inl (ia.2)).
    + exact (ib.1 ; inr (ib.2)).
  }
  simple refine (BuildIsEquiv _ _ _ _ _ _ _). {
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
  simple refine (BuildEquiv _ _ _ _). {
    intro aib.
    destruct aib as [a ib].
    destruct ib as [i b].
    refine (i; (a, b)).
  }
  simple refine (BuildIsEquiv _ _ _ _ _ _ _). {
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
  simple refine (BuildEquiv _ _ _ _). {
    intros apq.
    destruct apq as [a [p q]].
    refine (a; (q, p)).
  }
  simple refine (BuildIsEquiv _ _ _ _ _ _ _). {
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
  simple refine (BuildEquiv _ _ _ _). {
    exact snd.
  }
  simple refine (BuildIsEquiv _ _ _ _ _ _ _). {
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

Lemma unit_idenpotent:
    forall (A:Type) (B:Type), (A -> B <~> Unit) -> A * B <~> A.
  Proof.
    intros A B H.
    apply hprop_prod_r_eq in H.
    rewrite (path_universe_uncurried (prod_unit_r A)) in H.
    exact H.
  Defined.

Lemma sumPair {A B C} : {ab : A * B & C ab} <~> {ba : B * A & C (snd ba, fst ba)}.
  simple refine (BuildEquiv _ _ _ _). {
    intros [[a b] c].
    exists (b,a).
    exact c.
  }
  simple refine (BuildIsEquiv _ _ _ _ _ _ _). {
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
  simple refine (BuildEquiv _ _ _ _). {
    intros p.
    exists x.
    refine (p,_).
    reflexivity.
  }
  simple refine (BuildIsEquiv _ _ _ _ _ _ _). {
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
  simple refine (BuildEquiv _ _ _ _). {
    intros [[a b] [c d]].
    exists a.
    refine (c, _).
    exists b.
    exact d. }
  simple refine (BuildIsEquiv _ _ _ _ _ _ _). {
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
  simple refine (BuildEquiv _ _ _ _). {
    intros [a [c [b d]]].
    exists (a, b).
    exact (c, d). }
  simple refine (BuildIsEquiv _ _ _ _ _ _ _ ). {
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
  simple refine (BuildEquiv _ _ _ _). {
    intros [[[a b] c] d].
    exact ((b, c); (a; d)). }
  simple refine (BuildIsEquiv _ _ _ _ _ _ _). {
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

Lemma equiv_sigma_prod_assoc {A B C D}:
  {a: A & (B a) * ((C a) * (D a))} <~> {a:A & (B a) * (C a) * (D a)}.
Proof.
  simple refine (BuildEquiv _ _ _ _). {
    intros [a [b [c d]]].
    exact (a; (b, c, d)). }
  simple refine (BuildIsEquiv _ _ _ _ _ _ _). {
    intros [a [[b c] d]].
    exact (a; (b, (c, d))). }
  + unfold Sect.
    reflexivity.
  + unfold Sect.
    reflexivity.
  + unfold Sect.
    reflexivity.
 Defined.

  Lemma sum_pair_split' {A B C}:
    {ab: A * B & C ab} <~> {a:A & {b:B & C (a, b)}}.
  Proof.
    simple refine (BuildEquiv _ _ _ _). {
      intros [[a b] c].
      exists a.
      exists b.
      exact c. }
    simple refine (BuildIsEquiv _ _ _ _ _ _ _). {
      intros [a [b c]].
      exists (a, b).
      exact c. }
    + unfold Sect.
      intros.
      reflexivity.
    + unfold Sect.
      intros.
      reflexivity.
    + reflexivity.
  Qed.

Definition equiv_prod_sigma_r I A (B: I -> Type):
    ∑ i, (B i) * A <~> (∑ i, B i) * A .
Proof.
  simple refine (BuildEquiv _ _ _ _). {
    intros [i [b a]].
    exact ((i; b), a). }
  simple refine (BuildIsEquiv _ _ _ _ _ _ _). {
    intros [[i b] a].
    exact (i; (b, a)). }
  + unfold Sect.
    reflexivity.
  + unfold Sect.
    reflexivity.
  + unfold Sect.
    reflexivity.
Defined.

  Lemma equiv_sigma_prod_symm_m {A B C D E}:
    {a: A & B a * ((C a) * (D a)) * E a} <~> {a:A & B a * (D a * C a) * E a}.
  Proof.
    apply equiv_path.
    f_ap.
    by_extensionality a.    
    rewrite (path_universe_uncurried (equiv_prod_symm (C a) (D a))).
    reflexivity.
  Defined.

  Lemma equiv_sigma_sigma_prod {A B C D}:
    {a: A & B a * {c:C & D a c}} = {a: A & {c:C & B a * D a c}}.
  Proof.
    f_ap.
    by_extensionality a.
    apply path_universe_uncurried.
    refine (equiv_prod_sigma _ _ _).
  Defined.

  Lemma equiv_sigma_eq_subst {A B}:
    forall a1:A, {a0:A & (a0 = a1) * B a0} <~> B a1.
  Proof.
    intro a1.
    simple refine (BuildEquiv _ _ _ _). {
      intros [a0 [e ba1]].
      rewrite e in ba1.
      exact ba1. }
    simple refine (BuildIsEquiv _ _ _ _ _ _ _). {
      intros ba1.
      refine (a1; (_, _)).
      reflexivity.
      exact ba1. }
    + unfold Sect.
      intro x.
      reflexivity.
    + unfold Sect.
      intros [a0 [e ba0]].
      destruct e.
      reflexivity.
    + intros [a0 [e ba0]].
      destruct e.
      reflexivity.
  Defined.

  Lemma equiv_sigma_eq_subst_r {A B}:
    forall a1:A, {a0:A & (a1 = a0) * B a0} <~> B a1.
  Proof.
    intro a1.
     simple refine (BuildEquiv _ _ _ _). {
      intros [a0 [e ba1]].
      destruct e.
      exact ba1. }
     simple refine (BuildIsEquiv _ _ _ _ _ _ _). {
       intros ba1.
       refine (a1; (_, _)).
       reflexivity.
       exact ba1. }
    + unfold Sect.
      intros.
      reflexivity.
    + unfold Sect.
      intros [a0 [e ba0]].
      destruct e.
      reflexivity.
    + intros [a0 [e ba0]].
      destruct e.
      reflexivity.
  Defined.

  Lemma equiv_sigma_eq_subst' {A B}:
    forall a1:A, {a0:A &  B a0 * (a0 = a1)} <~> B a1.
  Proof.
    intro a1.
    rewrite <- (path_universe_uncurried (equiv_sigma_eq_subst a1)).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    apply equiv_path.
    reflexivity.
  Defined.

  Lemma equiv_sigma_eq_subst_r' {A B}:
    forall a1:A, {a0:A &  B a0 * (a1 = a0)} <~> B a1.
  Proof.
    intro a1.
    rewrite <- (path_universe_uncurried (equiv_sigma_eq_subst_r a1)).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    apply equiv_path.
    reflexivity.
  Defined.

  Lemma equiv_2sigma_eq_subst {A B C}:
    forall (f: A -> B),
      {a:A & {b0:B & (b0 = f a) * C a b0}} = {a: A & C a (f a)}.
  Proof.
    intros f.
    f_ap.
    by_extensionality a.
    exact (path_universe_uncurried (equiv_sigma_eq_subst (f a))).
  Defined.

  Lemma equiv_2sigma_eq_subst_r {A B C}:
    forall (f: A -> B),
      {a:A & {b0:B & (f a = b0) * C a b0}} = {a: A & C a (f a)}.
  Proof.
    intros f.
    f_ap.
    by_extensionality a.
    exact (path_universe_uncurried (equiv_sigma_eq_subst_r (f a))).
  Defined.

  Lemma equiv_2sigma_prod_assoc {A B C D E}:
    {a: A & {b: B & C a b * (D a b * E a b)}} <~> {a: A & {b: B & C a b * D a b * E a b}}.
  Proof.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    reflexivity.
  Defined.

  Lemma equiv_2sigma_prod_symm {A B C D}:
    {a: A & {b: B & C a b * D a b}} <~> {a: A & {b: B & D a b * C a b}}.
  Proof.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
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

 Lemma equiv_pair_assemble {A B} `{IsHSet A} `{IsHSet B} {a:A} {b:B}:
    forall c:A*B, ((a,b) = c) <~> (a = (fst c))* (b = (snd c)).
  Proof.
    intros c.
    apply equiv_iff_hprop_uncurried.
    constructor.
    + intros p. rewrite <- p. simpl.
      constructor; reflexivity.
    + intros [p1 p2].
      rewrite p1. rewrite p2.
      reflexivity.
  Defined.


Definition equiv_sig_sum_prod_distr_l {A B C D}:
  {a: A & B a * (C a + D a)} <~> {a:A & B a * C a + B a * D a}.
  apply equiv_path.
  f_ap.
  by_extensionality a.
  rewrite (path_universe_uncurried (sum_distrib_l _ _ _)).
  reflexivity.
Defined.

Definition equiv_sig_sum_prod_distr_r {A B C D}:
  {a: A & (C a + D a) * B a} <~> {a:A & C a * B a + D a * B a}.
  apply equiv_path.
  f_ap.
  by_extensionality a.
  rewrite (path_universe_uncurried (sum_distrib_r _ _ _)).
  reflexivity.
 Defined.

Definition equiv_sig_break_pair {A B T1} `{IsHSet A} `{IsHSet T1}:
  forall (t1: T1) (t2:T1*A), {a: A & B a * ((t1, a) = t2)} = {a: A & B a * (t1 = fst t2) * (a = snd t2)}.
  intros.
  f_ap.
  by_extensionality a.
  rewrite (path_universe_uncurried (equiv_pair_assemble _)).
  rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
  reflexivity.
Defined.
  
Definition equiv_prod_2sigma_r {A B C D}:
  {a: A &  {b:B & C a b} * D a } <~> {a: A & {b:B & C a b * D a}}.
  apply equiv_path.
  f_ap.
  by_extensionality a.
  rewrite (path_universe_uncurried (equiv_prod_sigma_r _ _ _)).
  reflexivity.
Defined.

Definition hprop_prod_trunc {A B} `{IsHProp A}:
    A * Trunc(-1) B <~> Trunc(-1) (A * B).
    apply equiv_iff_hprop_uncurried.
    constructor.
    + intros [a b].
      strip_truncations.
      apply tr.
      exact (a, b).
    + intros ab.
      strip_truncations.
      destruct ab as [a b].
      refine (a, tr b).
  Defined.

  Definition hprop_prod_trunc_r {A B} `{IsHProp B}:
    Trunc (-1) A * B <~> Trunc(-1) (A * B).
    apply equiv_iff_hprop_uncurried.
    constructor.
    + intros [a b].
      strip_truncations.
      apply tr.
      exact (a, b).
    + intros ab.
      strip_truncations.
      destruct ab as [a b].
      refine (tr a, b).
  Defined.
  
  Definition hprop_prod_trunc_in_sig {A:Type} {B: A -> hProp} {C D: A -> Type}:
    {a:A & B a * Trunc (-1) (C a) * D a} <~> {a:A & Trunc (-1) (B a * C a) * D a}.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried hprop_prod_trunc).
    reflexivity.
  Defined.

  Definition hprop_prod_trunc_in_sig_r {A:Type} {B: A -> Type} {C: A -> hProp}:
    {a:A & Trunc (-1) (B a) * C a} <~> {a:A & Trunc (-1) (B a * C a)}.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried hprop_prod_trunc_r).
    reflexivity.
  Defined.

  Definition equiv_sig_break_pair_f {A B C D} `{IsHSet A} `{IsHSet C} `{IsHSet D}:
  forall (f: A -> C * D) (t:C * D), {a: A & B a * (f a = t)} = {a: A & B a * ((fst (f a)) = fst t) * ((snd (f a)) = snd t)}.
  intros.
  f_ap.
  by_extensionality a.
  rewrite (path_universe_uncurried (equiv_pair_assemble _)).
  rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
  reflexivity.
Defined.

Definition path_trans {A} `{IsHSet A}:
    forall (a b c: A), (a = b) * (a = c) <~> (a = b) * (a = c) * (b = c).
    intros a b c.
    apply equiv_iff_hprop_uncurried.
    constructor; break_and_rewrite.
  Defined.
  
Definition path_trans_pred {A} {P: A -> hProp} `{IsHSet A}:
    forall (a b: A), (a = b) * P a = (a = b) * P a * P b.
    intros.
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor; break_and_rewrite.
  Defined.

Definition equiv_sigma_prod_assoc_h {A B C D E}:
    {a: A & B a * ((C a) * (D a)) * E a} <~> {a:A & B a * C a * D a * E a}.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    reflexivity.
  Defined.
 
Definition equiv_prod_eq_subst {A B}:
    forall (a1 a2:A), (a1 = a2) * B a1 <~> (a1 = a2) * B a2.
    intros a1 a2.
    simple refine (BuildEquiv _ _ _ _). {
      intros [h b].
      destruct h.
      refine (_, b).
      reflexivity. }
    simple refine (BuildIsEquiv _ _ _ _ _ _ _). {
      intros [h b].
      destruct h.
      refine (_, b).
      reflexivity. }
    + unfold Sect.
      intros [h b].
      destruct h.
      reflexivity.
    + unfold Sect.
      intros [h b].
      destruct h.
      reflexivity.
    + intros [h b].
      destruct h.
      reflexivity.
  Defined.

Lemma sum2_pair_split {D A B C}:
    {d: D & {ab: A * B & C d ab}} <~> {d:D & {a:A & {b:B & C d (a, b)}}}.
  Proof.
  apply equiv_path.
  f_ap.
  by_extensionality d.
  exact (path_universe_uncurried sum_pair_split').
  Defined.

Lemma sigma_path_trans_l {A B E f} `{IsHSet B}:
  forall (b c:B),
    {a:A & (b = c) * (b = f a) * E a } <~> {a:A & (b = c) * (b = f a) * (c = f a) * E a}.
  Proof.
    intros.
    apply equiv_path.
    f_ap.
    by_extensionality a0.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    symmetry.
    exact (path_universe_uncurried (path_trans b c _)).
  Defined.

 
Lemma sigma_path_trans_l' {A B E f} `{IsHSet B}:
    forall (b c:B),
      {a:A & (b = c) * (c = f a) * E a } <~> {a:A & (b = c) * (b = f a) * (c = f a) * E a}.
  Proof.
    intros.
    apply equiv_path.
    f_ap.
    by_extensionality a0.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor;
    break_and_rewrite.
  Defined.

Lemma sigma_prod_path_symm' {A B D} `{IsHSet B}:
    forall (b: B) (f: A -> B), {a:A & (b = f a) * D a} <~> {a:A & (f a = b) * D a}.
  Proof.
    intros.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor;
    break_and_rewrite.
  Defined.

Lemma equiv_sigma_prod_symm_f {A B C D}:
    {a: A & B a * C a * D a} <~> {a:A & C a * B a * D a}.
  Proof.
    apply equiv_path.
    f_ap.
    by_extensionality a.    
    rewrite (path_universe_uncurried (equiv_prod_symm (B a) (C a))).
    reflexivity.
  Defined.

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

  Definition hset_eq_symm {A} `{IsHSet A}:
    forall (a b:A), (a = b) <~> (b = a).
    intros.
    apply equiv_iff_hprop_uncurried.
    constructor; break_and_rewrite.
  Defined.

  Lemma equiv_sigma_prod_symm_t {A B C D}:
    {a: A & B a * C a * D a} <~> {a:A & B a * D a * C a}.
  Proof.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm (C a) (D a))).
    reflexivity.
  Defined.

  Definition equiv_sig_break_pair_f' {A B C D} `{IsHSet C} `{IsHSet D}:
    forall (f1:A -> C) (f2: A -> D) f3 f4, {a: A & B a * ((f1 a, f2 a) = (f3 a, f4 a))} = {a: A & B a * (f1 a = f3 a) * (f2 a = f4 a)}.    
    intros.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried (equiv_pair_assemble _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    reflexivity.
  Defined.

  Definition hprop_prod_path_trunc_in_sig {A:Type} {B} {C D: A -> Type} `{IsHSet B}:
    forall (f1 f2: A -> B), {a:A & (f1 a = f2 a) * Trunc (-1) (C a) * D a} <~> {a:A & Trunc (-1) ((f1 a = f2 a) * C a) * D a}.
    intros b c.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried hprop_prod_trunc).
    reflexivity.
  Defined.

    Definition equiv_sig_trunc_break_pair_f' {A B C D E F} `{IsHSet E} `{IsHSet F}:
    forall (f1:A -> C -> E) (f2: A -> C -> F) f3 f4,
      {a: A &  B a * Trunc (-1) {c:C & D a c * ((f1 a c, f2 a c) = (f3 a c, f4 a c))}} = {a: A & B a * Trunc (-1) {c:C & D a c * (f1 a c = f3 a c) * (f2 a c = f4 a c)}}.
  Proof.
    intros.
    f_ap.
    by_extensionality a.
    f_ap.
    f_ap.
    f_ap.
    by_extensionality c.
    rewrite (path_universe_uncurried (equiv_pair_assemble _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    reflexivity.
  Defined.
  
  Definition equiv_prod_2sigma_trunc_r {A B C D E}:
    {a: A & E a * Trunc (-1)({b:B & C a b} * D a) } <~> {a: A & E a * Trunc (-1) {b:B & C a b * D a}}.
  Proof.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    f_ap.
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_sigma_r _ _ _)).
    reflexivity.
  Defined.

  Definition equiv_sig_trunc_prod_hset {A B} {C D: A -> Type} `{IsHSet B}: 
    forall (f1 f2: A -> B), {a:A & Trunc (-1) (C a) * (f1 a = f2 a) * D a} <~> {a:A & Trunc (-1) ((C a) * (f1 a = f2 a)) * D a}.
  Proof.
    intros.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried hprop_prod_trunc_r).
    reflexivity.
  Defined.

  Lemma equiv_2sigma_prod_assoc_m {A B C D E F}:
    {a: A & {b: B & C a b * (D a b * E a b) * F a b}} <~> {a: A & {b: B & C a b * D a b * E a b * F a b}}.
  Proof.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc_h).
    reflexivity.
  Defined.

  Lemma equiv_2sigma_prod_symm_m {A B C D E F}:
    {a: A & {b: B & C a b * D a b * E a b * F a b}} <~> {a: A & {b: B & C a b * E a b * D a b * F a b}}.
  Proof.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite <- (path_universe_uncurried equiv_sigma_prod_assoc_h).
    rewrite (path_universe_uncurried equiv_sigma_prod_symm_m).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc_h).
    reflexivity.
  Defined.

  Lemma equiv_2sigma_prod_symm_h {A B C D E}:
    {a: A & {b: B & C a b * D a b * E a b}} <~> {a: A & {b: B & D a b * C a b * E a b}}.
  Proof.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    f_ap.
    by_extensionality b.
    rewrite (path_universe_uncurried (equiv_prod_symm (C a b) _)).
    reflexivity.
  Defined.

  Lemma equiv_2sigma_path_trans_reduce_r {A B C D} `{IsHSet D}:
  forall (fa fb fc: A -> B -> D),
    {a:A & {b: B & C a b * (fa a b = fb a b) * (fa a b = fc a b)}} <~> {a:A & {b: B & C a b * (fa a b = fb a b) * (fb a b = fc a b)}}.
  Proof.
    intros.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    f_ap.
    by_extensionality b.
    repeat rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    f_ap.
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor;
    break_and_rewrite.
  Defined.

  Lemma sigma_prod_path_symm {A B D} `{IsHSet B}:
    forall (f1 f2: A -> B), {a:A & (f1 a = f2 a) * D a} <~> {a:A & (f2 a = f1 a) * D a}.
  Proof.
    intros.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor;
    break_and_rewrite.
  Defined.

  Lemma equiv_prod_sigma_prod {A B C D E}:
  {a: A & E a * {b:B & C a b} * D a } <~> {a: A & E a * {b:B & C a b * D a}}.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried (equiv_prod_sigma_r _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    reflexivity.
  Defined.
