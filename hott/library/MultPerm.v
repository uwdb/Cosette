Require Import HoTT.
Require Import UnivalenceAxiom.
Require Import list peano_naturals Bool.
(* Require Import Coq.Init.Logic_Type. *)

Import ListNotations.

(** Goal: prove equality of products types upto permutation **)
(***)
(* denotePred gt (denoteProj itp_np e, ⟦ integer_1000 ⟧) * (denoteProj itp_itemno e = denoteProj itm_itemno a) * *)
(* (⟦ rel_itp ⟧ (fst (e, a)) * ⟦ rel_itm ⟧ (snd (e, a))) * *)
(* ((denoteProj itp_np e, (denoteProj itm_type a, denoteProj itm_itemno a)) = (t1, (t2, t3)) *)

Set Implicit Arguments.

(** tools *)
Fixpoint nth_error {A : Type} (l : list A) (n : nat) {struct n} : option A :=
  match n, l with
  | O, x :: _ => Some x
  | S n, _ :: l => nth_error l n
  | _ , _ => None
  end.

Definition nth_default {A : Type} (default : A) (l : list A) (n : nat) : A :=
  match nth_error l n with
  | Some x => x
  | None   => default
  end.


(** computation *)
Lemma le_lt_dec : forall a b : nat, (canonical_names.le a b) \/ (canonical_names.lt b a).
Proof.
induction a as [|a IHa].
- intros;left;apply zero_least.
- intros [|b].
  + right. apply lt_0_S.
  + destruct (IHa b).
    * left. apply le_S_S;trivial.
    * right. apply le_S_S. trivial.
Defined.


Global Instance nat_le_dec_compute: forall x y : nat, Decidable (canonical_names.le x y).
Proof.
intros a b. destruct (le_lt_dec a b).
- left; trivial.
- right. apply nat_lt_not_le. trivial.
Defined.

Definition decidable_bool {A : Type} (dec : Decidable A) : Bool :=
  match dec with
  | inl _ => true
  | inr _ => false
  end.

(* Coercion decidable_bool : (Decidable A) >-> bool. *)



(** monoid reflection *)
Section reflection.
  Definition A := Type.
  Definition zero : A := Unit.
  Definition add : A -> A -> A := prod.
  (* Parameter A : Type. *)
  (* Parameter zero : A. *)
  (* Parameter add : A -> A -> A. *)

  Notation " x + y " := (add x y).

  (* properties about the monoid we want *)
  Parameter add_z_left : forall (a : A), zero + a = a.
  Parameter add_z_right : forall (a : A), a + zero = a.
  Parameter comm : forall (a b : A), a + b = b + a.
  Parameter assoc : forall (a b c : A), a + b + c = a + (b + c).


  Definition var := nat. (* for indexing variables in compact representation *)


  (**
a + b
->

Add 0 (Add 1 zero)
[a,b]

*)
  (* syntax *)
  Inductive term : Type :=
  | Zero : term
  | Add  : var -> term -> term.

  (* denotation of the syntax, back into the monoid *)
  (* xs is a list of used variables *)
  Fixpoint termD (xs : list A) (t : term) : A :=
    match t with
    | Zero => zero
    | Add x t => (nth_default zero xs x) + (termD xs t)
    end.

  (* compact representation: bag semantics, in Gallina *)
  Record summary :=
    {
      (* how many times the variable appear in the product/list? *)
      (* since var are simply nats, this list sorted in increasing order *)
      Vars : list (var * nat);
    }.

  Definition empty : summary :=
    {| Vars := nil |}.

  (* increment variable count *)
  Fixpoint increment (x : nat) (amount : nat) (ls : list (nat * nat)) : list (nat * nat).
    refine match ls with
           | nil => (x, amount) :: nil
           | (y,n) :: ls => _
           end.
    destruct (nat_dec x y).
    exact ((y, (amount + n)%nat) :: ls).
    destruct (nat_le_dec_compute y x).
    exact ((y,n) :: (increment x amount ls)).
    exact ((x, amount) :: (y, n) :: ls).
  Defined.

  Print increment.

  Definition summary1 := {| Vars := ((0,1) :: (1,2) :: nil) |}.
  Definition summary2 := {| Vars := ((0,2) :: (1,2) :: nil) |}.

  Eval compute in (increment 1 12 summary1.(Vars)).
  Eval vm_compute in (increment 1 12 nil).

  Definition add_var (s : summary) (x : var) :=
    {| Vars := increment x 1 s.(Vars)  |}
  .


  (* complie a term into a summary *)
  Fixpoint summarize (t : term) : summary :=
    match t with
    | Zero => empty
    | Add x t => add_var (summarize t) x
    end.

  Eval compute in (summarize (Add 1 (Add 2 (Add 2 Zero)))).


  (* decidable equality for summaries *)
  Definition isCons {A : Type} (l : list A) : Bool :=
    match l with
    | nil => true
    | _   => false
    end.

  Lemma l : forall {A : Type} (y : list A) (a : A),  ~(a :: y = y).
  Proof.
    induction y; intros.
    - intro contra. apply (ap isCons) in contra. simpl in contra.
      apply (not_fixed_negb true) in contra. assumption.
    - intro contra. 
      specialize (IHy a).
      pose (f := fun (xs : list A0) =>
                  match xs with
                  | b::xs' => xs'
                  | _ => nil
                  end).
      apply (ap f) in contra. simpl in contra.
      destruct (IHy contra).
  Qed.


  Definition list_dec : DecidablePaths (list (var * nat)).
  unfold DecidablePaths.
  induction x; induction y.
  (* + induction y. *)
    - exact (inl 1%path).
    - refine (inr _).
    intro contra.
    apply (ap isCons) in contra. simpl in contra.
    apply (not_fixed_negb false) in contra. destruct contra.
  (* + induction y. *)
    - refine (inr _).
      intro contra.
      apply (ap isCons) in contra. simpl in contra.
      apply (not_fixed_negb true) in contra. destruct contra.
    -
      inversion IHy.
      destruct IHy.
      specialize (IHx y).
      destruct IHx.
      rewrite p0 in p.
      apply l in p.
      destruct p.

      refine (inr _).
      rewrite p.
      intro contra.
      apply inverse in contra.
      apply l in contra.
      destruct contra.

      specialize (IHx (a0::y)).
      destruct IHx.
      rewrite p.
      refine (inr _).
      intro contra.
      admit.

      






      destruct p.
      rewrite <- p0 in p0.
      destruct x. admit.
      destruct p0.

      destruct IHy.
    refine (inr _).
    admit.
    intro contra.
    destruct IHy.
    admit.
    rewrite p in contra.
    apply (ap (fun 

  refine contra.
  destruct IHy.

  Fixpoint list_eq (s1 s2 : list (var * nat)) : Bool :=
    match s1, s2 with
    | nil, nil => true
    | (x1, n1) :: s1' , (x2, n2) :: s2' =>
      if (nat_dec x1 x2)
      then if (nat_dec n1 n2)
           then list_eq s1' s2'
           else false
      else false
      (* (decidable_bool (nat_dec x1 x2)) && (decidable_bool (nat_dec n1 n2)) && list_eq s1' s2' *)
    | _, _ => false
    end.

  
  Definition dec_fn (m n : nat) :=
    match nat_dec m n with
    | inl _ => Unit
    | inr _ => Empty
    end.

  (* Lemma l : decidable_bool (nat_dec m n) = true -> dec_fn m n *)

  (* Lemma nat_dec_bool_true : forall (n m : nat), nat_dec m n -> m = n. *)

  Lemma nat_dec_bool_true : forall (n m : nat),  decidable_bool (nat_dec m n) = true -> m = n.
    destruct m,n; intros.
    - reflexivity.
    - compute in *. apply (not_fixed_negb true) in X; destruct X.
    - compute in *. apply (not_fixed_negb true) in X; destruct X.
    - 
      Search "dec".
      Compute (nat_dec 1 1).
      compute in *.
  Admitted.


  Fixpoint summaries_eq (s1 s2 : summary) : Bool :=
    list_eq s1.(Vars) s2.(Vars).

  Eval compute in (summaries_eq summary1 summary2).
  
  (* translate a summary into a canonical term *)
  Fixpoint repeatVars (v : A) (n : nat) : list A :=
    match n with
    | O => nil
    | S n => v :: (repeatVars v n)
    end.

  (* turn a summary into a list representing the sum, then flatten it out  *)
  Fixpoint genvars (vs : list A) (vars : list (var * nat)) : list A :=
    match vars with
    | nil => nil
    | (x, n) :: vars' => (repeatVars (nth_default zero vs x) n) ++ (genvars vs vars')
    end.

  Fixpoint flatten (xs : list A) (acc : A) : A :=
    match xs with
    | nil => acc
    | a::xs' => flatten xs' (acc + a)
    end.

  Definition summaryD (vs : list A) (s : summary) : A :=
    flatten (genvars vs s.(Vars)) zero.

  (* some properties of the denotation *)

  Lemma andb_true_iff : forall a b : Bool, (andb a b) = true -> a = true /\ b = true.
  Proof.
    intros. destruct a, b; simpl in *.
    - exact (idpath, idpath).
    - apply (not_fixed_negb true) in X; destruct X.
    - apply (not_fixed_negb true) in X; destruct X.
    - apply (not_fixed_negb true) in X; destruct X.
  Defined.

  Lemma list_eq_correct : forall l1 l2,
      list_eq l1 l2 = true -> l1 = l2.
  Proof.
    induction l1 as [ | [ ] ]; destruct l2 as [ | [ ] ]; simpl.
    - intro; reflexivity.
    - intro h; apply (not_fixed_negb true) in h; destruct h.
    - intro h; apply (not_fixed_negb true) in h; destruct h.
    - intros.
      destruct (andb_true_iff _ _ X) as [p1 h1]. destruct (andb_true_iff _ _ p1) as [h2 h3].
      specialize (IHl1 _ h1). rewrite IHl1.
      apply nat_dec_bool_true in h2.
      apply nat_dec_bool_true in h3.
      rewrite h2; rewrite h3; reflexivity.
  Qed.

  Lemma summaries_eq_correct : forall s1 s2,
      summaries_eq s1 s2 = true -> s1 = s2.
  Proof.
    destruct s1, s2; unfold summaries_eq; simpl; intros.
    apply list_eq_correct in X.
    rewrite X; reflexivity.
  Qed.

  (* Lemma flatten_cons : forall lst a vs, *)
  (*   flatten (genvars vs (a::lst)) zero =  + (flatten (genvars vs lst) zero). *)

  Lemma flatten_incr : forall lst vs v ,
    flatten (genvars vs (increment v 1 lst)) zero = (nth_default zero vs v) + (flatten (genvars vs lst) zero).
  Proof.
    induction lst; intros.
    apply comm.

    Admitted.

  Theorem summaries_correct : forall vs t,
      (summaryD vs (summarize t)) = (termD vs t).
  Proof.
    induction t; unfold summaryD in *; simpl; auto.
    rewrite <- IHt.
    apply flatten_incr.
  Qed.


  Theorem reflection_correct : forall vs t1 t2,
      summaries_eq (summarize t1) (summarize t2) = true
      -> (termD vs t1) = (termD vs t2).
  Proof.
    intros.
    apply summaries_eq_correct in X.
    pose (Y := ap (fun y => summaryD vs y) X); simpl in Y.
    exact (concat (inverse (summaries_correct vs t1)) (concat Y (summaries_correct vs t2))).
  Qed.
End reflection.



(**
Example hello : test = test'.
Proof.
  apply path_universe_uncurried.
  simple refine (BuildEquiv _ _ _ _).
  {
    intro.
    exact (tt, tt, tt, tt).
  }
Qed.

Definition perm_ex1 : forall B C D E : Type, B * C * D * E -> C * D * B * E.
  intros.
  destruct X as [[[b c] d] e].
  exact (c, d, b, e).
Defined.

Print perm_ex1.


(* the permutation (132)(4) may be represented as the function
(fun X => 
  (fun bcd =>
    (fun bc =>
      (fun b c d e => (c,d,b,e)) (fst bc) (snd bc))
    (fst bcd) (snd bcd))
 (fst X) (snd X))
 *)


(** what is the pattern?


 *)

Definition perm_ex2 : forall B C D E : Type, B * C * D * E -> C * D * B * E :=
  fun B C D E : Type =>
  fun X : B * C * D * E =>
    (fun b c d e => (c, d, b, e)) (fst (fst (fst X))) (snd (fst (fst X))) (snd (fst X)) (snd X).

Check (1, 2, 3, 4).

Definition perm_ex3 : forall B C D E : Type, B * C * D * E -> C * D * B * E :=
  fun B C D E : Type =>
  fun X : B * C * D * E =>
    match X with
    | (b, c, d, e) => (c, d, b, e)
    end.

(**
the prodcut should have some inductive structure:

(b,c,d,e)
~=
(((b . c) . d) . e) : Tree ?
[b; c; d; e] : leftassoc list ?
 *)

Check (prod (prod Unit Unit) Unit).
 *)

(* Definition toList (T : Type) : list Type := *)
(*   match T with *)
(*   | prod A B => nil *)
(*   end. *)

(** concrete term -> Gallina syntax *)
Ltac reverse' p acc :=
  match p with
  | (add ?p1 ?p2) =>
    reverse' p1 (add p2 acc)
  end.

Ltac reverse p := reverse p zero.

(* Is [X] an element of list [L]? *)
Ltac inList X L :=
  match L with
  | nil => false
  | X :: _ => true
  | _ :: ?L' => inList X L'
  end.

(* Return a list of all unique "variables" in term [L].
 * [vs] is a list of variables that should be extended. *)
Ltac varsOf L vs :=
  match L with
  | (add ?L' ?x) =>
    let xs := varsOf L' vs in
    match inList x xs with
    | true => xs
    | false => constr:(x::xs)
    end
  end.


(* What is the numeric position of [X] in list [Xs]? *)
Ltac posnOf X Xs :=
  match Xs with
  | X :: _ => O
  | _ :: ?Xs' =>
    let n := posnOf X Xs' in
    constr:(S n)
  end.

Ltac reifyTerm vs p :=
  match p with
  | (add ?p1 ?p2) =>
    let x := posnOf p2 vs in
    let p' := reifyTerm vs p1 in
    constr:(Add x p')
  | _ =>
    let x := posnOf p vs in
    constr:(Add x zero)
  end.


Ltac reify :=
  match goal with
  | [ |- ?prod1 = ?prod2 ] =>
    let vs := varsOf prod1 (@nil A) in
    (* pose vs *)
    let tm1 := reifyTerm vs prod1 in
    let tm2 := reifyTerm vs prod2 in
    change ((termD zero vs tm1) = (termD zero vs tm2))
  end.


(**
(* Fixpoint add_denote (ls : list Type) : Type := *)
(*   match ls with *)
(*   | nil => Unit *)
(*   | t :: ls => add (add_denote ls) t *)
(*   end. *)

(* Ltac prove_permute := *)
(*   intros; *)
(*   match goal with *)
(*   | [ |- ?prod1 = ?prod2 ] => *)
(*     let p1 := reify prod1 in *)
(*     let p2 := reify prod2 in *)
(*     assert (add_denote p1 = add_denote p2) *)
(*   end. *)
*)

Ltac prod_to_add :=

Example two : forall B C : Type, B * C = C * B.
Proof.
  intros.
  reify.
  change ((add B C) = (add C B)).
  prove_permute.

Admitted.

Theorem prod_reflect : forall 

Example four : forall B C D E : Type, B * C * D * E = C * D * B * E.
Proof.
  intros.
  prove_permute.
  apply path_universe_uncurried.
  pose (f := (fun X : B * C * D * E => match X with | (b, c, d, e) => (c, d, b, e) end)).
  pose (g := (fun X : C * D * B * E => match X with | (c, d, b, e) => (b, c, d, e) end)).
  simple refine (BuildEquiv _ _ f (BuildIsEquiv _ _ f g _ _ _ )); (unfold Sect; intros; reflexivity).
Qed.

  intros;
  apply path_universe_uncurried;
  pose (f := (fun X : B * C * D * E => match X with | (b, c, d, e) => (c, d, b, e) end));
  pose (g := (fun X : C * D * B * E => match X with | (c, d, b, e) => (b, c, d, e) end));
  simple refine (BuildEquiv _ _ f (BuildIsEquiv _ _ f g _ _ _ )); (unfold Sect; intros; reflexivity).



(* example really_short : forall a b c : a, *)
(*     (a; b; c) = (c; b; a). *)
(* Proof. *)
(*   intros. *)
(*   rewrite symm. *)
(*   rewrite (symm b a). *)
(*   rewrite assoc. *)
(*   reflexivity. *)
(* Qed. *)


(* Example short : forall b u t t e r f l y : A, *)