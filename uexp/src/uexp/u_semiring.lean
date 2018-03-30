-- definition of u-semiring
class denotation (A: Type) (B:Type) := 
  (denote : A → B)

--def denote {A B: Type} [denotation A B] : A → B := @denotation.denote 

constant datatype: Type
inductive tree (A:Type)
| node : tree → tree → tree
| leaf : A → tree
| empty {} : tree

definition Schema := tree datatype
constant denote : datatype → Type 

def Tuple : Schema → Type
| (tree.node t0 t1) := (Tuple t0) × (Tuple t1)
| (tree.leaf A) := denote A
| tree.empty := unit

constant usr : Type
constant usr.one : usr
constant usr.zero : usr
constant usr.plus : usr → usr → usr
constant usr.time : usr → usr → usr
constant usr.sig {s: Schema}: (Tuple s → usr) → usr
constant usr.squash : usr → usr
constant usr.not : usr → usr
constant usr.ueq {s : Schema} : Tuple s → Tuple s → usr

notation `∑` binders `, ` r:(scoped p, usr.sig p) := r
notation `∥` u `∥` := usr.squash u 
noncomputable instance : has_append Schema := ⟨tree.node⟩

infix `≃`:50 := usr.ueq
noncomputable instance usr_has_add : has_add usr := ⟨usr.plus⟩
noncomputable instance usr_has_mul : has_mul usr := ⟨usr.time⟩
noncomputable instance usr_has_zero : has_zero usr := ⟨usr.zero⟩
noncomputable instance usr_has_one : has_one usr := ⟨usr.one⟩

-- commutative semiring axioms
@[simp] axiom plus_comm (a b : usr) :       a + b = b + a
@[simp] axiom plus_zero (a : usr) :         a + 0 = a
@[simp] axiom plus_assoc (a b c : usr) :    a + b + c = a + (b + c)
@[simp] axiom time_comm (a b : usr) :       a * b = b * a
@[simp] axiom time_assoc (a b c : usr) : a * b * c = a * (b * c)
@[simp] axiom time_distrib_l (a b c : usr) :  a * (b + c) = a * b + a * c
@[simp] axiom time_distrib_r (a b c : usr) :  (a + b) * c = a * c + b * c
@[simp] axiom time_zero (a : usr): a * 0 = 0
@[simp] axiom time_one (a : usr): a * 1 = a

noncomputable instance : comm_semiring usr := {
    add_assoc := plus_assoc,
    add_zero := plus_zero,
    zero_add := by intros; rw plus_comm; simp,
    add_comm := plus_comm,
    mul_assoc := time_assoc,
    mul_one := time_one,
    one_mul := by intros; rw time_comm; simp,
    left_distrib := time_distrib_l,
    right_distrib := time_distrib_r,
    mul_zero := time_zero,
    zero_mul := by intros; rw time_comm; simp,
    mul_comm := time_comm,
    ..usr_has_add,
    ..usr_has_mul,
    ..usr_has_zero,
    ..usr_has_one
}

@[simp] axiom sig_distr_plus {s : Schema} (f₁ f₂ : Tuple s → usr) :
    (∑ t, f₁ t + f₂ t) = (∑ t, f₁ t) + (∑ t, f₂ t)
-- adding the sig_commute to the set of simplification lemma 
-- will make it run forever
axiom sig_commute {s t: Schema} (f: Tuple s → Tuple t → usr):
    (∑ t₁ t₂, f t₁ t₂) = (∑ t₂ t₁, f t₁ t₂)
@[simp] axiom sig_distr_time {s : Schema} (a: usr) (f: Tuple s → usr):
    a * (∑ t, f t) = (∑ t, a * (f t)) 
@[simp] axiom sig_pair_split {s₁ s₂: Schema} (f: Tuple (s₁ ++ s₂) → usr):
    (∑ t, (f t)) = (∑ t₁ t₂, (f (t₁, t₂)))

@[simp] axiom squash_zero : usr.squash 0 = 0
@[simp] axiom squash_one : usr.squash 1 = 1
@[simp] axiom squash_add_squash (x y : usr) :  ∥ ∥ x ∥ + y ∥ = ∥ x + y ∥ 
@[simp] axiom squash_time (x y : usr) : ∥ x ∥ * ∥ y ∥ = ∥ x * y ∥ 
@[simp] axiom squash_squared (x : usr) : ∥ x ∥ * ∥ x ∥  = ∥ x ∥ 
@[simp] axiom squash_eq_if_square_eq (x : usr) : x * x = x → ∥ x ∥ = x
@[simp] lemma squash_idempotent (x: usr): ∥ ∥ x ∥ ∥ = ∥ x ∥ :=
begin
    rewrite <- (@plus_zero (∥ x ∥)),
    rewrite squash_add_squash,
    rewrite plus_zero,
    rewrite plus_zero,
end

@[simp] lemma squash_time_squash (x y: usr): ∥ ∥ x ∥ * y ∥ = ∥ x * y ∥ :=
begin
    rewrite <- squash_time,
    rewrite squash_idempotent,
    rewrite squash_time,
end 

@[simp] axiom not_zero : usr.not 0 = 1
@[simp] axiom not_time (x y : usr) : usr.not (x * y) =  ∥ usr.not x + usr.not y ∥ 
@[simp] axiom not_plus (x y : usr) : usr.not (x + y) = usr.not x * usr.not y
@[simp] axiom not_squash (x : usr) : usr.not ∥ x ∥  = ∥ usr.not x ∥ 
@[simp] axiom squash_not (x : usr) : ∥ usr.not x ∥  = usr.not x

-- axioms about predicates
@[simp] axiom eq_subst_l {s: Schema} (t₁ t₂: Tuple s) (R: Tuple s → usr): (t₁ ≃ t₂) * (R t₁) = (t₁ ≃ t₂) * (R t₂)
@[simp] axiom eq_subst_r {s: Schema} (t₁ t₂: Tuple s) (R: Tuple s → usr): 
(R t₁) *(t₁ ≃ t₂) = (R t₂) * (t₁ ≃ t₂) 
@[simp] axiom em {s: Schema} (t₁ t₂ : Tuple s) : (t₁ ≃ t₂) + usr.not (t₁ ≃ t₂) = 1
@[simp] axiom eq_unique {s: Schema} (t' : Tuple s) : (∑ t, t ≃ t') = 1
@[simp] axiom eq_symm {s: Schema} (t₁ t₂ : Tuple s):
    (t₁ ≃ t₂) = (t₂ ≃ t₁)
axiom eq_pair {s₁ s₂: Schema} (t₁: Tuple s₁) (t₂: Tuple s₂) (t: Tuple (s₁ ++ s₂)): 
    (t ≃ (t₁, t₂)) = (t₁ ≃ t.1) * (t₂ ≃ t.2)