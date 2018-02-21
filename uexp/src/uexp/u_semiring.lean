-- definition of u-semiring
constant datatype: Type
inductive tree (A:Type)
| node : tree → tree → tree
| leaf : A → tree
| empty {} : tree

definition Schema := tree datatype
constant denote : datatype → Type
constant tuple : Type

def Tuple : Schema → Type
| (tree.node t0 t1) := (Tuple t0) × (Tuple t1)
| (tree.leaf A) := denote A
| tree.empty := unit

inductive usr : Type
| plus : usr → usr → usr
| time : usr → usr → usr
| zero : usr
| one : usr
| sig {s: Schema}: (Tuple s → usr) → usr
| squash : usr → usr
| not : usr → usr
| ueq {s : Schema} : Tuple s → Tuple s → usr

local infix * := usr.time
local infix + := usr.plus
notation `∑` := usr.sig
notation `∥` u `∥` := usr.squash u 
notation 0 := usr.zero
notation 1 := usr.one

infix `≃`:50 := usr.ueq

-- commutative semiring axioms
@[simp] axiom plus_comm (a b : usr) :       a + b = b + a
@[simp] axiom plus_zero (a : usr) :         a + 0 = a
@[simp] axiom plus_assoc (a b c : usr) :    a + b + c = a + (b + c)
@[simp] axiom time_comm (a b : usr) :       a * b = b * a
@[simp] axiom time_assoc_l (a b c : usr) :  a * (b + c) = a * b + a * c
@[simp] axiom time_assoc_r (a b c : usr) :  (a + b) * c = a * c + b * c
@[simp] axiom time_zero (a : usr): a * 0 = 0
@[simp] axiom time_one (a : usr): a * 1 = a

-- u-semiring axioms
@[simp] axiom sig_distr {s: Schema} (f₁ f₂ : Tuple s → usr):
    ∑ (λ t: Tuple s, (f₁ t) + (f₂ t)) = ∑ (λ t: Tuple s, (f₁ t)) + ∑ (λ t: Tuple s, (f₂ t))
@[simp] axiom sig_commute {s t: Schema} (f: Tuple s → Tuple t → usr):
    ∑ (λ t₁ : Tuple s, ∑ (λ t₂ : Tuple t, f t₁ t₂)) =
    ∑ (λ t₂ : Tuple t, ∑ (λ t₁ : Tuple s, f t₁ t₂))
@[simp] axiom sig_assoc {s: Schema} (a: usr) (f: Tuple s → usr):
    ∑ (λ t : Tuple s, a * (f t)) =
    a * ∑ (λ t: Tuple s, f t)

@[simp] axiom squash_zero : usr.squash 0 = 0
@[simp] axiom squash_one : usr.squash 1 = 1
@[simp] axiom squash_add_squash (x y : usr) :  ∥ ∥ x ∥ + y ∥ = ∥ x + y ∥ 
@[simp] axiom squash_time (x y : usr) : ∥ x * y ∥  = ∥ x ∥ * ∥ y ∥ 
@[simp] axiom squash_squared (x : usr) : ∥ x ∥ * ∥ x ∥  = ∥ x ∥ 
@[simp] axiom squash_eq_if_square_eq (x : usr) : x * x = x → ∥ x ∥ = x

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
@[simp] axiom sig_eq {s: Schema} (t₁ : Tuple s) : ∑ (λ t₂, t₁ ≃ t₂) = 1
@[simp] axiom eq_unique {s: Schema} (t' : Tuple s):
    ∑ (λ t: Tuple s, (t ≃ t')) = 1
