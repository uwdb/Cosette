-- definition of u-semiring
constant usr : Type
constant type: Type
inductive tree (A:Type)
| node : tree → tree → tree
| leaf : A → tree
| empty {} : tree

definition Schema := tree type
constant denote : type → Type
constant tuple : Type

def Tuple : Schema → Type
| (tree.node t0 t1) := (Tuple t0) × (Tuple t1)
| (tree.leaf A) := denote A
| tree.empty := unit

constant plus : usr → usr → usr
constant time : usr → usr → usr
constant zero : usr
constant one : usr

constant sig {s: Schema}: (Tuple s → usr) → usr -- is that right?
constant squash : usr → usr
constant usr.not : usr → usr
constant ueq {s : Schema} : Tuple s → Tuple s → usr

local infix * := time
local infix + := plus

infix `≃`:50 := ueq

-- commutative semiring axioms
@[simp] axiom plus_comm (a b : usr) :       a + b = b + a
@[simp] axiom plus_zero (a : usr) :         a + zero = a
@[simp] axiom plus_assoc (a b c : usr) :    a + b + c = a + (b + c)
@[simp] axiom time_comm (a b : usr) :       a * b = b * a
@[simp] axiom time_assoc_l (a b c : usr) :  a * (b + c) = a * b + a * c
@[simp] axiom time_assoc_r (a b c : usr) :  (a + b) * c = a * c + b * c
@[simp] axiom time_zero (a : usr): a * zero = zero
@[simp] axiom time_one (a : usr): a * one = a

-- u-semiring axioms
@[simp] axiom sig_distr {s: Schema} (f₁ f₂ : Tuple s → usr):
    sig (λ t: Tuple s, (f₁ t) + (f₂ t)) = sig (λ t: Tuple s, (f₁ t)) + sig (λ t: Tuple s, (f₂ t))
@[simp] axiom sig_commute {s t: Schema} (f: Tuple s → Tuple t → usr):
    sig (λ t₁ : Tuple s, sig (λ t₂ : Tuple t, f t₁ t₂)) =
    sig (λ t₂ : Tuple t, sig (λ t₁ : Tuple s, f t₁ t₂))
@[simp] axiom sig_assoc {s: Schema} (a: usr) (f: Tuple s → usr):
    sig (λ t : Tuple s, a * (f t)) =
    a * sig (λ t: Tuple s, f t)

@[simp] axiom squash_zero : squash zero = zero
@[simp] axiom squash_one : squash one = one
@[simp] axiom squash_add_squash (x y : usr) : squash (squash x + y) = squash (x + y)
@[simp] axiom squash_time (x y : usr) : squash (x * y) = squash x * squash y
@[simp] axiom squash_squared (x : usr) : squash x * squash x = squash x
@[simp] axiom squash_eq_if_square_eq (x : usr) : x * x = x → squash x = x

@[simp] axiom not_zero : usr.not zero = one
@[simp] axiom not_time (x y : usr) : usr.not (x * y) = squash (usr.not x + usr.not y)
@[simp] axiom not_plus (x y : usr) : usr.not (x + y) = usr.not x * usr.not y
@[simp] axiom not_squash (x : usr) : usr.not (squash x) = squash (usr.not x)
@[simp] axiom squash_not (x : usr) : squash (usr.not x) = usr.not x

-- axioms about predicates
@[simp] axiom eq_subst_l {s: Schema} (t₁ t₂: Tuple s) (R: Tuple s → usr): (t₁ ≃ t₂) * (R t₁) = (t₁ ≃ t₂) * (R t₂)
@[simp] axiom eq_subst_r {s: Schema} (t₁ t₂: Tuple s) (R: Tuple s → usr): 
(R t₁) *(t₁ ≃ t₂) = (R t₂) * (t₁ ≃ t₂) 
@[simp] axiom em {s: Schema} (t₁ t₂ : Tuple s) : (t₁ ≃ t₂) + usr.not (t₁ ≃ t₂) = one
@[simp] axiom sig_eq {s: Schema} (t₁ : Tuple s) : sig (λ t₂, t₁ ≃ t₂) = one
@[simp] axiom eq_unique {s: Schema} (t' : Tuple s):
    sig (λ t: Tuple s, (t ≃ t')) = one
