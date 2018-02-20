-- definition of u-semiring
constant usr : Type
constant type: Type
inductive tree (A:Type)
| node : tree → tree → tree
| leaf : A → tree
| empty : tree
definition Schema := tree type
constant denote : type → Type
constant tuple : Type
def Tuple (s: Schema) : Type :=
match s with
    | (node t0 t1) := (Tuple t0) × (Tuple t1)
    | (leaf A) := denote A
    | empty := unit
end

constant plus : usr → usr → usr
constant time : usr → usr → usr
constant zero : usr
constant one : usr

constant sig : (tuple → usr) → usr -- is that right?
constant squash : usr → usr
constant usr.not : usr → usr
constant ueq : tuple → tuple → usr

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
@[simp] axiom sig_distr (f₁ f₂ : tuple → usr):
    sig (λ t: tuple, (f₁ t) + (f₂ t)) = sig (λ t: tuple, (f₁ t)) + sig (λ t: tuple, (f₂ t))
@[simp] axiom sig_commute (f: tuple → tuple → usr):
    sig (λ t₁ : tuple, sig (λ t₂ : tuple, f t₁ t₂)) =
    sig (λ t₂ : tuple, sig (λ t₁ : tuple, f t₁ t₂))
@[simp] axiom sig_assoc (a: usr) (f: tuple → usr):
    sig (λ t : tuple, a * (f t)) =
    a * sig (λ t: tuple, f t)

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
@[simp] axiom eq_subst_l (t₁ t₂: tuple) (R: tuple → usr): (t₁ ≃ t₂) * (R t₁) = (t₁ ≃ t₂) * (R t₂)
@[simp] axiom eq_subst_r (t₁ t₂: tuple) (R: tuple → usr): 
(R t₁) *(t₁ ≃ t₂) = (R t₂) * (t₁ ≃ t₂) 
@[simp] axiom em (t₁ t₂ : tuple) : (t₁ ≃ t₂) + usr.not (t₁ ≃ t₂) = one
@[simp] axiom sig_eq (t₁ : tuple) : sig (λ t₂, t₁ ≃ t₂) = one
@[simp] axiom eq_unique (t' : tuple):
    sig (λ t: tuple, (t ≃ t')) = one
