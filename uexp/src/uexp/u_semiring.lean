-- definition of u-semiring
constant usr : Type
constant tuple : Type
constant plus : usr → usr → usr
constant time : usr → usr → usr
constant zero : usr
constant one : usr
constant sig : (tuple → usr) → usr -- is that right?
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

-- u-semiring axioms (TODO: squash and not)
@[simp] axiom sig_distr (f₁ f₂ : tuple → usr):
    sig (λ t: tuple, (f₁ t) + (f₂ t)) = sig (λ t: tuple, (f₁ t)) + sig (λ t: tuple, (f₂ t))
@[simp] axiom sig_commute (f: tuple → tuple → usr):
    sig (λ t₁ : tuple, sig (λ t₂ : tuple, f t₁ t₂)) =
    sig (λ t₂ : tuple, sig (λ t₁ : tuple, f t₁ t₂))
@[simp] axiom sig_assoc (a: usr) (f: tuple → usr):
    sig (λ t : tuple, a * (f t)) =
    a * sig (λ t: tuple, f t)

-- axioms about predicates
@[simp] axiom eq_subst_l (t₁ t₂: tuple) (R: tuple → usr): (t₁ ≃ t₂) * (R t₁) = (t₁ ≃ t₂) * (R t₂)
@[simp] axiom eq_subst_r (t₁ t₂: tuple) (R: tuple → usr): 
(R t₁) *(t₁ ≃ t₂) = (R t₂) * (t₁ ≃ t₂) 
@[simp] axiom eq_unique (t' : tuple):
    sig (λ t: tuple, (t ≃ t')) = one

-- these two lemmas are just to try the new encoding

-- this one works, hoory!
lemma lem_jared :
    forall (v : Type) (e1 e2 e3 : usr),
    (e1 + e2) * e3 = (e2 * e3) + (e3 * e1)  :=
begin
    intros,
    simp,
end

lemma eq_mixed_congruence :
    forall (t₁ t₂: tuple) (R: tuple → usr),
    (R t₁) * (t₁ ≃ t₂)  = (t₁ ≃ t₂) * (R t₂) :=
begin
    intros,
    simp,
end

-- this one breaks something
lemma eq_sigma_subst:
    forall (R: tuple → usr) (t : tuple),
    sig (λ t₁ : tuple,  (t₁ ≃ t) * (R t₁)) = (R t) := 
begin
    intros,
    simp,
end
