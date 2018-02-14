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
axiom plus_comm (a b : usr) :       a + b = b + a
axiom plus_zero (a : usr) :         a + zero = a
axiom plus_assoc (a b c : usr) :    a + b + c = a + (b + c)
axiom time_comm (a b c : usr) :     a * b * c =  a * (b * c)
axiom time_assoc_l (a b c : usr) :    a * (b + c) = a * b + a * c 
axiom time_assoc_r (a b c : usr) :    (a + b) * c = a * c + b * c
axiom time_zero (a : usr): a * zero = zero

-- these two lemmas are just to try the new encoding
lemma eq_mixed_congruence :
    forall (t₁ t₂: tuple) (R: tuple → usr),
    (t₁ ≃ t₂) * (R t₁) = (t₁ ≃ t₂) * (R t₂) := sorry 

lemma eq_sigma_subst:
    forall (R: tuple → usr) (t₂ t : tuple),
    sig (λ t₁ : tuple,  (t₁ ≃ t₂) * (R t)) = (R t) := sorry 