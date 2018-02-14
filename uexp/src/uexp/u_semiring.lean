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
    (t₁ ≃ t₂) * (R t₁) = (t₁ ≃ t₂) * (R t₂) :=
begin
    intros,
    simp,
end

lemma eq_sigma_subst:
    forall (R: tuple → usr) (t₂ t : tuple),
    sig (λ t₁ : tuple,  (t₁ ≃ t₂) * (R t₁)) = (R t) := sorry
