import .u_semiring
import .tactics

-- set_option trace.simp_lemmas.invalid true
-- set_option trace.simplify true

local infix * := time
local infix + := plus

infix `≃`:50 := ueq

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

