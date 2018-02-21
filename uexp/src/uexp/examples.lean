import .u_semiring

-- set_option trace.simp_lemmas.invalid true
set_option trace.simplify true

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
    forall {s: Schema} (t₁ t₂: Tuple s) (R: Tuple s → usr),
    (R t₁) * (t₁ ≃ t₂)  = (t₁ ≃ t₂) * (R t₂) :=
begin
    intros,
    simp,
end

-- this one breaks something
lemma eq_sigma_subst:
    forall {s: Schema} (R: Tuple s → usr) (t : Tuple s),
    (∑ t₁ ,  (t₁ ≃ t) * (R t₁)) = (R t) := 
begin
    intros,
    simp,
end

