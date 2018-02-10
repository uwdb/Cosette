import .core
import .tactics

open uexp

set_option trace.simp_lemmas.invalid true
set_option trace.simplify true

#check uexp.eq.refl

lemma uexp_refl :
    forall (v : Type) (e1 e2 : uexp v),
    e1 ≃ e1 :=
begin
    intros, usimp
end

lemma uexp_add_comm :
    forall (v : Type) (e1 e2 e3 : uexp v),
    (e1 + e2) ≃ (e2 + e1) :=
begin
    intros,
    usimp,
end

lemma lem_jared :
    forall (v : Type) (e1 e2 e3 : uexp v),
    (e1 + e2) * e3 ≃ (e2 * e3) + (e3 * e1)  :=
begin
    intros,
    usimp,
end

lemma eq_predicate_congruence :
    forall (v: Type) (a b c d: uexp v),
    (a~=b) * (b~=c) ≃ (a~=b) * (a~=c) :=
sorry

lemma eq_mixed_congruence :
    forall (v: Type) (a b: uexp v) (r: uexp v -> uexp v),
    (a~=b) * (r a) = (b~=a) * (r b) :=
sorry

-- this requires a new axiom
lemma sum_subst (v: Type) (t₂ : v):
uexp.sigma (λ t₁ : v, (t₁ ~= t₂) * (rel "R" t₁)) ≃
(rel "R" t₂) :=
sorry

lemma email_ex_refl (v : Type) :
uexp.sigma (λ t₁ : v,
  uexp.sigma (λ t₂ : v,
   ((var t₁) ~= (var t₂)) *
        uexp.sigma (λ t₃ : v,
            (t₃=>"k" ~= t₁=>"k") *
            (t₃=>"a" ~= t₁=>"a") *
            (rel "R" t₃)) * (rel "R" t₂) *
            (t₁=>"k" ~= t₂=>"k") *
            (le (t₁=>"a") (uexp.int 12)))) ≃
uexp.sigma (λ t₁ : v,
  uexp.sigma (λ t₂ : v,
   (t₁ ~= t₂) *
        uexp.sigma (λ t₃ : v,
            (t₃=>"k" ~= t₁=>"k") *
            (t₃=>"a" ~= t₁=>"a") *
            (rel "R" t₃)) * (rel "R" t₂) *
            (t₁=>"k" ~= t₂=>"k") *
            (le (t₁=>"a") (uexp.int 12)))) :=
begin
    intros, apply uexp.eq.refl,
end

lemma email_ex_full (v : Type) :
uexp.sigma (λ t₁ : v,
  uexp.sigma (λ t₂ : v,
   (t₁ ~= t₂) *
        uexp.sigma (λ t₃ : v,
            (t₃=>"k" ~= t₁=>"k") *
            (t₃=>"a" ~= t₁=>"a") *
            (rel "R" t₃)) * (rel "R" t₂) *
            (t₁=>"k" ~= t₂=>"k") *
            (le (t₁=>"a") (uexp.int 12)))) ≃
uexp.sigma (λ t₁ : v,
  uexp.sigma (λ t₂ : v,
    uexp.sigma (λ t₃ : v,
        (t₁ ~= t₂) * (t₁=>"k" ~= t₂=>"k") *
        (le (t₁=>"a") (uexp.int 12)) *
        (t₃=>"k" ~= t₁=>"k") *
        (t₃=>"a" ~= t₁=>"a") *
        (rel "R" t₃)) * (rel "R" t₂))) :=
begin
    intros,
    apply uexp.eq.sigma_inj; intros,
    apply uexp.eq.sigma_inj; intros,
    apply uexp.eq.trans; intros,
    apply uexp.eq.sigma_inj,
    tactic.rotate_left 1,
    apply uexp.eq.mul_comm; intros,
end
