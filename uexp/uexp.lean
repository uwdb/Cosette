inductive uexp (v : Type)
| zero : uexp
| one : uexp
| plus {} : uexp → uexp → uexp
| mul {} : uexp → uexp → uexp
| squash : uexp → uexp
| not : uexp → uexp
| var {} : v → uexp
-- I don't fully understand the "typing" of sigma
| sigma : (v → uexp) → uexp
| equals : uexp → uexp → uexp
| project : uexp → string → uexp
| rel {} : string → v → uexp
| le : uexp → uexp → uexp
| int {} : int → uexp

instance uexp.has_zero (v : Type) : has_zero (uexp v) :=
⟨ @uexp.zero v ⟩

instance uexp.has_one (v : Type) : has_one (uexp v) :=
⟨ @uexp.one v ⟩

instance uexp.has_add (v : Type) : has_add (uexp v) :=
⟨ uexp.plus ⟩

instance uexp.has_mul (v : Type) : has_mul (uexp v) :=
⟨ uexp.mul ⟩

instance uexp.var_coe (v : Type) : has_coe v (uexp v) :=
⟨ uexp.var ⟩

infix `=>`:61 := uexp.project
infix `~=`:60 := uexp.equals

inductive uexp.eq {v : Type} : uexp v → uexp v → Prop
| refl : forall u1, uexp.eq u1 u1
-- rule 19
| sigma_hoist :
    forall E (f : v → uexp v),
        uexp.eq (E * (@uexp.sigma v f)) (uexp.sigma (fun t', E * (f t')))
-- rule 16
| add_comm : forall (E1 E2 : uexp v),
  uexp.eq (E1 + E2) (E2 + E1)
| add_func : forall (E1 E2 E3: uexp v),
  uexp.eq E2 E3 → uexp.eq (E1 + E2)
   (E1 + E3)
| mul_assoc : forall (E1 E2 E3 : uexp v),
  uexp.eq (E1 * (E2 * E3)) (E1 * E2 * E3)
| mul_comm : forall (E1 E2 : uexp v),
  uexp.eq (E1 * E2) (E2 * E1)
| mul_distr : forall (E1 E2 E3: uexp v),
  uexp.eq ((E1 + E2) * E3) (E1 * E3 + E2 * E3) 
| sigma_inj :
    forall (f g : v → uexp v),
        (forall (x : v), uexp.eq (f x) (g x)) →
        uexp.eq (uexp.sigma f) (uexp.sigma g)
| trans : forall (e1 e2 e3 : uexp v),
    uexp.eq e1 e2 →
    uexp.eq e2 e3 →
    uexp.eq e1 e3

infix `≃`:50 := uexp.eq

open uexp

lemma lem_jared :
    forall (v : Type) (e1 e2 e3 : uexp v),
    (e1 + e2) * e3 ≃ (e2 * e3) + (e3 * e1)  :=
begin
    intros,
    apply uexp.eq.trans,
    apply uexp.eq.mul_distr,
    apply uexp.eq.trans,
    apply uexp.eq.add_comm,
    apply uexp.eq.trans,
    apply uexp.eq.add_func,
    apply uexp.eq.mul_comm,
    apply uexp.eq.refl
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

