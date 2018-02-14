inductive uexp : Type
| zero : uexp
| one : uexp
| plus : uexp → uexp → uexp
| mul : uexp → uexp → uexp
| squash : uexp → uexp
| not : uexp → uexp
| var {} : string → uexp
-- I don't fully understand the "typing" of sigma
-- | sigma : (v → uexp) → uexp
| equals : uexp → uexp → uexp
| project : uexp → string → uexp
| rel : string → string → uexp
| le : uexp → uexp → uexp
| int : int → uexp

instance uexp.has_zero : has_zero uexp :=
⟨ uexp.zero ⟩

instance uexp.has_one : has_one uexp:=
⟨ uexp.one ⟩

instance uexp.has_add : has_add uexp :=
⟨ uexp.plus ⟩

instance uexp.has_mul : has_mul uexp :=
⟨ uexp.mul ⟩

instance uexp.var_coe : has_coe string uexp :=
⟨ uexp.var ⟩

infix `=>`:61 := uexp.project
infix `~=`:60 := uexp.equals

inductive uexp.eq : uexp → uexp → Prop.

-- | refl : forall u1, uexp.eq u1 u1
-- -- -- rule 19
-- -- | sigma_hoist :
-- --     forall E (f : string → uexp),
-- --         uexp.eq (E * (@uexp.sigma v f)) (uexp.sigma (fun t', E * (f t')))
-- -- rule 16
-- | add_comm : forall (E1 E2 : uexp),
--   uexp.eq (uexp.plus E1 E2) (uexp.plus E2 E1)
-- | add_func : forall (E1 E2 E3: uexp),
--   uexp.eq E2 E3 → uexp.eq (E1 + E2)
--    (E1 + E3)
-- | mul_assoc : forall (E1 E2 E3 : uexp),
--   uexp.eq (E1 * (E2 * E3)) (E1 * E2 * E3)
-- | mul_comm : forall (E1 E2 : uexp),
--   uexp.eq (E1 * E2) (E2 * E1)
-- | mul_distr : forall (E1 E2 E3: uexp),
--   uexp.eq ((E1 + E2) * E3) (E1 * E3 + E2 * E3)
-- -- | sigma_inj :
-- --     forall (f g : string → uexp),
-- --         (forall (x : string), uexp.eq (f x) (g x)) →
-- --         uexp.eq (uexp.sigma f) (uexp.sigma g)
-- | trans : forall (e1 e2 e3 : uexp),
--     uexp.eq e1 e2 →
--     uexp.eq e2 e3 →
--     uexp.eq e1 e3

-- We need to add these to mark the relation as an equivalence relation for
-- the simplifier.


infix `≃`:50 := uexp.eq

@[refl] lemma uexp_eq_refl :
  forall (e1 : uexp), e1 ≃ e1 :=
begin
  admit
end

@[trans] lemma uexp_eq_trans :
  forall (e1 e2 e3 : uexp),
    e1 ≃ e2 →
    e2 ≃ e3 →
    e1 ≃ e3 :=
begin
  admit
end

open uexp
