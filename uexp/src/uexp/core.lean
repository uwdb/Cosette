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

-- We need to add these to mark the relation as an equivalence relation for
-- the simplifier.
attribute [refl] uexp.eq.refl
attribute [trans] uexp.eq.trans

infix `≃`:50 := uexp.eq

open uexp
