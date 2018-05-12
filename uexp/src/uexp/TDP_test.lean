import .TDP
import .cosette_tactics

open list io

example {p q r s} {f : Tuple p → Tuple q → Tuple r → Tuple s → usr}
  : (∑ (a : Tuple p) (b : Tuple q) (c : Tuple r) (d : Tuple s), f a b c d)
  = (∑ (c : Tuple r) (a : Tuple p) (d : Tuple s) (b : Tuple q), f a b c d) :=
begin
  TDP' tactic.ac_refl,
end

example {p} {R S: Tuple p → usr}
  : (∑ (a b: Tuple p), R a * S b * S b)
  = (∑ (a b: Tuple p), R b * S a * S a) :=
begin
  TDP' tactic.ac_refl,
end

example {p} {R: Tuple p → usr} {b t: Tuple p}:
    (∑ (a: Tuple p), (a ≃ t) * R a * R b)
  = R t * R b :=
begin
  normalize_sig_body,
  removal_step,
  ac_refl,
end

example {p q} {R S: Tuple p → usr} {t: Tuple p}
  : (∑ (a b: Tuple p) (c: Tuple q), (a ≃ b) * R a * R b)
  = (∑ (t: Tuple p) (c: Tuple q), R t * R t) :=
begin
  normalize_sig_body,
  removal_step,
  refl,
end

example {r p} {R: Tuple r → usr} :
  (∑ (a1 a2 a3: Tuple r) (b c: Tuple p), (a2 ≃ a1) * (a2 ≃ a3) * (c ≃ b) * (R a1)) = 
  (∑ (a: Tuple r)(b: Tuple p),  R a) := 
begin
  remove_dup_sigs,
  refl,
end 

example {p} {R: Tuple p → usr} {b t: Tuple p}:
    R t * R b = (∑ (a: Tuple p), (a ≃ t) * R a * R b) :=
begin
  apply ueq_symm,
  remove_dup_sigs,
  ac_refl,
end

example {r p} {R: Tuple r → usr} {k: Tuple (r++r)}:
  (∑ (a1 a2 a3: Tuple r) (b c: Tuple p), (k ≃ (pair a3 a2)) * (c ≃ b) * (R a1)) = 
  (∑ (a: Tuple r)(b: Tuple p),  R a) := 
begin
  remove_dup_sigs,
  ac_refl
end 

example {r} {R: Tuple r → usr}:
(∑ (a1), (∑ (a2: Tuple r), (a2 ≃ a1) * R a2 ) * R a1) = 
(∑ (t: Tuple r), R t * R t) :=
begin 
  TDP
end
