import .u_semiring

open tactic

-- set_option trace.simplify true

lemma congr_ex1 {s: Schema} (a b c d: Tuple s):
    (d ≃ c) * (d ≃ d) * (d ≃ a) * (d ≃ b) = (a ≃ b) * (b ≃ c) * (c ≃ d) :=
begin
    simp,
    sorry
end

meta def ueq_solve :=
    ac_refl

meta def ueq_congr :=
    applyc `eq_unit >> ueq_solve
