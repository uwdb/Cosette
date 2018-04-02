import .smt
local infix * := star
open tactic smt_tactic
attribute [ematch] one_star
meta def qf_monoid := using_smt $ smt_tactic.intros; eblast

section
variables {a b c d : m}

lemma plus_unit_p : a = b → o * a = b := by qf_monoid
lemma plus_assoc_p1 : a * (b * c) = d → (a * b) * c = d := by qf_monoid
lemma plus_assoc_p2 : b * (a * c) = d → (a * b) * c = d := by qf_monoid
lemma plus_comm_p : a * b = c → b * a = c := by qf_monoid

lemma plus_unit_c : a = b → a = o * b := by qf_monoid
lemma plus_assoc_c1 : d = a * (b * c) → (a * b) * c = d := by qf_monoid
lemma plus_assoc_c2 : d = b * (a * c) → (a * b) * c = d := by qf_monoid
lemma plus_comm_c : c = a * b → c = b * a := by qf_monoid

lemma plus_cancel : a = c → b = d → a * b = c * d := by qf_monoid

lemma plus_refl : a = a := by qf_monoid

end

open tactic expr

meta def iter_right :=
applyc `plus_unit_c <|>
applyc `plus_assoc_c1 >> iter_right <|>
applyc `plus_assoc_c2 >> iter_right <|>
applyc `plus_cancel >> reflexivity

meta def iter_left :=
applyc `plus_unit_p <|>
applyc `plus_assoc_p1 >> iter_left <|>
applyc `plus_assoc_p2 >> iter_left <|>
iter_right <|> applyc `plus_comm_p >> iter_right

meta def cancel :=
iter_left <|> applyc `plus_comm_p >> iter_left

meta def solve : tactic unit :=
repeat $ reflexivity <|> cancel

meta def solve_single :=
reflexivity <|> cancel
