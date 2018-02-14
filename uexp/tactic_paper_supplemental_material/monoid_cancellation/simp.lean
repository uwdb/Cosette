import .monoid
local infix * := star

attribute [simp] star_comm star_assoc one_star

@[simp] lemma star_left_comm : ∀ a b c, a * (b * c) = b * (a * c) :=
left_comm star star_comm star_assoc

@[simp] lemma star_one (a) : a * o = a := by simp
