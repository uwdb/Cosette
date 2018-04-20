inductive vect (α : Type) : ℕ → Type
| nil : vect 0
| cons : ∀ {n}, α → vect n → vect (n+1)

instance dec_eq_vect {α n} [decidable_eq α] : decidable_eq (vect α n) :=
by tactic.mk_dec_eq_instance

-- The runtime for the following definition will not show up when run with `--profile`,
-- it is not shown if takes less than 10 milliseconds.
def dec_eq_bool' : decidable_eq bool := by tactic.mk_dec_eq_instance

def dec_eq_list' (α) [decidable_eq α] : decidable_eq (list α) := by tactic.mk_dec_eq_instance
