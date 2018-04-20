open tactic

meta def arith :=
intros >> `[apply mul_pos] >> comp_val >> `[apply nat.lt_of_succ_lt] >> assumption

constant p : ∀ n, n > 0 → Prop
axiom pax : ∀ n h, p (2*n) h

lemma ex (n : nat) : n > 1 → p (2*n) (by arith) :=
by intros; apply pax
