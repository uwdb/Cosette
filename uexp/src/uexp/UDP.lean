import .u_semiring
import .cosette_tactics
import .ucongr
import .TDP
section UDP

open tactic

meta structure usr_add_repr :=
(summands : list expr)

-- Given a + (b + c), produce [a, b, c]
meta def add_expr_to_add_repr : expr → usr_add_repr
| `(%%a + %%b) :=
  match add_expr_to_add_repr b with
  | ⟨es⟩ := ⟨a :: es⟩
  end
| e := ⟨[e]⟩

meta def add_repr_to_add_expr : usr_add_repr → tactic expr
| ⟨xs⟩ := match xs.reverse with
          | (a::as) := list.mfoldr (λ (x sum : expr), to_expr ``(%%x + %%sum)) a as.reverse
          | [] := fail "Tried to turn an empty list into a sum"
          end

meta def get_lhs_add_repr : tactic usr_add_repr :=
target >>= λ e,
match e with
| `(%%a = %%b) := return $ add_expr_to_add_repr a
| _ := fail "Not an equality"
end

meta def swap_ith_summand_forward (i : nat)
  : usr_add_repr → tactic unit
| ⟨es⟩ := do
  swapped_repr ← usr_add_repr.mk <$> list.swap_ith_forward i es,
  normal_expr ← add_repr_to_add_expr ⟨es⟩,
  swapped_expr ← add_repr_to_add_expr swapped_repr,
  equality_lemma ← to_expr ``(%%normal_expr = %%swapped_expr),
  eq_lemma_name ← mk_fresh_name,
  tactic.assert eq_lemma_name equality_lemma,
  ac_refl,
  eq_lemma ← resolve_name eq_lemma_name >>= to_expr,
  rewrite_target eq_lemma,
  clear eq_lemma

meta def move_add_to_front (i : nat) : tactic unit :=
  let loop : ℕ → tactic unit → tactic unit :=
      λ iter_num next_iter, do
        repr ← get_lhs_add_repr,
        swap_ith_summand_forward iter_num repr,
        next_iter
  in nat.repeat loop i $ return ()

meta def UDP : tactic unit :=
  let loop (iter_num : ℕ) (next_iter : tactic unit) : tactic unit :=
      next_iter <|> do
      move_add_to_front iter_num,
      applyc `congr_arg₂,
      TDP,
      UDP
  in do
    num_summands ← list.length <$> usr_add_repr.summands <$> get_lhs_add_repr,
    nat.repeat loop num_summands TDP

end UDP

example {p q r s} {f g : Tuple p → Tuple q → Tuple r → Tuple s → usr}
  : (∑ (a : Tuple p) (b : Tuple q) (c : Tuple r) (d : Tuple s), f a b c d)
  + ((∑ (a : Tuple p) (b : Tuple q) (c : Tuple r) (d : Tuple s), g a b c d) + 1)
  = 1 + ((∑ (c : Tuple r) (a : Tuple p) (d : Tuple s) (b : Tuple q), g a b c d)
  + (∑ (c : Tuple r) (a : Tuple p) (d : Tuple s) (b : Tuple q), f a b c d)) :=
begin
  UDP,
end