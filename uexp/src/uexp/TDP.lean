import .u_semiring

meta constant swap_free_vars (i : nat) (j : nat) : expr → tactic expr

section TDP

open tactic

meta structure usr_sigma_repr :=
(var_schemas : list expr) (body : expr)

meta def sigma_expr_to_sigma_repr : expr → usr_sigma_repr
| `(usr.sig (λ t : Tuple %%s, %%a)) :=
  match sigma_expr_to_sigma_repr a with
  | ⟨var_schemas, inner⟩ := ⟨s :: var_schemas, inner⟩
  end
| e := ⟨[], e⟩

meta def sigma_repr_to_sigma_expr : usr_sigma_repr → tactic expr
| ⟨[], body⟩ := return body
| ⟨t::ts, body⟩ := do
  body' ← sigma_repr_to_sigma_expr ⟨ts, body⟩,
  to_expr ``(∑ x : Tuple %%t, %%body')

meta def get_lhs_repr : tactic usr_sigma_repr :=
target >>= λ e,
match e with
| `(%%a = %%b) := return $ sigma_expr_to_sigma_repr a
| _ := failed
end

meta def list.swap_ith_forward {α : Type}
  : Π (i : nat) (ls : list α), /-nat.succ i < ls.length →-/ tactic (list α)
--| 0 [] h := absurd (lt.trans h $ nat.zero_lt_succ 0) $ lt_irrefl 1
--| (nat.succ n) [] h := false.elim $ 
--                       nat.lt_le_antisymm (nat.zero_lt_succ $ nat.succ n) $
--                       nat.le_of_lt h
--| 0 [x] h := absurd h $ lt_irrefl 1
--| (nat.succ n) [x] h := absurd (lt.trans (nat.lt_of_succ_lt_succ h) $ nat.zero_lt_succ _) $ lt_irrefl _
| 0 (x::y::zs) := return $ y :: x :: zs
| (nat.succ n) (x::y::zs) := list.cons x <$> list.swap_ith_forward n (y :: zs)
| _ _ := failed

meta def swap_ith_sigma_forward (i : nat)
  : usr_sigma_repr → tactic unit
| ⟨xs, body⟩ := do
  swapped_schemas ← list.swap_ith_forward i xs,
  swapped_body ← swap_free_vars i (i + 1) body,
  let swapped_repr := usr_sigma_repr.mk swapped_schemas swapped_body,
  normal_expr ← sigma_repr_to_sigma_expr ⟨xs, body⟩,
  swapped_expr ← sigma_repr_to_sigma_expr swapped_repr,
  equality_lemma ← to_expr ``(%%normal_expr = %%swapped_expr),
  eq_lemma_name ← mk_fresh_name,
  tactic.assert eq_lemma_name equality_lemma,
  return ()

/-meta def move_to_front (i : nat) : tactic unit :=
  let loop : ℕ → tactic unit → tactic unit :=
      λ iter_num next_iter, do
        repr ← get_lhs_repr,
        swap_ith_sigma_forward iter_num repr,
        next_iter
  in nat.repeat loop i (return ())-/

meta def TDP : tactic unit := do
  failed

end TDP

example {p q r} {f : Tuple p → Tuple q → Tuple r → usr} : (∑ (a : Tuple p) (b : Tuple q) (c : Tuple r), f a b c) = usr.one :=
begin
  get_lhs_repr >>= swap_ith_sigma_forward 1,
  funext,
  funext,

end