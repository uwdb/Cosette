import .u_semiring
import .cosette_tactics
import .ucongr
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

-- This needs to be a tactic so we can resolve `Tuple and `usr.sig
meta def sigma_repr_to_sigma_expr : usr_sigma_repr → tactic expr
| ⟨[], body⟩ := return body
| ⟨t::ts, body⟩ := do
  body' ← sigma_repr_to_sigma_expr ⟨ts, body⟩,
  to_expr ``(∑ x : Tuple %%t, %%body')

meta def get_lhs_sigma_repr : tactic usr_sigma_repr :=
target >>= λ e,
match e with
| `(%%a = %%b) := return $ sigma_expr_to_sigma_repr a
| _ := failed
end

meta def swap_ith_sigma_forward (i : nat)
  : usr_sigma_repr → tactic unit
| ⟨xs, body⟩ := do
  swapped_schemas ← list.swap_ith_forward i xs,
  -- We have to subtract because the de Bruijn indices are inside-out
  let num_free_vars := list.length xs,
  let swapped_body := expr.swap_free_vars (num_free_vars - 1 - i) (num_free_vars - 1 - nat.succ i) body,
  let swapped_repr := usr_sigma_repr.mk swapped_schemas swapped_body,
  normal_expr ← sigma_repr_to_sigma_expr ⟨xs, body⟩,
  swapped_expr ← sigma_repr_to_sigma_expr swapped_repr,
  equality_lemma ← to_expr ``(%%normal_expr = %%swapped_expr),
  eq_lemma_name ← mk_fresh_name,
  tactic.assert eq_lemma_name equality_lemma,
  repeat $ applyc `congr_arg >> funext,
  try $ applyc `sig_commute,
  eq_lemma ← resolve_name eq_lemma_name >>= to_expr,
  rewrite_target eq_lemma,
  clear eq_lemma

meta def move_to_front (i : nat) : tactic unit :=
  let loop : ℕ → tactic unit → tactic unit :=
      λ iter_num next_iter,
        get_lhs_sigma_repr >>=
        swap_ith_sigma_forward iter_num >>

        next_iter
  in nat.repeat loop i $ return ()

meta def TDP' (easy_case_solver : tactic unit) : tactic unit :=
  let loop (iter_num : ℕ) (next_iter : tactic unit) : tactic unit :=
      next_iter <|> do
      move_to_front iter_num,
      to_expr ``(congr_arg usr.sig) >>= apply,
      funext,
      easy_case_solver <|> TDP'
  in do
    num_vars ← list.length <$> usr_sigma_repr.var_schemas <$> get_lhs_sigma_repr,
    nat.repeat loop num_vars easy_case_solver

meta def TDP := TDP' reflexivity

end TDP

example {p q r s} {f : Tuple p → Tuple q → Tuple r → Tuple s → usr}
  : (∑ (a : Tuple p) (b : Tuple q) (c : Tuple r) (d : Tuple s), f a b c d)
  = (∑ (c : Tuple r) (a : Tuple p) (d : Tuple s) (b : Tuple q), f a b c d) :=
begin
  TDP' tactic.ac_refl,
end