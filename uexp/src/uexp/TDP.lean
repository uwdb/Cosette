import .u_semiring

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

meta def get_lhs_repr : tactic usr_sigma_repr :=
target >>= λ e,
match e with
| `(%%a = %%b) := return $ sigma_expr_to_sigma_repr a
| _ := failed
end

def list.swap_ith_forward {α : Type} {f : Type → Type} [alternative f]
  : nat → list α → f (list α)
| 0 (x::y::zs) := pure $ y :: x :: zs
| (nat.succ n) (x::xs) := list.cons x <$> list.swap_ith_forward n xs
| _ _ := failure

lemma swap_gives_result_if_index_in_range {α : Type}
  : ∀ (ls : list α) i,
    i + 2 < list.length ls →
    ∃ ls', list.swap_ith_forward i ls = some ls' :=
begin
  intros ls i h,
  revert ls,
  induction i with j ih;
  intros; cases ls with x ys,
  { cases h },
  { cases ys with y zs, cases h, cases h_a,
    existsi (y :: x :: zs), refl },
  { cases h },
  { cases ih ys _ with ys' h',
    existsi x :: ys', unfold list.swap_ith_forward,
    rw h', refl,
    apply nat.lt_of_succ_lt_succ,
    assumption }
end

meta def expr.swap_free_vars (i : nat) (j : nat) : expr → expr
| (expr.var n) := if n = i
                    then expr.var j
                    else if n = j
                           then expr.var i
                           else expr.var n
| (expr.app f x) := expr.app (expr.swap_free_vars f) (expr.swap_free_vars x)
| (expr.lam n bi ty body) := let ty' := expr.swap_free_vars ty,
                                 body' := expr.swap_free_vars body
                             in expr.lam n bi ty' body'
| (expr.pi n bi ty body) := let ty' := expr.swap_free_vars ty,
                                body' := expr.swap_free_vars body
                            in expr.pi n bi ty' body'
| (expr.elet n ty val body) := let ty' := expr.swap_free_vars ty,
                                   val' := expr.swap_free_vars val,
                                   body' := expr.swap_free_vars body
                               in expr.elet n ty' val' body'
| ex := ex

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
        get_lhs_repr >>=
        swap_ith_sigma_forward iter_num >>
        next_iter
  in nat.repeat loop i $ return ()

meta def TDP : tactic unit := 
  let loop : ℕ → tactic unit → tactic unit :=
      λ iter_num next_iter, do
        ⟨schemas, body⟩ ← get_lhs_repr,
        sorry
  in sorry
end TDP

example {p q r} {f : Tuple p → Tuple q → Tuple r → usr}
  : (∑ (a : Tuple p) (b : Tuple q) (c : Tuple r), f a b c)
  = (∑ (c : Tuple r) (a : Tuple p) (b : Tuple q), f a b c) :=
begin
  move_to_front 2,
  refl
end