section cosette_tactics

def list.swap_ith_forward {α : Type} {f : Type → Type} [alternative f]
  : nat → list α → f (list α)
| 0 (x::y::zs) := pure $ y :: x :: zs
| (nat.succ n) (x::xs) := list.cons x <$> list.swap_ith_forward n xs
| _ _ := failure

lemma swap_gives_result_if_index_in_range {α : Type}
  : ∀ (ls : list α) i,
    i + 2 < list.length ls →
    { ls' : list α // list.swap_ith_forward i ls = some ls' } :=
begin
  intros ls i h,
  revert ls,
  induction i with j ih;
  intros; cases ls with x ys,
  { exfalso, cases h },
  { cases ys with y zs,
    { exfalso, cases h, cases h_a },
    { existsi (y :: x :: zs), refl } },
  { exfalso, cases h },
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

def move_nth_to_kth {α : Type} {m : Type → Type} [alternative m] [monad m]
  (initial final : ℕ) (ls : list α) : m (list α) :=
  list.append (ls.take initial) <$>
    nat.repeat (λ n (ls' : m (list α)), ls' >>= list.swap_ith_forward (final - n - 1))
               (final - initial) (return $ ls.drop initial)

universes u v w
def congr_arg₂ {α : Sort u} {β : Sort v} {γ : Sort w}
  {a₁ a₂ : α} {b₁ b₂ : β} (f : α → β → γ)
  : a₁ = a₂ → b₁ = b₂ → f a₁ b₁ = f a₂ b₂ :=
begin
  intros,
  apply congr,
  { apply congr_arg, assumption },
  { assumption }
end

#reduce (move_nth_to_kth 1 3 [1,2,3,4,5] : option (list ℕ))

end cosette_tactics