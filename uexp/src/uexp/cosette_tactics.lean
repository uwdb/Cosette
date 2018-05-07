import system.io
open nat io
open list io

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

meta def expr.subst_var (target: expr) : expr → expr := λ e, 
if e = target then (expr.var 0)
else 
match e with
| (expr.var n) := expr.var (n+1)
| (expr.app f x) := expr.app (expr.subst_var f) (expr.subst_var x)
| (expr.lam n bi ty body) := expr.lam n bi (expr.subst_var ty) (expr.subst_var body)
| (expr.pi n bi ty body) := expr.pi n bi (expr.subst_var ty) (expr.subst_var body)
| (expr.elet n ty val body) := let ty' := expr.subst_var ty,
                                   val' := expr.subst_var val,
                                   body' := expr.subst_var body
                               in expr.elet n ty' val' body'
| ex := ex
end

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

-- repeat tacitic t exactly n times
meta def repeat_n (n: nat) (t: tactic unit) : tactic unit :=
    nat.repeat (λ n next, t >> next) n $ return ()

-- check if an expr is in the list
meta def expr_in : expr →  list expr → bool :=
(λ e l, 
match l with
| [] := ff
| (h :: t) := if h=e then tt else (expr_in e t)
end)

-- get lhs expr if the goal is a = b
meta def get_lhs : tactic expr :=
tactic.target >>= λ e,
match e with
| `(%%a = _) := return a
| _ := tactic.failed
end

meta def solved_or_continue (next: tactic unit) : tactic unit := do
    tactic.try tactic.reflexivity,
    ok ← list.empty <$> tactic.get_goals,
    if ok then return ()
    else next

meta def print_goals : tactic unit :=  do 
    goals ← tactic.get_goals,
    tactic.trace goals

meta def repeat_or_sol (f: ℕ → tactic unit) : 
ℕ → tactic unit 
| 0 := (f 0)         
| (nat.succ n) := do 
    repeat_or_sol n, 
    ok ← list.empty <$> tactic.get_goals,
    if ok then return ()
    else (f n)    

meta def beta_reduction (e: expr): tactic unit := do 
    reduced ← tactic.head_beta e,
    n ← tactic.mk_fresh_name,
    tactic.to_expr ``(%%e=%%reduced) >>= tactic.assert n,
    tactic.reflexivity,
    eq_lemma ← tactic.resolve_name n >>= tactic.to_expr,
    tactic.rewrite_target eq_lemma,
    tactic.clear eq_lemma


end cosette_tactics