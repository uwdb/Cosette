import system.io
open nat io
open list io

section cosette_tactics

def list.swap_ith_forward {α : Type} {f : Type → Type} [alternative f]
    : nat → list α → f (list α)
| 0 (x::y::zs) := pure $ y :: x :: zs
| (nat.succ n) (x::xs) := list.cons x <$> list.swap_ith_forward n xs
| _ _ := failure

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

end cosette_tactics