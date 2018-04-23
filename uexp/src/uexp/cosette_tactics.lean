section cosette_tactics

def list.swap_ith_forward {α : Type} {f : Type → Type} [alternative f]
  : nat → list α → f (list α)
| 0 (x::y::zs) := pure $ y :: x :: zs
| (nat.succ n) (x::xs) := list.cons x <$> list.swap_ith_forward n xs
| _ _ := failure

end cosette_tactics