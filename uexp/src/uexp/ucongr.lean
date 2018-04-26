import .u_semiring
import .ucongr_lemmas
import .cosette_tactics

/- congruence procedure for u-semiring -/

open tactic

private meta def walk_product : expr → tactic unit
| `(%%a * %%b) := walk_product a >> walk_product b
| `(%%t₁ ≃ %%t₂) :=
  if t₁ > t₂
    then return ()
    else do h ← to_expr ``(eq_symm %%t₁ %%t₂),
            try $ rewrite_target h,
            return ()
| _ := return ()

-- walk the product and normalize equal pred,
-- we maintain an invariant, a ≃ b (a > b)
meta def unify_ueq : tactic unit := do
  t ← tactic.target,
  match t with
  | `(%%a = %%b) := walk_product a >> walk_product b
  | _ := failed
  end

-- collect ueq (equality predicate) from prod
meta def collect_ueq : expr → tactic (list expr)
| `(%%a * %%b) := 
    do lhs ← collect_ueq a,
       rhs ← collect_ueq b,
       return (lhs ++ rhs)
| e := match e with
        | `(%%a ≃ %%b) := return [e] 
        | _            := return []
       end 

-- collect ueq from lhs of goal
meta def collect_lhs_ueq : tactic (list expr) :=
target >>= λ e, 
match e with
| `(%%a = _ ) := collect_ueq a
| _ := return []
end

-- test
meta def test_collect_ueq :=
    do rs ← collect_lhs_ueq,
       tactic.trace rs,
       return ()

lemma prod_ex_1 {s: Schema} (a b c d: Tuple s):
    (a ≃ b) * (b ≃ c) * (c ≃ b) = (a ≃ d) :=
begin
   unify_ueq,
   test_collect_ueq,
   sorry
end

-- make sure all product is right assoc
meta def right_assoc :=
    `[repeat {rewrite time_assoc}]

-- change the goal to the form  a x 1 = b x 1
lemma add_unit (a b: usr):
    a * 1 = b * 1 → a = b :=
begin
    simp,
    intros, 
    assumption,
end

meta def product_to_repr : expr → list expr
| `(%%a * %%b) := a :: product_to_repr b
| e := [e] 

meta def repr_to_product : list expr → tactic expr
| [x] := return x
| (h::t) :=  do te ← repr_to_product t,
                to_expr ``(%%h * %%te)
| [] := failed

meta def get_lhs_repr : tactic (list expr) :=
target >>= λ e,
match e with
| `(%%a = %%b) := return $ product_to_repr a
| _ := failed
end

-- swap i-th element in a product forward
meta def swap_element_forward (i: nat) (l: list expr) : tactic unit :=
    do 
    swapped_list ← list.swap_ith_forward i l,
    origin_expr ← repr_to_product l,
    swapped_expr ← repr_to_product swapped_list,
    eq_lemma ← to_expr ``(%%origin_expr = %%swapped_expr),
    eq_lemma_name ← mk_fresh_name,
    tactic.assert eq_lemma_name eq_lemma,
    repeat_n i $ (to_expr ``(congr_arg (has_mul.mul _)) >>= apply >> return ()),
    applyc `prod_symm_assoc <|> applyc `mul_comm,
    eq_lemma ← resolve_name eq_lemma_name >>= to_expr,
    rewrite_target eq_lemma,
    clear eq_lemma

-- suppose i > j
meta def forward_i_to_j (i : nat) (j: nat) : tactic unit :=
    let loop : nat → tactic unit → tactic unit := 
        λ iter_num next_iter, do
        next_iter,
        repr ← get_lhs_repr,
        swap_element_forward (i - iter_num -1) repr
    in nat.repeat loop (i - j) $ return ()

lemma congr_ex0 (a b c d e f: usr):
    a * (b * (c * (d * e)))  = f :=
begin
    forward_i_to_j 3 1,
    sorry
end

lemma congr_ex1 {s: Schema} (a b c d e f: Tuple s) (R: Tuple s → usr):
     (a ≃ c) * ((b ≃ c) * (a ≃ d) * (e ≃ f))  = (c ≃ a) * ((a ≃ b) * ((b ≃ d) * (e ≃ f)))  :=
begin
    unify_ueq,
    right_assoc,
    apply add_unit,
    try {rw ueq_trans_1 <|> rw ueq_trans_2 <|> rw ueq_trans_3}, 
    sorry
end

lemma congr_ex2 {s: Schema} (a b c d e f: Tuple s) (R: Tuple s → usr):
     (a ≃ c) * (b ≃ c) * (d ≃ e) * (R a) * (R d)  = 
     (a ≃ b) * (b ≃ c) * (e ≃ d) * (R c) * (R e)  :=
begin 
    unify_ueq,
    sorry
end
