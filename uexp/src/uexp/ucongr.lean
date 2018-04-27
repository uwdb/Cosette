import .u_semiring
import .ucongr_lemmas
import .cosette_tactics

/- congruence procedure for u-semiring -/

open tactic

private meta def flip_ueq : expr → tactic unit
| `(%%a * %%b) := flip_ueq a >> flip_ueq b
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
  | `(%%a = %%b) := flip_ueq a >> flip_ueq b
  | _ := failed
  end

meta def remove_unit : tactic unit :=
    `[repeat {rw time_one <|> rw time_one'}]

-- collect ueq (equality predicate) from prod
meta def collect_ueq : expr → tactic (list expr)
| `(%%a * %%b) := 
    do l ← collect_ueq a,
       r ← collect_ueq b,
       return (l ++ r)
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

meta def product_to_repr : expr → list expr
| `(%%a * %%b) := a :: product_to_repr b
| e := [e] 

meta def repr_to_product : list expr → tactic expr
| [x] := return x
| (h::t) :=  do te ← repr_to_product t,
                to_expr ``(%%h * %%te)
| [] := failed

meta def get_lhs_repr1 : tactic (list expr) :=
target >>= λ e,
match e with
| `(%%a * _ = %%b) := return $ product_to_repr a
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
        repr ← get_lhs_repr1,
        swap_element_forward (i - iter_num -1) repr
    in nat.repeat loop (i - j) $ return ()

meta def rw_trans : tactic unit :=
    do 
    ueq_dict ← collect_lhs_ueq,
    t ← get_lhs,
    match t with
    | `(((%%a ≃ %%b) * ((%%c ≃ %%d) * _)) * _ ) := 
        if (b = c) then
            if (a > d) then do 
                ne ← to_expr ``(%%a ≃ %%d),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_1
            else failed
        else if (a = c) then 
            if (b > d) then do
                ne ← to_expr ``(%%b ≃ %%d),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_2_g 
            else if (d > b) then do
                ne ← to_expr ``(%%d ≃ %%b),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_2_l
            else failed -- there should no other case (TODO: revisit here)
        else if (b = d) then 
            if (a > c) then do 
                ne ← to_expr ``(%%a ≃ %%c),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_3_g
            else if (c > a) then do
                ne ← to_expr ``(%%c ≃ %%a),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_3_l
            else failed -- same here
        else if (a = d) then
            if (c > b) then do 
                ne ← to_expr ``(%%c ≃ %%b),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_4
            else failed -- same here 
        else return () -- do nothing if cannot use trans of ueq
    | `((%%a ≃ %%b) * (%%c ≃ %%d) * _) :=
        if (b = c) then
            if (a > d) then do 
                ne ← to_expr ``(%%a ≃ %%d),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_1'
            else failed
        else if (a = c) then 
            if (b > d) then do
                ne ← to_expr ``(%%b ≃ %%d),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_2_g' 
            else if (d > b) then do
                ne ← to_expr ``(%%d ≃ %%b),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_2_l'
            else failed -- there should no other case (TODO: revisit here)
        else if (b = d) then 
            if (a > c) then do 
                ne ← to_expr ``(%%a ≃ %%c),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_3_g'
            else if (c > a) then do
                ne ← to_expr ``(%%c ≃ %%a),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_3_l'
            else failed -- same here
        else if (a = d) then
            if (c > b) then do 
                ne ← to_expr ``(%%c ≃ %%b),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_4'
            else failed -- same here 
        else return () -- do nothing if cannot use trans of ueq
    | _ := trace "rw_trans fail" >> failed
    end

meta def pre_ucongr : tactic unit :=
    `[unify_ueq, right_assoc, apply add_unit]

meta def ucongr : tactic unit := do 
    pre_ucongr,
    return ()
