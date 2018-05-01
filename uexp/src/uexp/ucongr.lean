import .u_semiring
import .ucongr_lemmas
import .cosette_tactics

/- congruence procedure for u-semiring -/

open tactic

private meta def usimp : tactic unit :=
    `[try {simp}]

private meta def flip_ueq : expr → tactic unit
| `(%%a * %%b) := flip_ueq a >> flip_ueq b
| `(%%t₁ ≃ %%t₂) :=
    if t₁ > t₂ then return ()
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

-- make sure all product is right assoc
meta def right_assoc :=
    `[repeat {rewrite time_assoc}]

private meta def product_to_repr' : expr → list expr
| `(%%a * %%b) := a :: product_to_repr' b
| e := [e] 

meta def product_to_repr (e: expr) : tactic (list expr) :=
return $ product_to_repr' e 

meta def repr_to_product : list expr → tactic expr
| [x] := return x
| (h::t) :=  do te ← repr_to_product t,
                to_expr ``(%%h * %%te)
| [] := failed

meta def get_lhs_repr1 : tactic (list expr) :=
target >>= λ e,
match e with
| `(%%a * _ = %%b) := product_to_repr a
| _ := failed
end

meta def get_lhs_repr2 : tactic (list expr) :=
target >>= λ e,
match e with
| `(_ * %%a = %%b) := product_to_repr a
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

private meta def is_ueq : expr → bool
| `(_ ≃ _) := tt
| _ := ff

-- make sure ueq is in front of relation
private meta def ueq_right_order : list expr → bool
| [x] := tt 
| (a :: b :: xs) := 
    if ((¬(is_ueq a)) && (is_ueq b)) then ff
    else ueq_right_order (b::xs) 
| [] := tt

-- find the index of relation that is behind ueq
private meta def idx_of_bad : nat → list expr → tactic nat :=
λ pos l, 
match l with 
| [x] := failure
| (a :: b :: xs) :=
    if ((¬(is_ueq a)) && (is_ueq b)) then return (pos+1)
    else idx_of_bad (pos+1) (b::xs)
| []:= failure
end

private meta def all_ueq (l: list expr) : tactic bool :=
    list.foldl (λ v e, do v' ← v, return $ v' && (is_ueq e)) (return tt) l

meta def add_unit_when_all_ueq : tactic unit := do 
    lhs ← get_lhs,
    l ← product_to_repr lhs,
    all_u ← all_ueq l,
    if all_u then applyc `add_unit
    else return ()

meta def test_bad : tactic unit := do 
    lhs ← get_lhs,
    l ←  product_to_repr lhs, 
    a ← idx_of_bad 0 l,
    trace l,
    trace a,
    return () 

meta def move_ueq_step : tactic unit := do
        lhs ← get_lhs,
        l ← product_to_repr lhs,
        if ueq_right_order l then do
            failed
        else do 
            idx ← idx_of_bad 0 l,
            swap_element_forward (idx - 1) l

-- move ueq, TODO: revisit here to get general SPNF form 
meta def move_ueq: tactic unit :=
    `[right_assoc,
      add_unit_when_all_ueq,
      apply ueq_symm,
      add_unit_when_all_ueq,
      repeat {move_ueq_step},
      repeat {apply ueq_left_assoc_lem},
      repeat {apply ueq_right_assoc_lem},
      repeat {apply ueq_right_assoc_lem'},
      apply ueq_symm,
      repeat {move_ueq_step},
      repeat {apply ueq_left_assoc_lem},
      repeat {apply ueq_right_assoc_lem},
      repeat {apply ueq_right_assoc_lem'}
      ]

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
            else fail "fail to apply ueq_trans_1"
        else if (a = c) then 
            if (b > d) then do
                ne ← to_expr ``(%%b ≃ %%d),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_2_g 
            else if (d > b) then do
                ne ← to_expr ``(%%d ≃ %%b),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_2_l
            else fail "fail to apply ueq_trans_2_l"
        else if (b = d) then 
            if (a > c) then do 
                ne ← to_expr ``(%%a ≃ %%c),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_3_g
            else if (c > a) then do
                ne ← to_expr ``(%%c ≃ %%a),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_3_l
            else fail "fail to apply ueq_trans_3_l"
        else if (a = d) then
            if (c > b) then do 
                ne ← to_expr ``(%%c ≃ %%b),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_4
            else fail "fail to apply ueq_trans_4"  
        else return () -- do nothing if cannot use trans of ueq
    | `((%%a ≃ %%b) * (%%c ≃ %%d) * _) :=
        if (b = c) then
            if (a > d) then do 
                ne ← to_expr ``(%%a ≃ %%d),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_1'
            else fail "fail to apply ueq_trans_1'"
        else if (a = c) then 
            if (b > d) then do
                ne ← to_expr ``(%%b ≃ %%d),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_2_g' 
            else if (d > b) then do
                ne ← to_expr ``(%%d ≃ %%b),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_2_l'
            else fail "fail to apply ueq_trans_2_l'"
        else if (b = d) then 
            if (a > c) then do 
                ne ← to_expr ``(%%a ≃ %%c),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_3_g'
            else if (c > a) then do
                ne ← to_expr ``(%%c ≃ %%a),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_3_l'
            else fail "fail to apply ueq_trans_3_l'"
        else if (a = d) then
            if (c > b) then do 
                ne ← to_expr ``(%%c ≃ %%b),
                if expr_in ne ueq_dict then return ()
                else applyc `ueq_trans_4'
            else fail "fail to apply ueq_trans_4'" 
        else return () -- do nothing if cannot use trans of ueq
    | _ := fail "rw_trans fail"
    end

meta def pre_ucongr : tactic unit :=
    `[remove_unit, right_assoc, apply add_unit]

meta def ucongr_step : tactic unit := do 
    pre_ucongr,
    repr ← get_lhs_repr1,
    let l := list.length repr in
    let inner_loop : nat → tactic unit → tactic unit :=
        λ iter_num next_iter, do 
          next_iter,
          forward_i_to_j (1+iter_num) 1,
          rw_trans in 
    let outter_loop : nat → tactic unit → tactic unit :=
        λ iter_num next_iter, do 
          next_iter,
          forward_i_to_j iter_num 0,
          nat.repeat inner_loop (l-1) $ return ()
    in do nat.repeat outter_loop l $ return ()

meta def ucongr_lhs : tactic unit := do 
    ucongr_step,
    new_ueq ← get_lhs_repr2,
    remove_unit,
    if list.length new_ueq > 1 then do  -- progress!
        ucongr_lhs
    else return ()

meta def ucongr : tactic unit := do 
    usimp,  -- simp can remove duplicate
    ok ← list.empty <$> tactic.get_goals,
    if ok then do
        return ()
    else do
    unify_ueq,
    ucongr_lhs,
    applyc `ueq_symm,
    ucongr_lhs,
    solved ← list.empty <$> tactic.get_goals,
    if solved then 
    return ()
    else ac_refl

lemma congr_ex3 {s: Schema} (a b c d e f: Tuple s) (R: Tuple s → usr):
     (a ≃ b) * (R c) * (a ≃ c) * (R d) * (b ≃ c) * (d ≃ e) * (R d)  = 
     (a ≃ b) * (b ≃ c) * (e ≃ d) * (R c) * (R e)  :=
begin 
    move_ueq,
    sorry
end

lemma congr_ex5 {s: Schema} (a b c d e f: Tuple s) (R: Tuple s → usr):
     (a ≃ f) * (a ≃ c) * ((b ≃ c) * (a ≃ d) * (e ≃ f))  = (c ≃ a) * ((a ≃ b) * ((b ≃ d) * (e ≃ f)))  :=
begin
    move_ueq,
    sorry
end