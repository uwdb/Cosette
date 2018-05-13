import .u_semiring
import .cosette_lemmas
import .cosette_tactics

/- congruence procedure for u-semiring -/

open tactic

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

private meta def no_ueq (l: list expr) : tactic bool :=
    list.foldl (λ v e, do v' ← v, return $ v' && ¬ (is_ueq e)) (return tt) l

meta def add_unit_if_needed : tactic unit := do 
    lhs ← get_lhs,
    l ← ra_product_to_repr lhs,
    all_u ← all_ueq l,
    no_u ← no_ueq l,
    if all_u then applyc `add_unit -- add unit when there is no relation expr
    else if no_u then applyc `add_unit_l -- add unit when there is no ueq
    else return ()

meta def move_ueq_step : tactic unit := do
        lhs ← get_lhs,
        l ← ra_product_to_repr lhs,
        if ueq_right_order l then do
            failed
        else do 
            idx ← idx_of_bad 0 l,
            swap_element_forward (idx - 1) l

-- move ueq, TODO: revisit here to get general SPNF form 
meta def move_ueq: tactic unit :=
    `[right_assoc,
      add_unit_if_needed,
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
    | `(((%%a ≃ %%b) * ((%%c ≃ %%d) * _)) * _ * _ ) := 
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
    | `((%%a ≃ %%b) * (%%c ≃ %%d) * _ * _) :=
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

meta def ucongr_step : tactic unit := do 
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
    repeat $ applyc `move_ueq_between_com,
    if list.length new_ueq > 1 then do  -- progress!
        ucongr_lhs
    else return ()

meta def subst_step : tactic unit := do 
    l ← get_lhs,
    match l with
    | `((%%a ≃ %%b) * %%c * %%d * %%e)   := do 
        ty ← infer_type a,
        let body := expr.subst_var a e,
        let em : expr := (expr.lam `x binder_info.default ty body),
        lem ← to_expr ``(@ueq_subst_in_spnf _ %%a %%b %%c %%d %%em),
        try $ rewrite_target lem,
        l' ← get_lhs_expr3,
        beta_reduction l'
    | `((%%a ≃ %%b) * %%c * %%e) := do 
        ty ← infer_type a,
        let body := expr.subst_var a e,
        let em : expr := (expr.lam `x binder_info.default ty body),
        lem ← to_expr ``(@ueq_subst_in_spnf' _ %%a %%b %%c %%em),
        try $ rewrite_target lem,
        l' ← get_lhs_expr3,
        beta_reduction l'
    | _ := return ()
    end

private meta def ueq_toporder (e₁ e₂: expr) : bool :=
    match e₁ with 
    | `(%%a ≃ %%b) := match e₂ with 
                        | `(%%c ≃ %%d) := if (d > a) || (d = a) then ff else tt 
                        | _ := tt
                       end
    | _ := tt
    end

-- topology sort ueqs, so that we can do a single pass of substition 
meta def topsort_lhs : tactic unit := do 
    repr ← get_lhs_repr1,
    sorted ← return $ list.qsort ueq_toporder repr,
    origin ← repr_to_product repr,
    new ← repr_to_product sorted,
    eq_lemma ← to_expr ``(%%origin = %%new),
    eq_lemma_name ← mk_fresh_name,
    tactic.assert eq_lemma_name eq_lemma,
    try ac_refl,
    eq_lemma ← resolve_name eq_lemma_name >>= to_expr,
    rewrite_target eq_lemma,
    clear eq_lemma

meta def subst_lhs : tactic unit := do
    topsort_lhs,
    repr ← get_lhs_repr1,
    let l := list.length repr in
    let loop : nat → tactic unit:=
        λ iter_num, do 
            forward_i_to_j iter_num 0,
            subst_step in
    repeat_or_sol loop l

private meta def remove_dup_step : tactic unit :=
    `[repeat {rw ueq_dedup<|> rw ueq_dedup'}]

-- assuming LHS and RHS are already in SPNF
meta def remove_dup_ueq : tactic unit := do
    repr ← get_lhs_repr1,
    sorted ← return $ list.qsort (λ x y, x > y) repr,
    origin ← repr_to_product repr,
    new ← repr_to_product sorted,
    eq_lemma ← to_expr ``(%%origin = %%new),
    eq_lemma_name ← mk_fresh_name,
    tactic.assert eq_lemma_name eq_lemma,
    try ac_refl,
    eq_lemma ← resolve_name eq_lemma_name >>= to_expr,
    rewrite_target eq_lemma,
    clear eq_lemma,
    r2 ← get_lhs_repr1,
    remove_dup_step

private meta def remove_pred_step : tactic unit := 
    `[repeat {rw pred_cancel <|> rw pred_cancel'}]

meta def remove_dup_pred : tactic unit := do 
    repr ← get_lhs_repr3,
    sorted ← return $ list.qsort (λ x y, x > y) repr,
    origin ← repr_to_product repr,
    new ← repr_to_product sorted,
    eq_lemma ← to_expr ``(%%origin = %%new),
    eq_lemma_name ← mk_fresh_name,
    tactic.assert eq_lemma_name eq_lemma,
    try ac_refl,
    eq_lemma ← resolve_name eq_lemma_name >>= to_expr,
    rewrite_target eq_lemma,
    clear eq_lemma,
    remove_pred_step

meta def ucongr : tactic unit := do 
    solved_or_continue $ (do split_pairs,
    solved_or_continue $ (do unify_ueq,
    move_ueq,
    applyc `add_unit_m,
    remove_dup_ueq,
    solved_or_continue $ (do applyc `ueq_symm,
    remove_dup_ueq,
    solved_or_continue $ (do ucongr_lhs,
    solved_or_continue $ (do applyc `ueq_symm,
    ucongr_lhs,
    solved_or_continue $ (do subst_lhs,
    solved_or_continue $ (do applyc `ueq_symm,
    subst_lhs,
    solved_or_continue $ (do remove_dup_pred, 
    solved_or_continue $ (do applyc `ueq_symm,
    remove_dup_pred,
    solved_or_continue ac_refl)))))))))

