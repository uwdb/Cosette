import .u_semiring
import .cosette_tactics
import .ucongr
import .extra_constants
import .sql
section TDP

open tactic

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
  repeat_n i $ applyc `congr_arg >> funext,
  applyc `sig_commute,
  eq_lemma ← resolve_name eq_lemma_name >>= to_expr,
  rewrite_target eq_lemma,
  clear eq_lemma

meta def move_once (i: nat) : tactic unit := do
  lr ← get_lhs_sigma_repr,
  swap_ith_sigma_forward i lr

meta def move_to_front (i : nat) : tactic unit :=
  let loop : ℕ → tactic unit → tactic unit :=
      λ iter_num next_iter, do
        lr ← get_lhs_sigma_repr,
        swap_ith_sigma_forward iter_num lr,
        next_iter
  in nat.repeat loop i $ return ()

--move back i to j
meta def move_sig_back (i: nat) (j: nat) :=
  let loop: nat → tactic unit → tactic unit :=
    λ num next, do 
      next, 
      move_once (i+num)
  in nat.repeat loop (j-i) $ return ()

#check @cast

#check expr.instantiate_local
meta def split_l : expr → tactic (list expr)
| `(%%a ≃ %%b) := 
  match b with 
    | `((%%c, %%d)) := do
      trace "here", 
      ty ← infer_type a,
      let args := expr.get_app_args ty,
      r ← match args.nth 0 with
      | some `(%%r ++ _) := return r
      | _ := failure
      end,
      trace ty,
      trace r,
      ty2 ← to_expr ``((@cast %%ty (Tuple %%r × Tuple %%r) (by tactic.reflexivity) (%%a)).1),
      trace "BELOW",
      trace ty2,
      c_ty ← infer_type c,
      a_ty ← infer_type a,
      trace a_ty,
      trace c_ty,
      -- x1 ← to_expr ``((%%a).1 ≃ %%c),
      -- x2 ← to_expr ``((%%a).1 ≃ %%d),
      trace "here1",
      return []
    | x := return [x]
  end 
| x := do trace "no!", return [x]

meta def split_r : expr → tactic (list expr)
| `((pair %%a %%b) ≃ %%c) := do 
    x1 ← to_expr ``(%%a ≃ (%%c).1),
    x2 ← to_expr ``(%%b ≃ (%%c).2),
    return [x1, x2]
| x := do trace "no!", return [x]


meta def flatmap_in_repr (f: expr → tactic (list expr)): list expr → tactic (list expr)
| [x] := f x
| (h::t) := do h' ← f h,
            t' ← flatmap_in_repr t,
            return (h' ++ t')
| [] := return []

meta def split_pair_in_repr (r: list expr) : tactic (list expr) := do
s' ←  flatmap_in_repr split_l r,
flatmap_in_repr split_r s' 

-- normalize body of a sigma
meta def normalize_sig_body : tactic unit := do
  `[try {unfold pair}],
  lr ← get_lhs_sigma_repr,
  match lr with 
  |⟨xs, body⟩ := do
    le ← product_to_repr body,
    sl ← split_pair_in_repr le,
    trace sl,
    body' ← repr_to_product le,
    origin ← get_lhs,
    new ← sigma_repr_to_sigma_expr ⟨xs, body'⟩,
    eq_lemma ← tactic.to_expr ``(%%origin = %%new),
    lemma_name ← tactic.mk_fresh_name,
    tactic.assert lemma_name eq_lemma,
    repeat_n (list.length xs) $ tactic.applyc `congr_arg >> tactic.funext,
    tactic.ac_refl,
    eq_lemma_name ← tactic.resolve_name lemma_name >>= tactic.to_expr,
    tactic.rewrite_target eq_lemma_name,
    tactic.clear eq_lemma_name
  end

-- a single step removal
meta def removal_step : tactic unit := do
  lr ← get_lhs_sigma_repr,
  match lr with 
  | ⟨xs, body⟩ := do 
    le ← ra_product_to_repr body,
    match list.head le with
    | `(%%a ≃ %%b) := 
      match a, b with
      | (expr.var n), e := do 
        let l := (list.length xs),
        move_sig_back (l - 1 - n) (l - 1),
        lr' ← get_lhs_sigma_repr,
        match lr' with 
        | ⟨xs', body'⟩ := do 
          match body' with 
          | `((%%c ≃ %%d) * %%f) := do
            let sub_expr := expr.subst_var' c d f, 
            let new_body := expr.lower_vars sub_expr 1 1,
            old_expr ← sigma_repr_to_sigma_expr lr',
            new_expr ←  sigma_repr_to_sigma_expr ⟨list.take (l-1) xs', new_body⟩, 
            eq_lemma ← tactic.to_expr ``(%%old_expr = %%new_expr),
            lemma_name ← tactic.mk_fresh_name,
            tactic.assert lemma_name eq_lemma,
            repeat_n (l-1) $ tactic.applyc `congr_arg >> tactic.funext,
            tactic.applyc `sig_eq_subst_r,
            eq_lemma_name ← tactic.resolve_name lemma_name >>= tactic.to_expr,
            tactic.rewrite_target eq_lemma_name,
            tactic.clear eq_lemma_name
          | _ := tactic.fail "fail in removal step"
          end 
        end
      | e, (expr.var n) := do 
        let l := (list.length xs),
        move_sig_back (l - 1 - n) (l - 1),
        lr' ← get_lhs_sigma_repr,
        match lr' with 
        | ⟨xs', body'⟩ := do 
          match body' with 
          | `((%%c ≃ %%d) * %%f) := do
            let sub_expr := expr.subst_var' d c f, 
            let new_body := expr.lower_vars sub_expr 1 1,
            old_expr ← sigma_repr_to_sigma_expr lr',
            new_expr ←  sigma_repr_to_sigma_expr ⟨list.take (l-1) xs', new_body⟩, 
            eq_lemma ← tactic.to_expr ``(%%old_expr = %%new_expr),
            lemma_name ← tactic.mk_fresh_name,
            tactic.assert lemma_name eq_lemma,
            repeat_n (l-1) $ tactic.applyc `congr_arg >> tactic.funext,
            tactic.applyc `sig_eq_subst_l,
            eq_lemma_name ← tactic.resolve_name lemma_name >>= tactic.to_expr,
            tactic.rewrite_target eq_lemma_name,
            tactic.clear eq_lemma_name
          | _ := tactic.fail "fail in removal step"
          end 
        end
      | _, _ := return ()
      end
    | _ := return ()
    end 
  end

meta def remove_dup_sigs : tactic unit := do 
  normalize_sig_body,
  lhs ← get_lhs,
  s ← sig_body_size,
  final ← let loop : ℕ → ℕ → (tactic ℕ) := λ s n, do
    forward_i_to_j_in_sig n 0,
    removal_step,
    sig_body_size
  in repeat_if_progress loop s s,
  return ()

meta def TDP' (easy_case_solver : tactic unit) : tactic unit :=
  let loop (iter_num : ℕ) (next_iter : tactic unit) : tactic unit :=
      next_iter <|> do
      move_to_front iter_num,
      to_expr ``(congr_arg usr.sig) >>= apply,
      funext,
      easy_case_solver <|> TDP'
  in do
    remove_dup_sigs,
    applyc `ueq_symm,
    remove_dup_sigs,
    num_vars ← list.length <$> usr_sigma_repr.var_schemas <$> get_lhs_sigma_repr,
    nat.repeat loop num_vars easy_case_solver

meta def TDP := TDP' $ ac_refl <|> ucongr

end TDP
