import .u_semiring
import .cosette_tactics
import .ucongr
import .extra_constants
import .sql
section TDP

open tactic

meta def break_p : expr →  tactic (list expr)
| `(%%a ≃ %%b) := 
  match a, b with
    | `((%%a1, %%a2)) , `((%%b1, %%b2)) := do
      x1 ← to_expr ``((%%a1 ≃ %%b1)),
      x2 ← to_expr ``((%%a2 ≃ %%b2)),
      l ← break_p x1,
      r ← break_p x2,
      return (l ++ r)
    | _, _ := do x ← to_expr ``((%%a ≃ %%b)), return [x]
  end 
| x := return [x]

meta def split_p (ex : expr) : tactic (list expr) :=
match ex with
| `(%%a ≃ %%b) := 
  match a, b with
    | `((%%a1, %%a2)) , `((%%b1, %%b2)) := do
      x1 ← to_expr ``((%%a).1 ≃ (%%b).1),
      x2 ← to_expr ``((%%a).2 ≃ (%%b).2),
      return [x1, x2]
    | _, _ := return [ex]
  end 
| x := return [x]
end

meta def split_l (ex : expr) : tactic (list expr) :=
match ex with
| `(%%a ≃ %%b) := 
  match a, b with
    | _ , `((%%c, %%d)) := do
      /-
      ty ← infer_type a,
      let args := expr.get_app_args ty,
      (r1, r2) ← match args.nth 0 with
      | some `(%%r1 ++ %%r2) := return (r1, r2)
      | _ := failure
      end,
      trace (r1, r2),
      ty2 ← to_expr ``((@cast %%ty (Tuple %%r1 × Tuple %%r2) (by tactic.reflexivity) (%%a)).1),
      -/
      x1 ← to_expr ``((%%a).1 ≃ %%c),
      x2 ← to_expr ``((%%a).2 ≃ %%d),
      return [x1, x2]
    | _, _ := return [ex]
  end 
| x := return [x]
end

meta def split_r (ex : expr) : tactic (list expr) :=
match ex with
| `(%%a ≃ %%b) := 
  match a, b with
    | `((%%c, %%d)), _ := do
      ty ← infer_type b,
      let args := expr.get_app_args ty,
      r ← match args.nth 0 with
      | some `(%%r ++ _) := return r
      | _ := failure
      end,
      ty2 ← to_expr ``((@cast %%ty (Tuple %%r × Tuple %%r) (by tactic.reflexivity) (%%b)).1),
      x1 ← to_expr ``(%%c ≃ (%%b).1),
      x2 ← to_expr ``(%%d ≃ (%%b).2),
      return [x1, x2]
    | _, _ := return [ex]
  end 
| x := return [x]
end


meta def flatmap_in_repr (f: expr → tactic (list expr)): list expr → tactic (list expr)
| [x] := f x
| (h::t) := do h' ← f h,
            t' ← flatmap_in_repr t,
            return (h' ++ t')
| [] := return []

meta def split_pair_in_repr (r: list expr) : tactic (list expr) := do
r1 ← flatmap_in_repr split_p r,
s' ← flatmap_in_repr split_l r1,
r ← flatmap_in_repr split_r s',
return r

meta def normalize_step (n: nat) : tactic unit := do 
   repeat_n n $ tactic.applyc `congr_arg >> tactic.funext,
   split_pairs

-- normalize body of a sigma
meta def normalize_sig_body : tactic unit := do
  `[try {unfold pair}],
  lr ← get_lhs_sigma_repr,
  lr_body_closed ← sigma_repr_to_closed_body_expr lr,
  match lr_body_closed with 
  | ⟨body, names⟩ := do
    le ← product_to_repr body,
    s1 ← split_pair_in_repr le, 
    body' ← repr_to_product s1,
    origin ← get_lhs,
    let abstracted := expr.abstract_locals body' (list.reverse names),
    new ← sigma_repr_to_sigma_expr ⟨lr.var_schemas, abstracted⟩,
    eq_lemma ← tactic.to_expr ``(%%origin = %%new),
    lemma_name ← tactic.mk_fresh_name,
    tactic.assert lemma_name eq_lemma,
    tactic.focus1 $ normalize_step lr.var_schemas.length,
    tactic.try tactic.ac_refl,
    eq_lemma_name ← tactic.resolve_name lemma_name >>= tactic.to_expr,
    tactic.rewrite_target eq_lemma_name,
    tactic.clear eq_lemma_name
  end

meta def removal_step : tactic unit := do
  lhs ← get_lhs,
  remove_sig_step lhs

meta def remove_dup_sigs : tactic unit := do 
  -- this is a workround, this unnest 3 levels of pair
  -- repeat_n 3 $ normalize_sig_body >> try dsimp_target, 
  repeat_n 3 normalize_sig_body,
  lhs ← get_lhs,
  s ← sig_body_size,
  final ← let loop : ℕ → ℕ → (tactic ℕ) := λ s n, do
    forward_i_to_j_in_sig n 0,
    removal_step,
    sig_body_size
  in repeat_if_progress loop s s,
  return ()

meta def is_sig (e: expr) : bool :=
match e with 
| `(usr.sig _) := tt
| _ := ff
end

/- step 1: move sigs inside front -/
meta def unify_sigs_step_1: tactic unit := do
  lr ← get_lhs_sigma_repr,
  lr_body_closed ← sigma_repr_to_closed_body_expr lr,
  match lr_body_closed with 
  | ⟨body, names⟩ := do 
    le ← product_to_repr body,
    sl ← return $ list.qsort 
                  (λ e1 e2, if is_sig e1 then tt else if is_sig e2 then ff else tt) 
                  le,
    body' ← repr_to_product sl,
    origin ← get_lhs,
    let abstracted := expr.abstract_locals body' (list.reverse names),
    new ← sigma_repr_to_sigma_expr ⟨lr.var_schemas, abstracted⟩,
    eq_lemma ← tactic.to_expr ``(%%origin = %%new),
    lemma_name ← tactic.mk_fresh_name,
    tactic.assert lemma_name eq_lemma,
    repeat_n lr.var_schemas.length $ tactic.applyc `congr_arg >> tactic.funext,
    tactic.try tactic.ac_refl,
    eq_lemma_name ← tactic.resolve_name lemma_name >>= tactic.to_expr,
    tactic.rewrite_target eq_lemma_name,
    tactic.clear eq_lemma_name
  end 

/- step 2: distribute sumation -/
meta def unify_sigs_step_2: tactic unit := do 
  lr ← get_lhs_sigma_repr,
  lr_body_closed ← sigma_repr_to_closed_body_expr lr,
  match lr_body_closed with 
  | ⟨body, names⟩ := do 
    le ← product_to_repr body,
    h ←  return $ list.head le,
    t ← return $ list.tail le,
    if ¬ (is_sig h) then tactic.failed -- if there is no sig inside, terminate
    else do
    sr ← return $ sigma_expr_to_sigma_repr h,
    (b, n) ← sigma_repr_to_closed_body_expr sr,
    body' ← repr_to_product (b::t),
    names' ← return $ (n ++ names),
    let abstracted := expr.abstract_locals body' (list.reverse names'),
    new ← sigma_repr_to_sigma_expr ⟨(lr.var_schemas) ++ (sr.var_schemas), abstracted⟩,
    origin ← get_lhs,
    eq_lemma ← tactic.to_expr ``(%%origin = %%new),
    lemma_name ← tactic.mk_fresh_name,
    tactic.assert lemma_name eq_lemma,
    repeat_n lr.var_schemas.length $ tactic.applyc `congr_arg >> tactic.funext,
    tactic.applyc `sig_distr_time_r,
    eq_lemma_name ← tactic.resolve_name lemma_name >>= tactic.to_expr,
    tactic.rewrite_target eq_lemma_name,
    tactic.clear eq_lemma_name
  end

meta def unify_sigs : tactic unit :=
  tactic.repeat $ unify_sigs_step_1 >> unify_sigs_step_2

meta def TDP' (easy_case_solver : tactic unit) : tactic unit :=
  let loop (iter_num : ℕ) (next_iter : tactic unit) : tactic unit :=
      next_iter <|> do
      move_sig_to_front iter_num,
      to_expr ``(congr_arg usr.sig) >>= apply,
      funext,
      easy_case_solver <|> TDP'
  in do
    unify_sigs,
    remove_dup_sigs,
    applyc `ueq_symm,
    remove_dup_sigs,
    num_vars ← list.length <$> usr_sigma_repr.var_schemas <$> get_lhs_sigma_repr,
    nat.repeat loop num_vars easy_case_solver

meta def TDP := TDP' $ ac_refl <|> ucongr

end TDP
