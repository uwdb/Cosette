import ..u_semiring ..sql ..extra_constants
import .cosette_tactics .ucongr

section TDP

open tactic

meta def normalize_sig_body_lhs : tactic unit := do
  normalize_sig_body get_lhs

meta def removal_step : tactic unit := do
  remove_sig_step get_lhs

meta def remove_dup_sigs_lhs : tactic unit := do 
  -- this is a workround, this unnest 3 levels of pair
  -- repeat_n 3 $ normalize_sig_body_lhs >> try dsimp_target, 
  repeat_n 3 normalize_sig_body_lhs,
  lhs ← get_lhs,
  s ← sig_body_size get_lhs,
  final ← let loop : ℕ → ℕ → (tactic ℕ) := λ s n, do
    forward_i_to_j_in_sig_lhs n 0,
    removal_step,
    sig_body_size get_lhs
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
      move_sig_to_front get_lhs iter_num,
      to_expr ``(congr_arg usr.sig) >>= apply,
      funext,
      easy_case_solver <|> TDP'
  in do
    unify_sigs,
    remove_dup_sigs_lhs,
    applyc `ueq_symm,
    remove_dup_sigs_lhs,
    num_vars ← list.length <$> usr_sigma_repr.var_schemas <$> get_lhs_sigma_repr,
    nat.repeat loop num_vars easy_case_solver

meta def TDP := TDP' $ ac_refl <|> ucongr

end TDP
