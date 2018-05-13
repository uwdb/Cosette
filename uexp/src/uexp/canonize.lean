import .cosette_tactics .TDP 
open tactic

section canonize

meta inductive canonize_term_repr : Type
| sig : expr → list name → canonize_term_repr
| prod : list expr → canonize_term_repr

meta def expr_to_canonize_term_repr (ex : expr)
  : tactic canonize_term_repr :=
  match sigma_expr_to_sigma_repr ex with
  | ⟨[], e⟩ := canonize_term_repr.prod <$> product_to_repr e
  | repr := function.uncurry canonize_term_repr.sig
            <$> sigma_repr_to_closed_body_expr repr
  end

private meta definition rw_kc_in_prod_repr (kc : key_constraint) :
  list expr → tactic (list expr)
| (`(denoteProj %%k₁ %%t₁ ≃ denoteProj %%k₂ %%t'₁) ::
   `(denote_r %%R₁ %%t₂) ::
   `(denote_r %%R₂ %%t'₂) :: terms) :=
  if k₁ = k₂ ∧ t₁ = t₂ ∧ t'₁ = t'₂ ∧ R₁ = R₂
     ∧ k₁ = kc.column ∧ R₁ = kc.table
    then (λ congr' rel', congr' :: rel' :: terms)
         <$> to_expr ``(%%t₁ ≃ %%t'₁)
         <*> to_expr ``(denote_r %%R₁ %%t₁)
    else list.cons <$> to_expr ``(denoteProj %%k₁ %%t₁ ≃ denoteProj %%k₂ %%t'₁) <*>
         (list.cons <$> to_expr ``(denote_r %%R₁ %%t₂) <*>
         (list.cons <$> to_expr ``(denote_r %%R₂ %%t'₂) <*>
          rw_kc_in_prod_repr terms))
| (x :: terms) := list.cons x <$> rw_kc_in_prod_repr terms
| [] := return []

meta definition canonize : tactic unit :=
  let rewrite_constraint_occurence (kc : key_constraint) (e : expr) : tactic unit := do
    repr ← expr_to_canonize_term_repr e,
    match repr with
    | canonize_term_repr.sig body lconsts := do
      body_terms ← product_to_repr body,
      body' ← rw_kc_in_prod_repr kc body_terms,
      body'_expr ← repr_to_product body',
      rewritten_sigma_repr ← closed_sigma_repr_to_sigma_repr body'_expr lconsts,
      rewritten_expr ← sigma_repr_to_sigma_expr rewritten_sigma_repr,
      eq_lemma ← tactic.to_expr ``(%%e = %%rewritten_expr),
      lemma_name ← tactic.mk_fresh_name,
      tactic.assert lemma_name eq_lemma,
      repeat_n lconsts.length `[apply congr_arg usr.sig, funext],
      rewrite_target kc.name,
      ac_refl,
      eq_lemma_name ← tactic.resolve_name lemma_name >>= tactic.to_expr,
      tactic.rewrite_target eq_lemma_name,
      tactic.clear eq_lemma_name
    | canonize_term_repr.prod terms := do
      terms' ← rw_kc_in_prod_repr kc terms,
      rewritten_expr ← repr_to_product terms',
      eq_lemma ← tactic.to_expr ``(%%e = %%rewritten_expr),
      lemma_name ← tactic.mk_fresh_name,
      tactic.assert lemma_name eq_lemma,
      rewrite_target kc.name,
      ac_refl,
      eq_lemma_name ← tactic.resolve_name lemma_name >>= tactic.to_expr,
      tactic.rewrite_target eq_lemma_name,
      tactic.clear eq_lemma_name
    end
  in do
  constraints ← find_keys,
  monad.mapm' (λ kc, repeat $ get_lhs >>= rewrite_constraint_occurence kc)
              constraints,
  monad.mapm' (λ kc, repeat $ get_rhs >>= rewrite_constraint_occurence kc)
              constraints

end canonize