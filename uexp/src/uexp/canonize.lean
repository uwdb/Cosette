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

private meta definition rw_kc_in_prod_repr (kc : key_constraint) (assumptions : list expr)
  : expr → tactic (expr × expr)
| `(denoteProj %%k₁ %%t ≃ denoteProj %%k₂ %%t') :=
  let is_denote_r (tup : expr) (e : expr) : bool :=
      match e with
      | `(denote_r %%R %%tup') := R = kc.table ∧ tup' = tup
      | _ := ff
      end in
  if k₁ = k₂ ∧ k₁ = kc.column
     ∧ assumptions.any (is_denote_r t)
     ∧ assumptions.any (is_denote_r t')
    then return (t, t')
    else failed
| _ := failed

private meta def mk_key_lhs (kc : key_constraint) (t t' : expr)
  : tactic (list expr) :=
  monad.mapm to_expr
             [ ``(denoteProj %%kc.column %%t ≃ denoteProj %%kc.column %%t')
             , ``(denote_r %%kc.table %%t)
             , ``(denote_r %%kc.table %%t')
             ]

private meta def mk_key_rhs (kc : key_constraint) (t t' : expr)
  : tactic (list expr) :=
  monad.mapm to_expr [``(%%t≃%%t'), ``(denote_r %%kc.table %%t)]

meta definition canonize : tactic unit :=
  let rewrite_constraint_occurence (kc : key_constraint) (e : expr) : tactic unit := do
    repr ← expr_to_canonize_term_repr e,
    match repr with
    | canonize_term_repr.sig body lconsts := do
      body_terms ← product_to_repr body,
      (t, t') ← list.foldr (<|>) failed
                $ list.map (rw_kc_in_prod_repr kc body_terms) body_terms,
      key_terms ← mk_key_lhs kc t t',
      let non_key_terms := body_terms.remove_first_of_each key_terms,
      let body' := key_terms ++ non_key_terms,
      rewritten_key_terms ← mk_key_rhs kc t t',
      let rewritten_body := rewritten_key_terms ++ non_key_terms,
      intermediate_body_expr ← repr_to_product body',
      rewritten_body_expr ← repr_to_product rewritten_body,
      intermediate_sigma_repr ← closed_sigma_repr_to_sigma_repr intermediate_body_expr lconsts,
      rewritten_sigma_repr ← closed_sigma_repr_to_sigma_repr rewritten_body_expr lconsts,
      intermediate_expr ← sigma_repr_to_sigma_expr intermediate_sigma_repr,
      rewritten_expr ← sigma_repr_to_sigma_expr rewritten_sigma_repr,
      eq_lemma ← tactic.to_expr ``(%%e = %%rewritten_expr),
      lemma_name ← tactic.mk_fresh_name,
      tactic.assert lemma_name eq_lemma,
      to_expr ``(@eq.trans _ %%e %%intermediate_expr %%rewritten_expr) >>= apply,
      repeat_n lconsts.length `[apply congr_arg usr.sig, funext], ac_refl,
      repeat_n lconsts.length `[apply congr_arg usr.sig, funext],
      to_expr ``(isKey_times_const %%kc.column %%kc.table %%kc.name) >>= rewrite_target,
      ac_refl,
      eq_lemma_name ← tactic.resolve_name lemma_name >>= tactic.to_expr,
      tactic.rewrite_target eq_lemma_name,
      tactic.clear eq_lemma_name
    | canonize_term_repr.prod terms := do
      (t, t') ← list.foldr (<|>) failed
                $ list.map (rw_kc_in_prod_repr kc terms) terms,
      key_terms ← mk_key_lhs kc t t',
      let non_key_terms := terms.remove_first_of_each key_terms,
      let body' := terms ++ non_key_terms,
      rewritten_key_terms ← mk_key_rhs kc t t',
      let rewritten_body := rewritten_key_terms ++ non_key_terms,
      intermediate_expr ← repr_to_product body',
      rewritten_expr ← repr_to_product rewritten_body,
      eq_lemma ← tactic.to_expr ``(%%e = %%rewritten_expr),
      lemma_name ← tactic.mk_fresh_name,
      tactic.assert lemma_name eq_lemma,
      to_expr ``(@eq.trans _ %%e %%intermediate_expr %%rewritten_expr) >>= apply,
      ac_refl,
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