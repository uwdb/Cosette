import .sql
import .tactics
import .u_semiring
import .extra_constants
import .cosette_tactics
import .TDP

-- assume there is only sig inside squash
lemma sig2_distr_plus {s₁ s₂ : Schema} {f₁ f₂ : Tuple s₁ → Tuple s₂  → usr} :
    (∑ t₁ t₂ , f₁ t₁ t₂ + f₂ t₁ t₂) = (∑ t₁ t₂ , f₁ t₁ t₂) + (∑ t₁ t₂, f₂ t₁ t₂) :=
begin 
    rw ← sig_distr_plus,
    apply congr_arg,
    funext,
    apply sig_distr_plus,
end

meta def inside_squash (e: expr) : tactic expr := 
    match e with 
    | `(usr.squash %%d) := tactic.to_expr ``(%%d)
    | _ := do tactic.fail "no squash to match"
    end 

meta def add_sqush (e: expr) : tactic expr :=
    tactic.to_expr ``(usr.squash %%e)

meta def solve_lem (n: nat) : tactic unit := do 
    repeat_n n (tactic.applyc `congr_arg >> tactic.funext), 
    `[rw eq_lem],
    remove_all_unit,
    tactic.try tactic.ac_refl

-- add lem of ith binder and jth binder
meta def add_lem (i j: nat) : tactic unit := do 
    lhs ← get_lhs,
    le ← inside_squash lhs, -- orginal sig
    lsr ← return $ sigma_expr_to_sigma_repr le,
    ⟨body, binders⟩ ← sigma_repr_to_closed_body_expr' lsr,
    binders' ← return $ list.reverse binders,
    let (exprs, names) := binders'.unzip, 
    let t₁ := list.ilast $ list.take (i+1) exprs,
    let t₂ := list.ilast $ list.take (j+1) exprs,
    lem ← tactic.to_expr ``((%%t₁ ≃ %%t₂) + usr.not (%%t₁ ≃ %%t₂)),
    lr ← product_to_repr body,
    new_lr ← return $ lem :: lr,
    new_body ← repr_to_product new_lr,
    abstracted ← return $ expr.abstract_locals new_body names, 
    new ← sigma_repr_to_sigma_expr ⟨lsr.var_schemas, abstracted⟩, 
    eq_lemma ← tactic.to_expr ``(%%le = %%new),
    ng_before ← list.length <$> tactic.get_goals,
    lemma_name ← tactic.mk_fresh_name,
    tactic.assert lemma_name eq_lemma,
    tactic.focus1 $ solve_lem (list.length lsr.var_schemas), 
    ng_after ← list.length <$> tactic.get_goals,
    if ng_after > ng_before then tactic.fail "add_lem fail"
    else (do
    eq_lemma_name ← tactic.resolve_name lemma_name >>= tactic.to_expr,
    tactic.rewrite_target eq_lemma_name,
    tactic.clear eq_lemma_name)

meta def is_plus : expr → bool 
| `(_ + _) := tt
| _ := ff

meta def solve_split_ins (n:nat) : tactic unit := do  
    repeat_n n (tactic.applyc `congr_arg >> tactic.funext), 
    `[rw time_distrib_r]

/- split + introduced by lem -/
meta def split_lem : tactic unit := do 
    lhs ← get_lhs,
    le ← inside_squash lhs, -- orginal sig
    lsr ← return $ sigma_expr_to_sigma_repr le,
    ⟨body, binders⟩ ← sigma_repr_to_closed_body_expr' lsr,
    binders' ← return $ list.reverse binders,
    let (exprs, names) := binders'.unzip,
    lr ← product_to_repr body,
    if not $ is_plus (list.head lr) then return () --do nothing
    else do
    (a, b) ← match (list.head lr) with 
                | `(%%a + %%b) := return (a, b)
                | _ := tactic.fail "spli_lem fail"
                end,
    b1 ← repr_to_product (a::(list.tail lr)),
    b2 ← repr_to_product (b::(list.tail lr)),
    new ← tactic.to_expr ``(%%b1 + %%b2),
    abstracted ← return $ expr.abstract_locals new names,
    new_ex ← sigma_repr_to_sigma_expr ⟨lsr.var_schemas, abstracted⟩,
    eq_lemma ← tactic.to_expr ``(%%le = %%new_ex),
    ng_before ← list.length <$> tactic.get_goals,
    lemma_name ← tactic.mk_fresh_name,
    tactic.assert lemma_name eq_lemma,
    tactic.focus1 $ solve_split_ins (list.length lsr.var_schemas), 
    ng_after ← list.length <$> tactic.get_goals,
    if ng_after > ng_before then tactic.fail "add_lem fail"
    else (do
    eq_lemma_name ← tactic.resolve_name lemma_name >>= tactic.to_expr,
    tactic.rewrite_target eq_lemma_name,
    tactic.clear eq_lemma_name)

meta def solve_distr_lem (n:nat) : tactic unit := do  
    repeat_n (n - 1) `[rw ← sig_distr_plus, apply congr_arg, funext], 
    tactic.applyc `sig_distr_plus

meta def distr_lem : tactic unit := do 
    lhs ← get_lhs,
    le ← inside_squash lhs, -- orginal sig
    lsr ← return $ sigma_expr_to_sigma_repr le,
    ⟨body, binders⟩ ← sigma_repr_to_closed_body_expr' lsr,
    binders' ← return $ list.reverse binders,
    let (exprs, names) := binders'.unzip,
    if not $ is_plus body then return () --do nothing
    else do
    (a, b) ← match body with 
                | `(%%a + %%b) := return (a, b)
                | _ := tactic.fail "spli_lem fail"
                end,
    a1 ← return $ expr.abstract_locals a names,
    a2 ← return $ expr.abstract_locals b names,
    new1 ← sigma_repr_to_sigma_expr ⟨lsr.var_schemas, a1⟩,
    new2 ← sigma_repr_to_sigma_expr ⟨lsr.var_schemas, a2⟩,
    eq_lemma ← tactic.to_expr ``(%%le = %%new1 + %%new2),
    ng_before ← list.length <$> tactic.get_goals,
    lemma_name ← tactic.mk_fresh_name,
    tactic.assert lemma_name eq_lemma,
    tactic.focus1 $ solve_distr_lem (list.length lsr.var_schemas), 
    ng_after ← list.length <$> tactic.get_goals,
    if ng_after > ng_before then tactic.fail "add_lem fail"
    else (do
    eq_lemma_name ← tactic.resolve_name lemma_name >>= tactic.to_expr,
    tactic.rewrite_target eq_lemma_name,
    tactic.clear eq_lemma_name)

-- get a from ∥ a + b ∥ 
meta def first_in_squash (scope: tactic expr) : tactic expr := do
    ex ← scope,
    match ex with 
     | `(usr.squash (%%a + %%b)) := return a
     | _ := tactic.fail "no squashed union in scope"
    end

meta def snd_in_squash (scope: tactic expr) : tactic expr := do
    ex ← scope,
    match ex with 
     | `(usr.squash (%%a + %%b)) := return b
     | _ := tactic.fail "no squashed union in scope"
    end

meta def unwrap_squash (scope: tactic expr) : tactic expr := do
    ex ← scope,
    match ex with 
    | `(usr.squash %%a) := return a
    | _ := tactic.fail "no squash to unwrap"
    end

meta def is_one (e:expr) :bool :=
match e with 
| `(has_one.one usr) :=  true
| _ := false
end

meta def unit_ueq_to_one (lp: list expr) : tactic (list expr) := do 
    let f : expr → tactic expr := λ e,
    match e with 
    | `(%%a ≃ %%b) := if a = b then tactic.to_expr ``(has_one.one usr)
                      else return e
    | ex := return ex
    end 
    in do l ← monad.mapm f lp,
        return $ list.filter (λ x, ¬ (is_one x)) l

meta def prove_in_sig (n: nat) (solver: tactic unit ) : tactic unit := do
    repeat_n n $ tactic.applyc `congr_arg >> tactic.funext,
    solver

/- simplification inside sigma 
target: expr getter
trans: transformation on AST
solver: proof for transformation
-/
meta def simplify_in_sig (target: tactic expr) (trans: list expr → tactic (list expr)) (solver: tactic unit): tactic unit := do 
    old ← target,
    lsr ← return $ sigma_expr_to_sigma_repr old,
    ⟨body, binders⟩ ← sigma_repr_to_closed_body_expr' lsr,
    binders' ← return $ list.reverse binders,
    let (exprs, names) := binders'.unzip,
    lr ← product_to_repr body,
    new_lr ← trans lr,
    new_body ← repr_to_product new_lr,
    abstracted ← return $ expr.abstract_locals new_body names, 
    new ← sigma_repr_to_sigma_expr ⟨lsr.var_schemas, abstracted⟩, 
    eq_lemma ← tactic.to_expr ``(%%old = %%new),
    ng_before ← list.length <$> tactic.get_goals,
    lemma_name ← tactic.mk_fresh_name,
    tactic.assert lemma_name eq_lemma,
    tactic.focus1 $ prove_in_sig (list.length names) solver, 
    ng_after ← list.length <$> tactic.get_goals,
    if ng_after > ng_before
    then tactic.fail "simplify_inside_sig fail"
    else (do
    eq_lemma_name ← tactic.resolve_name lemma_name >>= tactic.to_expr,
    tactic.rewrite_target eq_lemma_name,
    tactic.clear eq_lemma_name)


meta def unify_binder_i_j (i j: nat) : tactic unit := do
    add_lem i j, -- add lem of i-th and j-th binders
    split_lem, -- split plus inside sig
    distr_lem, -- distribute plus over sig
    -- remove dup sig on one side
    remove_dup_sigs (first_in_squash get_lhs),
    `[rw plus_comm],
    remove_dup_sigs (first_in_squash get_lhs),
    -- simplify after remove_dup_sigs    
    simplify_in_sig (first_in_squash get_lhs) unit_ueq_to_one `[repeat {rw eq_unit}, remove_all_unit],
    `[rw plus_comm],
    simplify_in_sig (first_in_squash get_lhs) unit_ueq_to_one `[repeat {rw eq_unit}, remove_all_unit],
    -- remove redundant relation 
    -- factorize
    -- reduce done
    return ()

example {Γ s : Schema} (a : relation s) (g : Tuple Γ) (t : Tuple s):
∥(∑ (t₁ t₂ : Tuple s), denote_r a t₁ * (denote_r a t₂ * (t≃t₁)))∥ =
    ∥(∑ (t_1 : Tuple s), denote_r a t_1 * (t≃t_1))∥ :=
begin
    unify_binder_i_j 0 1,
    rw dup_in_squashed_union,
    have h: (∑ (x : Tuple s), denote_r a x * (denote_r a t * usr.not (t≃x))) = denote_r a t * (∑ (x : Tuple s), denote_r a x * usr.not (t≃x)),
    focus{
        simp,
        TDP,
    },
    rewrite h,
    clear h,
    rw squash_union_factor,
    apply ueq_symm,
    remove_dup_sigs $ unwrap_squash get_lhs,
    refl,
end

example {Γ s : Schema} {ty0 ty1 : datatype} (a : relation s) (c0 : Column ty0 s)
(c1 : Column ty1 s)
(g : Tuple Γ)
(t : Tuple (tree.leaf ty0 ++ tree.leaf ty1)):
∥(∑ (t₁ t₂ : Tuple s),
         (denoteProj c0 t₁≃denoteProj c0 t₂) *
           (denote_r a t₁ *
              (denote_r a t₂ *
                 ((denoteProj c1 t₁≃denoteProj c1 t₂) * (t≃(denoteProj c0 t₂, denoteProj c1 t₂))))))∥ =
    ∥(∑ (t_1 : Tuple s), denote_r a t_1 * (t≃(denoteProj c0 t_1, denoteProj c1 t_1)))∥ :=
begin
    unify_binder_i_j 0 1,
    sorry, 
end

example {Γ s1 s2 : Schema} (a : SQL Γ s1) (b : SQL Γ s2)
(ty0 ty1 : datatype) (x : Column ty0 s1) (ya : Column ty1 s1)
(yb : Column ty1 s2) (g : Tuple Γ) (t : Tuple (tree.leaf ty0)):
∥(∑ (t₁ : Tuple s1) (t₂ : Tuple s2),
         denoteSQL a g t₁ *
           (denoteSQL b g t₂ * ((t≃denoteProj x t₁) * (denoteProj ya t₁≃denoteProj yb t₂))))∥ 
=
∥(∑ (t₁ t₂ : Tuple s1) (t₂_1 : Tuple s2),
         (denoteProj ya t₁≃denoteProj yb t₂_1) *
           ((denoteProj x t₁≃denoteProj x t₂) *
              (denoteSQL a g t₁ * (denoteSQL b g t₂_1 * (denoteSQL a g t₂ * (t≃denoteProj x t₁))))))∥ :=
begin
    apply ueq_symm,
    unify_binder_i_j 0 1,
    sorry,
end