import .sql
import .tactics
import .u_semiring
import .extra_constants
import .cosette_tactics

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
    | _ := tactic.fail "no squash to match"
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
    lemma_name ← tactic.mk_fresh_name,
    tactic.assert lemma_name eq_lemma,
    tactic.focus1 $ solve_lem (list.length lsr.var_schemas), 
    eq_lemma_name ← tactic.resolve_name lemma_name >>= tactic.to_expr,
    tactic.rewrite_target eq_lemma_name,
    tactic.clear eq_lemma_name

meta def unify_binder_i_j (i j: nat) : tactic unit := do
    lhs ← get_lhs,
    le ← inside_squash lhs,
    ⟨body, names⟩ ← return $ sigma_expr_to_sigma_repr le,
    tactic.trace body,
    -- distribute + in body
    return ()

example {Γ s : Schema} (a : relation s) (g : Tuple Γ) (t : Tuple s):
∥(∑ (t₁ t₂ : Tuple s), denote_r a t₁ * (denote_r a t₂ * (t≃t₁)))∥ =
    ∥(∑ (t_1 : Tuple s), denote_r a t_1 * (t≃t_1))∥ :=
begin
    add_lem 0 1,
    have h: ∥(∑ (t₁ t₂ : Tuple s), denote_r a t₁ * (denote_r a t₂ * (t≃t₁)))∥ = 
            ∥(∑ (t₁ t₂ : Tuple s), ((t₁ ≃ t₂) + usr.not (t₁ ≃ t₂))*(denote_r a t₁ * (denote_r a t₂ * (t≃t₁))))∥, 
    focus {
        apply congr_arg,
        apply congr_arg,
        funext,
        apply congr_arg,
        funext,
        rw eq_lem,
        remove_all_unit,
    },
    rw h,
    clear h,
    have h: ∥(∑ (t₁ t₂ : Tuple s), ((t₁ ≃ t₂) + usr.not (t₁ ≃ t₂))*(denote_r a t₁ * (denote_r a t₂ * (t≃t₁))))∥ = 
     ∥(∑ (t₁ t₂ : Tuple s), (t₁ ≃ t₂) *(denote_r a t₁ * (denote_r a t₂ * (t≃t₁))) + usr.not (t₁ ≃ t₂)*(denote_r a t₁ * (denote_r a t₂ * (t≃t₁))))∥,
     focus {
        apply congr_arg,
        apply congr_arg,
        funext,
        apply congr_arg,
        funext,
        rw time_distrib_r,
    },
    rw h,
    clear h,
    have h : ∥(∑ (t₁ t₂ : Tuple s), (t₁≃t₂) * (denote_r a t₁ * (denote_r a t₂ * (t≃t₁))) + usr.not (t₁≃t₂) * (denote_r a t₁ * (denote_r a t₂ * (t≃t₁))))∥ = 
    ∥(∑ (t₁ t₂ : Tuple s), (t₁≃t₂) * (denote_r a t₁ * (denote_r a t₂ * (t≃t₁)))) + (∑ (t₁ t₂ : Tuple s), usr.not (t₁≃t₂) * (denote_r a t₁ * (denote_r a t₂ * (t≃t₁))))∥,
    focus {
        rw sig2_distr_plus,
    },
    rw h,
    clear h,
    sorry
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
    sorry,
end