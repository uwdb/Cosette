import system.io
import .u_semiring
import .cosette_lemmas

open nat io
open list io

section cosette_tactics

def list.swap_ith_forward {α : Type} {f : Type → Type} [alternative f]
    : nat → list α → f (list α)
| 0 (x::y::zs) := pure $ y :: x :: zs
| (nat.succ n) (x::xs) := list.cons x <$> list.swap_ith_forward n xs
| _ _ := failure

lemma swap_gives_result_if_index_in_range {α : Type}
  : ∀ (ls : list α) i,
    i + 2 < list.length ls →
    { ls' : list α // list.swap_ith_forward i ls = some ls' } :=
begin
  intros ls i h,
  revert ls,
  induction i with j ih;
  intros; cases ls with x ys,
  { exfalso, cases h },
  { cases ys with y zs,
    { exfalso, cases h, cases h_a },
    { existsi (y :: x :: zs), refl } },
  { exfalso, cases h },
  { cases ih ys _ with ys' h',
    existsi x :: ys', unfold list.swap_ith_forward,
    rw h', refl,
    apply nat.lt_of_succ_lt_succ,
    assumption }
end

meta def expr.swap_free_vars (i : nat) (j : nat) : expr → expr
| (expr.var n) := if n = i
                    then expr.var j
                    else if n = j
                           then expr.var i
                           else expr.var n
| (expr.app f x) := expr.app (expr.swap_free_vars f) (expr.swap_free_vars x)
| (expr.lam n bi ty body) := let ty' := expr.swap_free_vars ty,
                                 body' := expr.swap_free_vars body
                             in expr.lam n bi ty' body'
| (expr.pi n bi ty body) := let ty' := expr.swap_free_vars ty,
                                body' := expr.swap_free_vars body
                            in expr.pi n bi ty' body'
| (expr.elet n ty val body) := let ty' := expr.swap_free_vars ty,
                                   val' := expr.swap_free_vars val,
                                   body' := expr.swap_free_vars body
                               in expr.elet n ty' val' body'
| ex := ex

--  substitute variable and also lift de bruijn index
meta def expr.subst_var (target: expr) : expr → expr := λ e, 
if e = target then (expr.var 0)
else 
match e with
| (expr.var n) := expr.var (n+1)
| (expr.app f x) := expr.app (expr.subst_var f) (expr.subst_var x)
| (expr.lam n bi ty body) := expr.lam n bi (expr.subst_var ty) (expr.subst_var body)
| (expr.pi n bi ty body) := expr.pi n bi (expr.subst_var ty) (expr.subst_var body)
| (expr.elet n ty val body) := let ty' := expr.subst_var ty,
                                   val' := expr.subst_var val,
                                   body' := expr.subst_var body
                               in expr.elet n ty' val' body'
| ex := ex
end

-- substitute variable without lift de bruijn index
meta def expr.subst_var' (target: expr) (replacement: expr) : expr → expr := λ e, 
if e = target then replacement
else 
match e with
| (expr.var n) := expr.var n
| (expr.app f x) := expr.app (expr.subst_var' f) (expr.subst_var' x)
| (expr.lam n bi ty body) := expr.lam n bi (expr.subst_var' ty) (expr.subst_var' body)
| (expr.pi n bi ty body) := expr.pi n bi (expr.subst_var' ty) (expr.subst_var' body)
| (expr.elet n ty val body) := let ty' := expr.subst_var' ty,
                                   val' := expr.subst_var' val,
                                   body' := expr.subst_var' body
                               in expr.elet n ty' val' body'
| ex := ex
end

def move_nth_to_kth {α : Type} {m : Type → Type} [alternative m] [monad m]
  (final initial : ℕ) (ls : list α) : m (list α) :=
  list.append (ls.take initial) <$>
    nat.repeat (λ n (ls' : m (list α)), ls' >>= list.swap_ith_forward (final - n - 1))
               (final - initial) (return $ ls.drop initial)

universes u v w
def congr_arg₂ {α : Sort u} {β : Sort v} {γ : Sort w}
  {a₁ a₂ : α} {b₁ b₂ : β} (f : α → β → γ)
  : a₁ = a₂ → b₁ = b₂ → f a₁ b₁ = f a₂ b₂ :=
begin
  intros,
  apply congr,
  { apply congr_arg, assumption },
  { assumption }
end

-- repeat tacitic t exactly n times
meta def repeat_n (n: nat) (t: tactic unit) : tactic unit :=
    nat.repeat (λ n next, t >> next) n $ return ()

-- check if an expr is in the list
meta def expr_in : expr →  list expr → bool :=
(λ e l, 
match l with
| [] := ff
| (h :: t) := if h=e then tt else (expr_in e t)
end)

meta def get_eq_sides : tactic (expr × expr) :=
tactic.target >>= λ e,
match e with
| `(%%a = %%b) := return (a, b)
| _ := tactic.failed
end

meta def get_lhs : tactic expr :=
prod.fst <$> get_eq_sides

meta def get_rhs : tactic expr :=
prod.snd <$> get_eq_sides

meta def solved_or_continue (next: tactic unit) : tactic unit := do
    tactic.try tactic.reflexivity,
    ok ← list.empty <$> tactic.get_goals,
    if ok then return ()
    else next

meta def print_goals : tactic unit :=  do 
    goals ← tactic.get_goals,
    tactic.trace goals

meta def repeat_or_sol (f: ℕ → tactic unit) : 
ℕ → tactic unit 
| 0 := (f 0)         
| (nat.succ n) := do 
    repeat_or_sol n, 
    ok ← list.empty <$> tactic.get_goals,
    if ok then return ()
    else (f n)    

meta def beta_reduction (e: expr): tactic unit := do 
    reduced ← tactic.head_beta e,
    n ← tactic.mk_fresh_name,
    tactic.to_expr ``(%%e=%%reduced) >>= tactic.assert n,
    tactic.reflexivity,
    eq_lemma ← tactic.resolve_name n >>= tactic.to_expr,
    tactic.rewrite_target eq_lemma,
    tactic.clear eq_lemma

-- this assume that expr is a right associative product
private meta def ra_product_to_repr' : expr → list expr
| `(%%a * %%b) := a :: ra_product_to_repr' b
| e := [e] 

-- this assume that expr is a right associative product
meta def ra_product_to_repr (e: expr) : tactic (list expr) :=
return $ ra_product_to_repr' e 

meta def repr_to_product : list expr → tactic expr
| [x] := return x
| (h::t) :=  do te ← repr_to_product t,
                tactic.to_expr ``(%%h * %%te)
| [] := tactic.to_expr ``(usr.one)

-- this doesn't assume any form of the product expr
private meta def product_to_repr' : expr → list expr
| `(%%a * %%b) := (product_to_repr' a) ++ (product_to_repr' b)
| x := [x]

meta def product_to_repr (e: expr) : tactic (list expr) :=
    return $ product_to_repr' e 

meta def is_ueq : expr → bool
| `(_ ≃ _) := tt
| _ := ff

meta def get_ueqs (l: list expr) : list expr :=
    list.filter (λ e, is_ueq e = tt) l 

meta def get_non_ueqs (l: list expr) : list expr :=
    list.filter (λ e, is_ueq e = ff) l 

-- assuming lhs is in the form of a*b*c
meta def get_lhs_repr1 : tactic (list expr) :=
tactic.target >>= λ e,
match e with
| `(%%a * _ * _ = %%_) := ra_product_to_repr a
| _ := tactic.failed
end

-- assuming lhs is in the form of a*b*c
meta def get_lhs_repr2 : tactic (list expr) :=
tactic.target >>= λ e,
match e with
| `(_ * %%a * _ = _) := ra_product_to_repr a
| _ := tactic.failed
end

-- assuming lhs is in the form of a*b*c
meta def get_lhs_repr3 : tactic (list expr) :=
tactic.target >>= λ e,
match e with
| `(_ * _ * %%a = _) := ra_product_to_repr a
| _ := tactic.failed
end

meta def get_lhs_expr3 : tactic expr :=
tactic.target >>= λ e,
match e with
| `(_ * _ * %%a = _) := return a
| _ := tactic.failed
end

-- swap i-th element in a product forward
meta def swap_element_forward (i: nat) (l: list expr) : tactic unit :=
    do 
    swapped_list ← list.swap_ith_forward i l,
    origin_expr ← repr_to_product l,
    swapped_expr ← repr_to_product swapped_list,
    eq_lemma ← tactic.to_expr ``(%%origin_expr = %%swapped_expr),
    eq_lemma_name ← tactic.mk_fresh_name,
    tactic.assert eq_lemma_name eq_lemma,
    repeat_n i $ (tactic.to_expr ``(congr_arg (has_mul.mul _)) >>= tactic.apply >> return ()),
    tactic.applyc `prod_symm_assoc <|> tactic.applyc `mul_comm,
    eq_lemma ← tactic.resolve_name eq_lemma_name >>= tactic.to_expr,
    tactic.rewrite_target eq_lemma,
    tactic.clear eq_lemma

-- suppose i > j
meta def forward_i_to_j (i : nat) (j: nat) : tactic unit :=
    let loop : nat → tactic unit → tactic unit := 
        λ iter_num next_iter, do
        next_iter,
        repr ← get_lhs_repr1,
        swap_element_forward (i - iter_num -1) repr
    in nat.repeat loop (i - j) $ return ()

-- the first nat is the size of body, the second nat is iteration
meta def repeat_if_progress (f: ℕ → ℕ → (tactic ℕ)) : 
ℕ → ℕ → (tactic ℕ) 
| (s) 0 := return 0         
| (s) (nat.succ n) := do 
    s' ← f s (s - n - 1), 
    repeat_if_progress s' n

meta structure usr_sigma_repr :=
(var_schemas : list expr) (body : expr)

meta def sigma_expr_to_sigma_repr : expr → usr_sigma_repr
| `(usr.sig (λ t : Tuple %%s, %%a)) :=
  match sigma_expr_to_sigma_repr a with
  | ⟨var_schemas, inner⟩ := ⟨s :: var_schemas, inner⟩
  end
| e := ⟨[], e⟩

-- This needs to be a tactic so we can resolve `Tuple and `usr.sig
meta def sigma_repr_to_sigma_expr : usr_sigma_repr → tactic expr
| ⟨[], body⟩ := return body
| ⟨t::ts, body⟩ := do
  body' ← sigma_repr_to_sigma_expr ⟨ts, body⟩,
  n ← tactic.get_unused_name `x,
  ty ← tactic.to_expr ``(Tuple %%t),
  let lam : expr := expr.lam n binder_info.default ty body',
  tactic.to_expr ``(usr.sig %%lam)

meta def get_lhs_sigma_repr : tactic usr_sigma_repr :=
tactic.target >>= λ e,
match e with
| `(%%a = %%b) := return $ sigma_expr_to_sigma_repr a
| _ := tactic.failed
end

meta def forward_i_to_j_in_sig (i: nat) (j: nat) : tactic unit := do 
  lr ← get_lhs_sigma_repr,
  match lr with 
  |⟨xs, body⟩ := do
    le ← product_to_repr body,
    le' ← move_nth_to_kth i j le,    
    body' ← repr_to_product le',
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

meta def sig_body_size : tactic ℕ := do 
  lr ← get_lhs_sigma_repr,
  match lr with 
  |⟨xs, body⟩ := do 
    le ← product_to_repr body,
    return $ list.length le
  end 

meta def split_pairs : tactic unit := do 
    `[repeat {rw eq_pair <|> rw eq_pair'}, try {dsimp}]

meta def is_key_type (e : expr) : bool :=
    do let fn := expr.get_app_fn e,
    match fn with
    | (expr.const n _) := n = `isKey
    | _ := bool.ff
    end

meta def find_keys : tactic (list expr) :=
    do hyps ← tactic.local_context, 
       hyp_types ← monad.mapm tactic.infer_type hyps,
       let pairs := list.filter (fun (p: expr × expr), is_key_type p.snd = bool.tt) (list.zip hyps hyp_types),
       return $ (list.unzip pairs).fst

meta def try_me : tactic unit := do 
    ks ← find_keys,
    tactic.trace ks

-- Keep applying g until it fails
meta def repeat_with_state {α : Type} {f : Type → Type} [alternative f] [monad f]
  (g : α → f α) : α → f α
  := λ a₀, (g a₀ >>= repeat_with_state) <|> return a₀

end cosette_tactics