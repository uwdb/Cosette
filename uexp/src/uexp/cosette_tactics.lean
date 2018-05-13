import system.io
import .u_semiring
import .cosette_lemmas

open nat io
open list io

section cosette_tactics

def list.remove_first_of_each {α : Type} [decidable_eq α]
  : list α → list α → list α
| xs [] := xs
| [] ys := []
| (x::xs) (y::ys) := if x = y
                       then list.remove_first_of_each xs ys
                       else x :: list.remove_first_of_each xs (y::ys)

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

meta def get_lhs_expr1 : tactic expr :=
tactic.target >>= λ e,
match e with
| `(%%a * _ * _ = _) := return a
| _ := tactic.failed
end

-- assuming lhs is in the form of a*b*c
meta def get_lhs_repr1 : tactic (list expr) :=
tactic.target >>= λ e,
match e with
| `(%%a * _ * _ = %%_) := ra_product_to_repr a
| _ := tactic.failed
end

meta def get_lhs_expr2 : tactic expr :=
tactic.target >>= λ e,
match e with
| `(_ * %%a * _ = _) := return a
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

/- suppose i > j -/
meta def forward_i_to_j (target: tactic expr) (i j: nat): tactic unit :=
    let loop : nat → tactic unit → tactic unit := 
        λ iter_num next_iter, do
        next_iter,
        ex ← target,
        repr ← product_to_repr ex,
        swap_element_forward (i - iter_num -1) repr
    in nat.repeat loop (i - j) $ return ()

meta def forward_i_to_j_lhs (i : nat) (j: nat) : tactic unit :=
    forward_i_to_j get_lhs_expr1 i j

/- the first nat is the size of body, the second nat is iteration -/
meta def repeat_if_progress (f: ℕ → ℕ → (tactic ℕ)) : 
ℕ → ℕ → (tactic ℕ) 
| (s) 0 := return 0         
| (s) (nat.succ n) := do 
    s' ← f s (s - n - 1), 
    repeat_if_progress s' n

meta structure usr_sigma_repr :=
(var_schemas : list expr) (body : expr)

meta instance sigma_repr_format : has_to_format usr_sigma_repr :=
  ⟨λ sig, format.cbrace $ "var_schemas := " ++ to_fmt sig.var_schemas ++ "," ++
                         " body := " ++ to_fmt sig.body⟩

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

meta def sigma_repr_to_closed_body_expr : usr_sigma_repr → tactic (expr × list name)
| ⟨schemas, body⟩ := do
  lconsts ← list.mfoldr (λ (t : expr) (lconsts : list (expr × name)),
                           do n ← tactic.mk_fresh_name,
                              ty ← tactic.to_expr ``(Tuple %%t),
                              let local_const := expr.local_const n n binder_info.default ty,
                              return $ (local_const, n) :: lconsts)
                        []
                        $ list.reverse schemas,
  let ⟨lconsts', names⟩ := lconsts.unzip,
  return (expr.instantiate_vars body lconsts', names)

meta def sigma_repr_to_closed_body_expr' : usr_sigma_repr → tactic (expr × list (expr × name))
| ⟨schemas, body⟩ := do
  lconsts ← list.mfoldr (λ (t : expr) (lconsts : list (expr × name)),
                           do n ← tactic.mk_fresh_name,
                              ty ← tactic.to_expr ``(Tuple %%t),
                              let local_const := expr.local_const n n binder_info.default ty,
                              return $ (local_const, n) :: lconsts)
                        []
                        $ list.reverse schemas,
  let ⟨lconsts', names⟩ := lconsts.unzip,
  return (expr.instantiate_vars body lconsts', lconsts)

private meta def get_types_of_local_consts
  (ns : list name) : expr → list (nat × expr)
| (expr.app f x) := list.union (get_types_of_local_consts f) $
                               get_types_of_local_consts x
| (expr.lam n bi ty body) := list.union (get_types_of_local_consts ty) $
                                        get_types_of_local_consts body
| (expr.pi n bi ty body) := list.union (get_types_of_local_consts ty) $
                                       get_types_of_local_consts body
| (expr.elet n ty val body) := list.union (get_types_of_local_consts ty) $
                               list.union (get_types_of_local_consts val) $
                                          get_types_of_local_consts body
| (expr.local_const n _ _ ty) :=
  let idx : option nat :=
      list.rec none (λ n' ns res, if n = n' then some 0 else nat.succ <$> res) ns
  in match idx with
  | some i := [(i, ty)]
  | none := []
  end
| _ := []

meta def closed_sigma_repr_to_sigma_repr (body : expr) (names : list name)
  : tactic usr_sigma_repr := do
  schemas ← monad.sequence
            $ list.map (λ p : nat × expr,
                          match p with
                          | (_, `(Tuple %%s)) := return s
                          | _ := tactic.failed
                          end)
            $ list.qsort (λ x y : nat × expr, x.fst ≥ y.fst)
            $ get_types_of_local_consts names body,
  return $ usr_sigma_repr.mk schemas
         $ expr.abstract_locals body
         $ list.reverse names

meta def forward_i_to_j_in_sig (target: tactic expr) (i: nat) (j: nat) : tactic unit := do 
  ex ← target,
  lr ← return $ sigma_expr_to_sigma_repr ex,
  match lr with 
  |⟨xs, body⟩ := do
    le ← product_to_repr body,
    le' ← move_nth_to_kth i j le,    
    body' ← repr_to_product le',
    origin ← target,
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

meta def forward_i_to_j_in_sig_lhs (i: nat) (j: nat) : tactic unit :=
    forward_i_to_j_in_sig get_lhs i j

meta def sig_body_size (target: tactic expr) : tactic ℕ := do 
  ex ← target,
  lr ← return $ sigma_expr_to_sigma_repr ex,
  match lr with 
  |⟨xs, body⟩ := do 
    le ← product_to_repr body,
    return $ list.length le
  end 

meta def split_pairs : tactic unit := do 
    `[repeat {rw eq_pair <|> rw eq_pair'}, try {dsimp}]

meta def get_table_and_column (e : expr) : option (expr × expr) :=
  let fn := expr.get_app_fn e in do
    match fn with
    | (expr.const n _) :=
      if n = `isKey
        then match list.reverse $ expr.get_app_args e with
             | (rel::col::_) := some (rel, col)
             | _ := none
             end
        else none
    | _ := none
    end

meta structure key_constraint :=
(name : expr) (table : expr) (column : expr)

meta instance key_constraint_to_format : has_to_format key_constraint :=
  ⟨λ kc, format.cbrace $ "name := " ++ to_fmt kc.name ++ "," ++
                         " table := " ++ to_fmt kc.table ++ "," ++
                         " column := " ++ to_fmt kc.column⟩

meta def find_keys : tactic (list key_constraint) := do
  hyps ← tactic.local_context, 
  hyp_types ← monad.mapm tactic.infer_type hyps,
  return $ list.filter_map
              (λ (name_and_type : expr × expr),
                  match name_and_type with
                  | (key_name, key_type) :=
                    match get_table_and_column key_type with
                    | some (rel, col) := some $ key_constraint.mk key_name rel col
                    | none := none
                    end
                  end)
         $ list.zip hyps hyp_types

meta def unfold_all_denotations := `[
    repeat { unfold denoteSQL
            <|> unfold denotePred
            <|> unfold denoteProj
            <|> unfold denoteExpr
            <|> unfold groupBy 
            <|> unfold combineGroupByProj
            <|> unfold pair
            <|> unfold plainGroupByProj
            <|> unfold aggregatorGroupByProj}
]

meta def remove_all_unit : tactic unit :=
    `[repeat {rw time_one <|> rw time_one'}]

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
  equality_lemma ← tactic.to_expr ``(%%normal_expr = %%swapped_expr),
  eq_lemma_name ← tactic.mk_fresh_name,
  tactic.assert eq_lemma_name equality_lemma,
  repeat_n i $ tactic.applyc `congr_arg >> tactic.funext,
  tactic.applyc `sig_commute,
  eq_lemma ← tactic.resolve_name eq_lemma_name >>= tactic.to_expr,
  tactic.rewrite_target eq_lemma,
  tactic.clear eq_lemma

meta def move_sig_once (target: tactic expr) (i: nat) : tactic unit := do
  ex ← target,
  lr ← return $ sigma_expr_to_sigma_repr ex,
  swap_ith_sigma_forward i lr

meta def move_sig_to_front (target: tactic expr) (i : nat) : tactic unit :=
  let loop : ℕ → tactic unit → tactic unit :=
      λ iter_num next_iter, do
        ex ← target,
        lr ← return $ sigma_expr_to_sigma_repr ex,
        swap_ith_sigma_forward iter_num lr,
        next_iter
  in nat.repeat loop i $ return ()

--move back i to j
meta def move_sig_back (target: tactic expr) (i: nat) (j: nat) :=
  let loop: nat → tactic unit → tactic unit :=
    λ num next, do 
      next, 
      move_sig_once target (i+num)
  in nat.repeat loop (j-i) $ return ()

-- a single step removal
meta def remove_sig_step (target: tactic expr): tactic unit := do
  ex ← target,
  lr ← return $ sigma_expr_to_sigma_repr ex,
  match lr with 
  | ⟨xs, body⟩ := do 
    le ← ra_product_to_repr body,
    match list.head le with
    | `(%%a ≃ %%b) := 
      match a, b with
      | (expr.var n), e := do 
        let l := (list.length xs),
        move_sig_back target (l - 1 - n) (l - 1),
        ex' ← target,
        lr' ← return $ sigma_expr_to_sigma_repr ex',
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
        move_sig_back target (l - 1 - n) (l - 1),
        ex' ← target,
        lr' ← return $ sigma_expr_to_sigma_repr ex',
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

meta def split_p (ex : expr) : tactic (list expr) :=
match ex with
| `(%%a ≃ %%b) := 
  match a, b with
    | `((%%a1, %%a2)) , `((%%b1, %%b2)) := do
      x1 ← tactic.to_expr ``((%%a).1 ≃ (%%b).1),
      x2 ← tactic.to_expr ``((%%a).2 ≃ (%%b).2),
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
      x1 ← tactic.to_expr ``((%%a).1 ≃ %%c),
      x2 ← tactic.to_expr ``((%%a).2 ≃ %%d),
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
      ty ← tactic.infer_type b,
      let args := expr.get_app_args ty,
      r ← match args.nth 0 with
      | some `(%%r ++ _) := return r
      | _ := failure
      end,
      ty2 ← tactic.to_expr ``((@cast %%ty (Tuple %%r × Tuple %%r) (by tactic.reflexivity) (%%b)).1),
      x1 ← tactic.to_expr ``(%%c ≃ (%%b).1),
      x2 ← tactic.to_expr ``(%%d ≃ (%%b).2),
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
meta def normalize_sig_body (target: tactic expr) : tactic unit := do
  ex ← target,
  lr ← return $ sigma_expr_to_sigma_repr ex,
  lr_body_closed ← sigma_repr_to_closed_body_expr lr,
  match lr_body_closed with 
  | ⟨body, names⟩ := do
    le ← product_to_repr body,
    s1 ← split_pair_in_repr le, 
    body' ← repr_to_product s1,
    origin ← target,
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

meta def remove_dup_sigs (target: tactic expr) : tactic unit := do 
  -- this is a workround, this unnest 3 levels of pair
  -- repeat_n 3 $ normalize_sig_body_lhs >> try dsimp_target, 
  repeat_n 3 $ normalize_sig_body target,
  s ← sig_body_size target,
  final ← let loop : ℕ → ℕ → (tactic ℕ) := λ s n, do
    forward_i_to_j_in_sig target n 0,
    remove_sig_step target,
    sig_body_size target
  in repeat_if_progress loop s s,
  return ()

end cosette_tactics