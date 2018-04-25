import .u_semiring
import .cosette_tactics

open tactic

private meta def walk_product : expr → tactic unit
| `(%%a * %%b) := walk_product a >> walk_product b
| `(%%t₁ ≃ %%t₂) :=
  if t₁ > t₂
    then return ()
    else do h ← to_expr ``(eq_symm %%t₁ %%t₂),
            try $ rewrite_target h,
            -- tactic.trace $ "rewriting " ++ h.to_string,
            return ()
| _ := return ()

-- walk the product and normalize equal pred
meta def unify_eq : tactic unit := do
  t ← tactic.target,
  match t with
  | `(%%a = %%b) := walk_product a >> walk_product b
  | _ := failed
  end

meta def split_mult : expr → tactic (list expr)
| `(eq %%a _) := split_mult a 
| `(%%a * %%b) := 
    do lhs ← split_mult a,
       rhs ← split_mult b,
       return (lhs ++ rhs)
| e := match e with
        | `(%%a ≃ %%b) := (fun x y, x :: y ::[]) 
                        <$> to_expr ``(%%a ≃ %%b) 
                        <*> to_expr ``(%%b ≃ %%a)
        | _            := return []
       end 

meta def eq_exist : expr →  list expr → bool :=
(λ e l, 
match l with
| [] := ff
| (h :: t) := if h=e then tt else (eq_exist e t)
end)

meta def test_split_mul :=
    do tgt ← tactic.target,
       rs ← split_mult tgt,
       tactic.trace rs,
       return () 

meta def trans_step :=
    do t ← tactic.target,
       rs ← split_mult t,
       match t with 
        | `(%%a * %%b) := if (eq_exist a rs) then applyc `eq_trans else return ()
        | _ := return ()
       end

-- set_option pp. false
-- set_option trace.simplify true
section
variables {s: Schema} {t₁ t₂ t₃: Tuple s} {a b c d e: usr} 
private meta def simp_solve :=
    `[intros, simp, assumption <|> ac_refl ]

lemma usr_eq_symm: a = b → b = a := 
begin
    intros, rewrite a_1, 
end

-- should match the equations in the tail?
lemma ueq_trans_1 : 
(t₁ ≃ t₂) * ((t₂ ≃ t₃) * c) * (d * (t₁ ≃ t₃)) = e → 
(t₁ ≃ t₂) * ((t₂ ≃ t₃) * c) * d = e  := 
begin
    intros,
    rw ← a,
    rw ← time_assoc,
    rw eq_trans,
    simp,
end

lemma ueq_trans_2 : 
(t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * (d * (t₂ ≃ t₃)) = e → 
(t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * d = e  := 
begin
    intros,
    rw ← a,
    rw ← time_assoc,
    simp,
end

lemma ueq_trans_3 : 
(t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * (d * (t₃ ≃ t₂)) = e → 
(t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * d = e  := 
begin
    intros,
    rw ← a,
    rw ← time_assoc,
    simp,
end

lemma prod_symm_assoc :
a * (b * c) = b * (a * c) := by ac_refl 

end

-- make sure all product is right assoc
meta def right_assoc :=
    `[repeat {rewrite time_assoc}]

-- change the goal to the form  a x 1 = b x 1
lemma add_unit (a b: usr):
    a * 1 = b * 1 → a = b :=
begin
    simp,
    intros, 
    assumption,
end

meta def product_to_repr : expr → list expr
| `(%%a * %%b) := a :: product_to_repr b
| e := [e] 

meta def repr_to_product : list expr → tactic expr
| [x] := return x
| (h::t) :=  do te ← repr_to_product t,
                to_expr ``(%%h * %%te)
| [] := failed

meta def get_lhs_repr : tactic (list expr) :=
target >>= λ e,
match e with
| `(%%a = %%b) := return $ product_to_repr a
| _ := failed
end

meta def swap_ith_pred_forward (i: nat) (l: list expr) : tactic unit :=
    do 
    swapped_list ← list.swap_ith_forward i l,
    origin_expr ← repr_to_product l,
    swapped_expr ← repr_to_product swapped_list,
    eq_lemma ← to_expr ``(%%origin_expr = %%swapped_expr),
    eq_lemma_name ← mk_fresh_name,
    tactic.assert eq_lemma_name eq_lemma,
    repeat_n i $ (to_expr ``(congr_arg (has_mul.mul _)) >>= apply >> return ()),
    applyc `prod_symm_assoc <|> applyc `mul_comm,
    eq_lemma ← resolve_name eq_lemma_name >>= to_expr,
    rewrite_target eq_lemma,
    clear eq_lemma

meta def move_once (i : nat) : tactic unit :=
    get_lhs_repr >>= swap_ith_pred_forward i

lemma congr_ex0 (a b c d e f: usr):
    c * d = e :=
begin
    move_once 0,
    sorry
end

lemma congr_ex1 {s: Schema} (a b c d e f: Tuple s) (R: Tuple s → usr):
     (a ≃ c) * (e ≃ c)  = (e ≃ c) * (a ≃ c)  :=
begin
    unify_eq,
    right_assoc,
    apply add_unit,
    sorry
end


