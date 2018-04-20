import .u_semiring

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

-- should match the equations in the tail?
lemma prod_eq_trans_1 : 
(t₁ ≃ t₂) * ((t₂ ≃ t₃) * c) * (d * (t₁ ≃ t₃)) = e → 
(t₁ ≃ t₂) * ((t₂ ≃ t₃) * c) * d = e  := 
begin
    intros,
    rw ← a,
    rw ← time_assoc,
    rw eq_trans,
    simp,
end

lemma prod_eq_trans_2 : 
(t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * (d * (t₂ ≃ t₃)) = e → 
(t₁ ≃ t₂) * ((t₁ ≃ t₃) * c) * d = e  := 
begin
    intros,
    rw ← a,
    rw ← time_assoc,
    simp,
end

lemma prod_eq_trans_3 : 
(t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * (d * (t₃ ≃ t₂)) = e → 
(t₁ ≃ t₂) * ((t₃ ≃ t₂) * c) * d = e  := 
begin
    intros,
    rw ← a,
    rw ← time_assoc,
    simp,
end
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

lemma congr_ex1 {s: Schema} (a b c d e f: Tuple s) (R: Tuple s → usr):
     (a ≃ b) * (d ≃ e) * (b ≃ c)  = (a ≃ c) * (b ≃ c) * (e ≃ d)  :=
begin
    unify_eq,
    right_assoc,
    apply add_unit,
    sorry
end

