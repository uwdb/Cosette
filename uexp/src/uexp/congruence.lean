import .u_semiring

open tactic

private meta def walk_product : expr → tactic unit
| `(%%a * %%b) := walk_product a >> walk_product b
| `(%%t₁ ≃ %%t₂) :=
  if t₁ > t₂
    then return ()
    else do h ← to_expr ``(eq_symm %%t₁ %%t₂),
            try $ rewrite_target h,
            tactic.trace $ "rewriting " ++ h.to_string,
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
variables {s: Schema} {t₁ t₂ t₃: Tuple s} {a b c d: usr} 
private meta def simp_solve :=
    `[intros, simp, assumption <|> ac_refl ]

lemma prod_unit_p1: c = d → 1 * c = d := by simp_solve

lemma plus_assoc_p1: a * (b * c) = d → (a * b) * c = d := by simp_solve

lemma prod_assoc_p2: 
b * (a * c) = d → (a * b) * c = d := 
begin
    intros,
    rw ← a_1,
    ac_refl
end

lemma plus_comm_p : a * b = c → b * a = c := by simp_solve

lemma plus_unit_c : a = b → a = 1 * b := by simp_solve

lemma plus_assoc_c1 : d = a * (b * c) → (a * b) * c = d := 
begin
    intros,
    rw a_1,
    ac_refl,
end

lemma plus_assoc_c2 : d = b * (a * c) → (a * b) * c = d :=
begin
    intros,
    rw a_1,
    ac_refl,
end    

lemma plus_comm_c : c = a * b → c = b * a := by simp_solve

lemma plus_cancel : 
(t₁ ≃ t₂) * ((t₂ ≃ t₃) * c) = d  := 
begin
    intros,
    rw a_1,
    rw a_2,
end
end

lemma congr_ex1 {s: Schema} (a b c d: Tuple s):
     (a ≃ b) * (b ≃ c) * (a ≃ c) = (a ≃ c) * (b ≃ c)   :=
begin
    unify_eq,
    sorry
end
