import ..u_semiring


@[derive [decidable_eq]]
meta inductive ast : Type
| one : ast
| zero : ast
| plus : ast → ast → ast
| time : ast → ast → ast
| sig : list (name × expr) → ast → ast
| const : expr → ast
| squash : ast → ast
| not : ast → ast
| ueq : expr → expr → ast

-- The ast is formatted as an s-expression to distinguish it from actual terms
meta def ast.format : ast → format
| ast.one := "one"
| ast.zero := "zero"
| (ast.plus x y) := "(plus "
                 ++ x.format ++ " "
                 ++ y.format ++ ")"
| (ast.time x y) := "(time "
                 ++ x.format ++ " "
                 ++ y.format ++ ")"
| (ast.sig [] body) := "(sigma () " ++ body.format ++ ")"
| (ast.sig (var::vars) body) :=
  let format_var (v : name × expr) : format :=
    "(" ++ has_to_format.to_format v.fst ++ " : "
          ++ has_to_format.to_format v.snd ++ ")"
  in "(sigma (" ++ format_var var
                ++ vars.foldr (λ v fmt, " " ++ format_var v ++ fmt) ")"
                ++ body.format ++ ")"
| (ast.const e) := "(const " ++ has_to_format.to_format e ++ ")"
| (ast.squash x) := "(squash " ++ x.format ++ ")"
| (ast.not x) := "(not " ++ x.format ++ ")"
| (ast.ueq t1 t2) := "(eq " ++ has_to_format.to_format t1 ++ " "
                            ++ has_to_format.to_format t2 ++ ")"

meta instance ast_has_to_format : has_to_format ast := ⟨ast.format⟩

-- TODO: Make all products into lists
meta def ast.of_expr : expr → tactic ast
| `(1) := return ast.one
| `(usr.one) := return ast.one
| `(0) := return ast.zero
| `(usr.zero) := return ast.zero
| `(%%a + %%b) := do
  a' ← ast.of_expr a,
  b' ← ast.of_expr b,
  return $ ast.plus a' b'
| `(usr.plus %%a %%b) := tactic.to_expr ``(%%a + %%b) >>= ast.of_expr
| `(%%a * %%b) := do
  a' ← ast.of_expr a,
  b' ← ast.of_expr b,
  return $ ast.time a' b'
| `(usr.time %%a %%b) := tactic.to_expr ``(%%a * %%b) >>= ast.of_expr
| `(∑ (t : Tuple %%s), %%b) := do
  n ← tactic.mk_fresh_name,
  ty ← tactic.to_expr ``(Tuple %%s),
  let local_const := expr.local_const n n binder_info.default ty,
  let closed_body := expr.instantiate_var b local_const,
  b' ← ast.of_expr b,
  match b' with
  | (ast.sig bindings body) :=
    let bindings' := (n, ty) :: bindings
    in return $ ast.sig bindings' body
  | _ := return $ ast.sig [(n, ty)] b'
  end
| `(usr.squash %%x) := ast.squash <$> ast.of_expr x
| `(usr.not %%x) := ast.not <$> ast.of_expr x
| `(%%t ≃ %%t') := return $ ast.ueq t t'
| _ := tactic.fail "not an ast"

meta def make_r_assoc_expr (terms : list expr) (op ident : expr) : tactic expr :=
match terms with 
| [] := return ident
| (x::xs) :=
  let last_term := list.last (x::xs) (by intro h; cases h),
      init_terms := list.init (x::xs)
  in init_terms.mfoldr (λ x sum, tactic.to_expr ``(%%op %%x %%sum))
                       last_term
end

meta def expr.of_ast (a : ast) : tactic expr :=
  ast.rec_on a
  (return `(usr.one)) -- ast.one
  (return `(usr.zero)) -- ast.zero
  (λ (x y :  ast) (eval_x eval_y : tactic expr), do
    x' : expr ← eval_x,
    y' : expr ← eval_y,
    tactic.to_expr ``(usr.plus %%x' %%y')) -- ast.plus
  (λ (x y :  ast) (eval_x eval_y : tactic expr), do
    x' : expr ← eval_x,
    y' : expr ← eval_y,
    tactic.to_expr ``(usr.time %%x' %%y')) -- ast.time
  (λ vars body_ast (eval_body : tactic expr), do
    let ⟨names, types⟩ := list.unzip vars,
    body_expr ← eval_body,
    let closed_body_expr := expr.abstract_locals body_expr (list.reverse names),
    list.mfoldr (λ (ty : expr) (body : expr),
                   tactic.to_expr ``(∑ (x : %%ty), %%body))
                closed_body_expr
                types) -- ast.sig
  (λ e : expr, return e)
  (λ x (eval_x : tactic expr), do
    x' : expr ← eval_x,
    tactic.to_expr ``(usr.squash %%x')) -- ast.squash
  (λ x (eval_x : tactic expr), do
    x' : expr ← eval_x,
    tactic.to_expr ``(usr.not %%x')) -- ast.not
  (λ t1 t2, tactic.to_expr ``(%%t1 ≃ %%t2)) -- ast.ueq