import ..u_semiring

def tuple_var := nat

constant schema_rep : Type -- TODO: what should this be?
meta constant expr_to_schema_rep : expr → tactic schema_rep

inductive ast : Type
| one : ast
| zero : ast
| plus : list ast → ast
| time : list ast → ast
| sig : list schema_rep → ast → ast
| of_var : tuple_var → ast
| squash : ast → ast
| not : ast → ast
| ueq : tuple_var → tuple_var → ast

meta constant expr_to_tuple : expr → tactic tuple_var

meta def ast.of_expr : expr → tactic ast
| `(1) := return ast.one
| `(usr.one) := return ast.one
| `(0) := return ast.zero
| `(usr.zero) := return ast.zero
| `(%%a + %%b) := do
  a' ← ast.of_expr a,
  b' ← ast.of_expr b,
  match b' with
  | (ast.plus bs) := return $ ast.plus (a' :: bs)
  | _ := return $ ast.plus [a', b']
  end
| `(usr.plus %%a %%b) := tactic.to_expr ``(%%a + %%b) >>= ast.of_expr
| `(%%a * %%b) := do
  a' ← ast.of_expr a,
  b' ← ast.of_expr b,
  match b' with
  | (ast.time bs) := return $ ast.time (a' :: bs)
  | _ := return $ ast.time [a', b']
  end
| `(usr.time %%a %%b) := tactic.to_expr ``(%%a * %%b) >>= ast.of_expr
| `(∑ (t : Tuple %%s), %%b) := do
  b' ← ast.of_expr b,
  s' ← expr_to_schema_rep s,
  match b' with
  | (ast.sig schemas body) :=
    let schemas' := s' :: schemas
    in return $ ast.sig schemas' body
  | _ := return $ ast.sig [s'] b'
  end
| `(usr.squash %%x) := ast.squash <$> ast.of_expr x
| `(usr.not %%x) := ast.not <$> ast.of_expr x
| `(%%t ≃ %%t') := ast.ueq <$> expr_to_tuple t <*> expr_to_tuple t'