import .u_semiring_AST

meta def generator (transform : ast → ast)
                   (transform_eq : tactic unit)
                   (get_expr : tactic expr)
                   : tactic unit := do
                   eq ← get_expr,
                   