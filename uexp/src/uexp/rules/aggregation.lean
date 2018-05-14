import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants
import ..cosette_tactics

open Expr
open Proj
open Pred
open SQL
open tree

theorem aggegation_query :
forall (Γ : Schema) s (a : relation s) C0 (value : Column C0 s) C1 (label: Column C1 s) (l : const C1),
    (denoteSQL ((SELECT *
                FROM1
                (SELECT (combineGroupByProj PLAIN((uvariable (right⋅label))) COUNT(uvariable (right⋅value)))
                FROM1 (table a)
                GROUP BY (right⋅label))
                WHERE equal (uvariable (right⋅left)) (constantExpr l)) : SQL Γ _)) = 
    (denoteSQL ((SELECT *
                FROM1
                (SELECT (combineGroupByProj PLAIN((uvariable (right⋅label))) COUNT(uvariable (right⋅value)))
                FROM1 (SELECT * FROM1 (table a) WHERE equal (uvariable (right⋅label)) (constantExpr l))
                GROUP BY (right⋅label))) : SQL Γ _)) :=
begin
intros,
unfold_all_denotations,
simp,
funext,
sorry
end