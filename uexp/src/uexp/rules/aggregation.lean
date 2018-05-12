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
    let lbl : Expr (Γ ++ s) C1 := uvariable (right⋅label),
        val : Expr (Γ ++ s) C0 := uvariable (right⋅value),
        lbl' : Expr (Γ ++ (leaf C1 ++ leaf datatypes.int)) C1 := uvariable (right⋅left)
    in (denoteSQL ((SELECT *
                  FROM1
                  (SELECT (combineGroupByProj PLAIN(lbl) COUNT(val))
                   FROM1 (table a)
                   GROUP BY (right⋅label))
                  WHERE equal lbl' (constantExpr l)) : SQL Γ _)) = 
       (denoteSQL ((SELECT *
                   FROM1
                   (SELECT (combineGroupByProj PLAIN(lbl) COUNT(val))
                    FROM1 (SELECT * FROM1 (table a) WHERE equal lbl (constantExpr l))
                    GROUP BY (right⋅label))) : SQL Γ _)) :=
begin
intros,
unfold_all_denotations,
simp,
funext,
sorry
end