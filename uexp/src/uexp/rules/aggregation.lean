import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants

open Expr
open Proj
open Pred
open SQL
open tree

#check groupBy

theorem aggegation_query :
forall (Γ : Schema) s (a : relation s) C0 (value : Column C0 s) C1 (label: Column C1 s) (l : const C1),
    let lbl := @uvariable C1 (Γ ++ s) (right⋅label),
        val := @uvariable C0 (Γ ++ s) (right⋅value),
        lbl' := @uvariable C1 (Γ ++ (leaf C1 ++ leaf datatypes.int)) (right⋅left)
    in (denoteSQL ((SELECT *
                  FROM1
                  (groupBy (combineGroupByProj (PLAIN lbl) (COUNT val)) (table a) (right⋅label)) 
                  WHERE equal lbl' (constantExpr l)) : SQL Γ _)) = 
       (denoteSQL ((SELECT *
                   FROM1
                   (groupBy 
                   (combineGroupByProj (PLAIN lbl) (COUNT val))
                   (SELECT * FROM1 (table a) WHERE equal lbl (constantExpr l))
                   (right⋅label))) : SQL Γ _)) :=
begin
intros,
unfold_all_denotations,
funext,
simp,
sorry
end