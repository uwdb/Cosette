import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants

open Expr
open Proj
open Pred
open SQL
open binary_operators

theorem rule :
    forall (Γ s1 : Schema) (a : relation s1)
           (x : Column datatypes.int s1) (y : Column datatypes.int s1),
           let xVar : Expr (Γ ++ s1) _ := uvariable (right⋅x),
               yVar : Expr (Γ ++ s1) _ := uvariable (right⋅y) in
           denoteSQL (SELECT1 (e2p (binaryExpr add xVar xVar))
                      FROM1 (table a WHERE (equal xVar yVar)) : SQL Γ _) =
           denoteSQL (SELECT1 (e2p (binaryExpr add xVar yVar))
                      FROM1 (table a WHERE (equal xVar yVar)) : SQL Γ _) :=
begin
    admit
end