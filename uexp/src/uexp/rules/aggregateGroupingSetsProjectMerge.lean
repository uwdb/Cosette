import ..extra_constants
import ..sql
import ..u_semiring
import ..tactics

open SQL
open Proj
open Pred
open Expr

theorem rule :
    forall (Γ scm_s : Schema)
           (rel_r : relation scm_s)
           (s_a : Column datatypes.int scm_s)
           (s_b : Column datatypes.int scm_s)
           (s_c : Column datatypes.int scm_s),
    let var_a : Expr (Γ ++ scm_s) datatypes.int := uvariable (right⋅s_a),
        var_b : Expr (Γ ++ scm_s) datatypes.int := uvariable (right⋅s_b),
        var_c : Expr (Γ ++ scm_s) datatypes.int := uvariable (right⋅s_c),
        groupByVars := combineGroupByProj PLAIN(var_a)
                  $ combineGroupByProj PLAIN(var_b)
                  $ COUNT(var_c) in
    denoteSQL
    (SELECT (groupByVars)
     FROM1 table rel_r
     GROUP BY combine (right⋅s_a) (right⋅s_b) : SQL Γ _) =
    denoteSQL
    (SELECT (groupByVars)
     FROM1 table rel_r
     GROUP BY combine (right⋅s_b) (right⋅s_a) : SQL Γ _) :=
begin
    intros,
    unfold_all_denotations,
    funext,
    simp,
end