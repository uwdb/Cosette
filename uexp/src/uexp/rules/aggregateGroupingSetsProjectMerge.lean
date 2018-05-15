import ..extra_constants
import ..sql
import ..u_semiring
import ..cosette_tactics
import ..TDP

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
    denoteSQL
    (SELECT (combineGroupByProj PLAIN(@uvariable datatypes.int (Γ ++ scm_s) (right⋅s_a))
                  $ combineGroupByProj PLAIN(@uvariable datatypes.int (Γ ++ scm_s) (right⋅s_b))
                  $ COUNT(@uvariable datatypes.int (Γ ++ scm_s) (right⋅s_c)))
     FROM1 table rel_r
     GROUP BY combine (right⋅s_a) (right⋅s_b) : SQL Γ _) =
    denoteSQL
    (SELECT (combineGroupByProj PLAIN(@uvariable datatypes.int (Γ ++ scm_s) (right⋅s_a))
                  $ combineGroupByProj PLAIN(@uvariable datatypes.int (Γ ++ scm_s) (right⋅s_b))
                  $ COUNT(@uvariable datatypes.int (Γ ++ scm_s) (right⋅s_c)))
     FROM1 table rel_r
     GROUP BY combine (right⋅s_b) (right⋅s_a) : SQL Γ _) :=
begin
    intros,
    unfold_all_denotations,
    funext,
    simp,
    print_size,
   sorry 
end