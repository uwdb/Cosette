import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants
import ..meta.cosette_tactics


open Expr
open Proj
open Pred
open SQL
open tree

notation `int` := datatypes.int
constant integer_10 : const int

definition rule: forall (Γ scm_dept: Schema) (rel_dept: relation scm_dept) (dept_deptno : Column int scm_dept) (dept_name : Column int scm_dept), 
denoteSQL 
((SELECT1 (combine (right⋅left) (right⋅right)) FROM1 ((SELECT  (combineGroupByProj PLAIN(uvariable (right⋅dept_name)) (COUNT(uvariable (right⋅dept_name)))) FROM1  (table rel_dept)  GROUP BY  (right⋅dept_name))) WHERE (equal (uvariable (right⋅left)) (@constantExpr _ _ integer_10))) :SQL Γ  _ ) =
denoteSQL 
((SELECT  (combineGroupByProj PLAIN(uvariable (right)) (COUNT(uvariable right))) 
 FROM1 (((SELECT1 (right⋅dept_name) FROM1 (table rel_dept) )) 
 WHERE (equal (uvariable right) (constantExpr integer_10))) 
 GROUP BY (right)) : SQL Γ _) :=
 begin
    intros,
    unfold_all_denotations,
    funext,
    print_size,
    simp,
    print_size,
    sorry
end
