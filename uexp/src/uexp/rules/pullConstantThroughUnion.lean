import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants
import ..ucongr
import ..TDP
import ..UDP

open Expr
open Proj
open Pred
open SQL
open tree

notation `int` := datatypes.int
 
constant integer_2 : const int

theorem rule:
    forall ( Γ scm_emp: Schema) (rel_emp: relation scm_emp) (emp_empno : Column int scm_emp) (emp_ename : Column int scm_emp) (emp_job : Column int scm_emp) (emp_mgr : Column int scm_emp) (emp_hiredate : Column int scm_emp) (emp_comm : Column int scm_emp) (emp_sal : Column int scm_emp) (emp_deptno : Column int scm_emp) (emp_slacker : Column int scm_emp), 
    denoteSQL (((SELECT1 (combine (e2p (constantExpr integer_2)) (combine (right⋅emp_deptno) (right⋅emp_job))) FROM1 (table rel_emp) )) UNION ALL ((SELECT1 (combine (e2p (constantExpr integer_2)) (combine (right⋅emp_deptno) (right⋅emp_job))) FROM1 (table rel_emp) )) : SQL Γ _ ) 
    = denoteSQL ((SELECT1 (combine (e2p (constantExpr integer_2)) (combine (right⋅left) (right⋅right))) FROM1 (((SELECT1 (combine (right⋅emp_deptno) (right⋅emp_job)) FROM1 (table rel_emp) )) UNION ALL ((SELECT1 (combine (right⋅emp_deptno) (right⋅emp_job)) FROM1 (table rel_emp) ))) ) : SQL Γ _) :=
begin
    intros,
    unfold_all_denotations,
    funext,
    simp,
    sorry
end 