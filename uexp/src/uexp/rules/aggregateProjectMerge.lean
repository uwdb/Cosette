import ..extra_constants
import ..sql
import ..u_semiring
import ..tactics
import ..cosette_tactics

open SQL
open Proj
open Pred
open Expr

theorem rule :
    forall (Γ scm_emp : Schema)
           (rel_emp : relation scm_emp)
           (emp_empno : Column datatypes.int scm_emp)
           (emp_ename : Column datatypes.int scm_emp)
           (emp_job : Column datatypes.int scm_emp)
           (emp_mgr : Column datatypes.int scm_emp)
           (emp_hiredate : Column datatypes.int scm_emp)
           (emp_comm : Column datatypes.int scm_emp)
           (emp_sal : Column datatypes.int scm_emp)
           (emp_deptno : Column datatypes.int scm_emp)
           (emp_slacker : Column datatypes.int scm_emp),
           denoteSQL (SELECT (combineGroupByProj PLAIN(uvariable (right⋅emp_deptno))
                                (combineGroupByProj SUM(uvariable (right⋅emp_sal))
                                                    PLAIN(uvariable (right⋅emp_empno))))
                      FROM1 table rel_emp
                      GROUP BY combine (right⋅emp_deptno) (right⋅emp_empno) : SQL Γ _) =
           denoteSQL (SELECT (combineGroupByProj PLAIN(uvariable (right⋅emp_deptno))
                                (combineGroupByProj SUM(uvariable (right⋅emp_sal))
                                                    PLAIN(uvariable (right⋅emp_empno))))
                      FROM1 table rel_emp
                      GROUP BY combine (right⋅emp_empno) (right⋅emp_deptno) : SQL Γ _) :=
begin
    intros,
    unfold_all_denotations,
    funext,
    simp,
    sorry
end