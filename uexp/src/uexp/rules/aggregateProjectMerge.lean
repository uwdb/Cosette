import ..extra_constants
import ..sql
import ..u_semiring
import ..tactics

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
           let deptnoProj : Proj (Γ ++ scm_emp) _ := right⋅emp_deptno,
               salProj : Proj (Γ ++ scm_emp) _ := right⋅emp_sal,
               empnoProj : Proj (Γ ++ scm_emp) _ := right⋅emp_empno in
           denoteSQL (SELECT (combineGroupByProj PLAIN(uvariable deptnoProj)
                                (combineGroupByProj SUM(uvariable salProj)
                                                    PLAIN(uvariable empnoProj)))
                      FROM1 table rel_emp
                      GROUP BY combine deptnoProj empnoProj : SQL Γ _) =
           denoteSQL (SELECT (combineGroupByProj PLAIN(uvariable deptnoProj)
                                (combineGroupByProj SUM(uvariable salProj)
                                                    PLAIN(uvariable empnoProj)))
                      FROM1 table rel_emp
                      GROUP BY combine empnoProj deptnoProj : SQL Γ _) :=
begin
    intros,
    unfold_all_denotations,
    funext,
    simp,
    sorry,
end