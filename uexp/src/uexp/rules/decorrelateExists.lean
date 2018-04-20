import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants

open Expr
open Proj
open Pred
open SQL

variable i : const datatypes.int

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
    let left_deptno : Expr ((Γ ++ scm_emp) ++ scm_emp) datatypes.int
                    := uvariable (left⋅right⋅emp_deptno),
        right_deptno : Expr ((Γ ++ scm_emp) ++ scm_emp) datatypes.int
                    := uvariable (right⋅emp_deptno) in
    denoteSQL
    (SELECT *
     FROM1 (table rel_emp
            WHERE EXISTS (SELECT *
                           FROM1 table rel_emp
                           WHERE (equal left_deptno right_deptno)))
    : SQL Γ _) =
    denoteSQL
    (SELECT1 (right⋅left⋅star)
     FROM1 (product (table rel_emp)
                     (DISTINCT (SELECT1 (combine (right⋅emp_deptno)
                                                 (e2p (constantExpr i)))
                                FROM1 table rel_emp))
            WHERE (equal (uvariable (right⋅left⋅emp_deptno))
                         (uvariable (right⋅right⋅left)))) : SQL Γ _) :=
begin
    intros,
    unfold_all_denotations,
    funext,
    simp,
    sorry
end