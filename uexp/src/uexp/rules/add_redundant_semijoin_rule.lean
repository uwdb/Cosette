import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants

variable i : const datatypes.int

open SQL
open Pred
open Expr
open Proj

definition rule : Prop := Π (Γ scm_dept scm_emp : Schema)
                     (rel_dept : relation scm_dept)
                     (rel_emp : relation scm_emp)
                     (dept_deptno : Column datatypes.int scm_dept)
                     (dept_name : Column datatypes.int scm_dept)
                     (emp_empno : Column datatypes.int scm_emp)
                     (emp_ename : Column datatypes.int scm_emp)
                     (emp_job : Column datatypes.int scm_emp)
                     (emp_mgr : Column datatypes.int scm_emp)
                     (emp_hiredate : Column datatypes.int scm_emp)
                     (emp_comm : Column datatypes.int scm_emp)
                     (emp_sal : Column datatypes.int scm_emp)
                     (emp_deptno : Column datatypes.int scm_emp)
                     (emp_slacker : Column datatypes.int scm_emp)
                     (k1 : isKey emp_empno rel_emp)
                     (k2 : isKey dept_deptno rel_dept),
                     denoteSQL ((SELECT1 (e2p (constantExpr i)) (FROM1 (product (table rel_emp) (table rel_dept)) WHERE (equal (uvariable (right⋅left⋅emp_deptno)) (uvariable (right⋅right⋅dept_deptno))))): SQL Γ _) = 
                     denoteSQL ((SELECT1 (e2p (constantExpr i)) (FROM1 (product (table rel_emp) (product (table rel_dept) (table rel_dept))) WHERE (and (equal (uvariable (right⋅left⋅emp_deptno)) (uvariable (right⋅right⋅left⋅dept_deptno))) (equal (uvariable (right⋅left⋅emp_deptno)) (uvariable (right⋅right⋅right⋅dept_deptno)))))): SQL Γ _)

theorem rule_is_valid : Π i, rule i :=
begin
    intros,
    unfold rule,
    intros,
    unfold_all_denotations,
    funext,
    simp,
    admit
end