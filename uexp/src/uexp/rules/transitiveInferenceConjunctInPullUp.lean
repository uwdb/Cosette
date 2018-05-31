import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants
import ..meta.ucongr
import ..meta.TDP
import ..meta.UDP

open Expr
open Proj
open Pred
open SQL
open tree

notation `int` := datatypes.int

variable integer_1: const datatypes.int
variable integer_7: const datatypes.int
variable integer_9: const datatypes.int
variable integer_10: const datatypes.int


theorem rule:
forall ( Γ scm_t scm_account scm_bonus scm_dept scm_emp: Schema) (rel_t: relation scm_t) (rel_account: relation scm_account) (rel_bonus: relation scm_bonus) (rel_dept: relation scm_dept) (rel_emp: relation scm_emp) (t_k0 : Column int scm_t) (t_c1 : Column int scm_t) (t_f1_a0 : Column int scm_t) (t_f2_a0 : Column int scm_t) (t_f0_c0 : Column int scm_t) (t_f1_c0 : Column int scm_t) (t_f0_c1 : Column int scm_t) (t_f1_c2 : Column int scm_t) (t_f2_c3 : Column int scm_t) (account_acctno : Column int scm_account) (account_type : Column int scm_account) (account_balance : Column int scm_account) (bonus_ename : Column int scm_bonus) (bonus_job : Column int scm_bonus) (bonus_sal : Column int scm_bonus) (bonus_comm : Column int scm_bonus) (dept_deptno : Column int scm_dept) (dept_name : Column int scm_dept) (emp_empno : Column int scm_emp) (emp_ename : Column int scm_emp) (emp_job : Column int scm_emp) (emp_mgr : Column int scm_emp) (emp_hiredate : Column int scm_emp) (emp_comm : Column int scm_emp) (emp_sal : Column int scm_emp) (emp_deptno : Column int scm_emp) (emp_slacker : Column int scm_emp),
denoteSQL ((SELECT1 (e2p (constantExpr integer_1)) FROM1 (product ((SELECT * FROM1 (table rel_emp) WHERE (or (or (equal (uvariable (right⋅emp_deptno)) (constantExpr integer_7)) (equal (uvariable (right⋅emp_deptno)) (constantExpr integer_9))) (castPred (combine (right⋅emp_deptno) (e2p (constantExpr integer_10)) ) predicates.gt)))) (table rel_emp)) WHERE (equal (uvariable (right⋅left⋅emp_deptno)) (uvariable (right⋅right⋅emp_deptno)))) :SQL Γ _)
=
denoteSQL ((SELECT1 (e2p (constantExpr integer_1)) FROM1 (product ((SELECT * FROM1 (table rel_emp) WHERE (or (or (equal (uvariable (right⋅emp_deptno)) (constantExpr integer_7)) (equal (uvariable (right⋅emp_deptno)) (constantExpr integer_9))) (castPred (combine (right⋅emp_deptno) (e2p (constantExpr integer_10)) ) predicates.gt)))) ((SELECT * FROM1 (table rel_emp) WHERE (or (or (equal (uvariable (right⋅emp_deptno)) (constantExpr integer_7)) (equal (uvariable (right⋅emp_deptno)) (constantExpr integer_9))) (castPred (combine (right⋅emp_deptno) (e2p (constantExpr integer_10)) ) predicates.gt))))) WHERE (equal (uvariable (right⋅left⋅emp_deptno)) (uvariable (right⋅right⋅emp_deptno)))) :SQL Γ _)  :=
begin
  intros,
  unfold_all_denotations,
  funext,
  try {simp},
  sorry
end