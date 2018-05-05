import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants
import ..ucongr
import ..TDP

open Expr
open Proj
open Pred
open SQL
open tree

notation `int` := datatypes.int

variable integer_1: const datatypes.int
variable integer_7: const datatypes.int

theorem rule:
forall ( Γ scm_t scm_account scm_bonus scm_dept scm_emp: Schema) (rel_t: relation scm_t) (rel_account: relation scm_account) (rel_bonus: relation scm_bonus) (rel_dept: relation scm_dept) (rel_emp: relation scm_emp) (t_k0 : Column int scm_t) (t_c1 : Column int scm_t) (t_f1_a0 : Column int scm_t) (t_f2_a0 : Column int scm_t) (t_f0_c0 : Column int scm_t) (t_f1_c0 : Column int scm_t) (t_f0_c1 : Column int scm_t) (t_f1_c2 : Column int scm_t) (t_f2_c3 : Column int scm_t) (account_acctno : Column int scm_account) (account_type : Column int scm_account) (account_balance : Column int scm_account) (bonus_ename : Column int scm_bonus) (bonus_job : Column int scm_bonus) (bonus_sal : Column int scm_bonus) (bonus_comm : Column int scm_bonus) (dept_deptno : Column int scm_dept) (dept_name : Column int scm_dept) (emp_empno : Column int scm_emp) (emp_ename : Column int scm_emp) (emp_job : Column int scm_emp) (emp_mgr : Column int scm_emp) (emp_hiredate : Column int scm_emp) (emp_comm : Column int scm_emp) (emp_sal : Column int scm_emp) (emp_deptno : Column int scm_emp) (emp_slacker : Column int scm_emp),
denoteSQL ((SELECT1 (e2p (constantExpr integer_1)) FROM1 (product (table rel_emp) ((SELECT * FROM1 (table rel_emp) WHERE (castPred (combine (right⋅emp_deptno) (e2p (constantExpr integer_7)) ) predicates.gt)))) WHERE (equal (uvariable (right⋅left⋅emp_deptno)) (uvariable (right⋅right⋅emp_deptno)))) :SQL Γ _)
=
denoteSQL ((SELECT1 (e2p (constantExpr integer_1)) FROM1 (product ((SELECT * FROM1 (table rel_emp) WHERE (castPred (combine (right⋅emp_deptno) (e2p (constantExpr integer_7)) ) predicates.gt))) ((SELECT * FROM1 (table rel_emp) WHERE (castPred (combine (right⋅emp_deptno) (e2p (constantExpr integer_7)) ) predicates.gt)))) WHERE (equal (uvariable (right⋅left⋅emp_deptno)) (uvariable (right⋅right⋅emp_deptno)))) :SQL Γ _)  :=
begin
  intros,
  unfold_all_denotations,
  funext,
  try {simp},
  apply congr_arg _,
  funext,
  apply congr_arg _,
  funext,
  split_pairs,
  unify_ueq,
  move_ueq,
  apply add_unit_m,
  subst_lhs,
  apply ueq_symm,
  subst_lhs,  
  remove_dup_pred,
  apply ueq_symm,
  remove_dup_pred,
  sorry
end

example (Γ scm_emp : Schema)
(rel_emp : relation scm_emp)
(emp_deptno : Column int scm_emp)
(t' : Tuple (leaf datatypes.int))
(t₁ t₂ : Tuple scm_emp):
(denoteProj emp_deptno t₂≃denoteProj emp_deptno t₁) * 1 *
      (denotePred predicates.gt (pair (denoteProj emp_deptno t₂) (denote_c integer_7))) =
(denoteProj emp_deptno t₂≃denoteProj emp_deptno t₁) * 1 *
      (denotePred predicates.gt (pair (denoteProj emp_deptno t₂) (denote_c integer_7)) *
         (denotePred predicates.gt (pair (denoteProj emp_deptno t₁) (denote_c integer_7)) *
            (denote_r rel_emp t₁ * denote_r rel_emp t₂))) :=
begin
  unfold pair,
  rw (@ueq_subst_in_spnf' _ (denoteProj emp_deptno t₂) (denoteProj emp_deptno t₁) 1 (λ t, denotePred predicates.gt (t, (denote_c integer_7)))),
  sorry
end