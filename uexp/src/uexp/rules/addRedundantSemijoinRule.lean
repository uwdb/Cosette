import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants
import ..TDP ..canonize
import ..ucongr
import ..cosette_tactics

set_option profiler true

variable i : const datatypes.int

open SQL
open Pred
open Expr
open Proj

theorem rule :
    forall (Γ scm_dept scm_emp : Schema)
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
           denoteSQL ((SELECT1 (e2p (constantExpr i)) (FROM1 (product (table rel_emp) (product (table rel_dept) (table rel_dept))) WHERE (and (equal (uvariable (right⋅left⋅emp_deptno)) (uvariable (right⋅right⋅left⋅dept_deptno))) (equal (uvariable (right⋅left⋅emp_deptno)) (uvariable (right⋅right⋅right⋅dept_deptno)))))): SQL Γ _) :=
begin
    intros,
    unfold_all_denotations,
    funext,
    simp,
    print_size,
    have assert₀
        : (∑ (t₁ : Tuple scm_emp) (t₁_1 t₂ : Tuple scm_dept),
            (denoteProj dept_deptno t₁_1≃denoteProj emp_deptno t₁) *
                ((denoteProj dept_deptno t₂≃denoteProj emp_deptno t₁) *
                    (denote_r rel_emp t₁ * (denote_r rel_dept t₁_1 * (denote_r rel_dept t₂ * (t'≃denote_c i))))))
        = ∑ (t₁ : Tuple scm_emp) (t₁_1 t₂ : Tuple scm_dept),
            (denoteProj dept_deptno t₁_1≃denoteProj dept_deptno t₂) *
                ((denoteProj dept_deptno t₁_1≃denoteProj emp_deptno t₁) *
                    ((denoteProj dept_deptno t₂≃denoteProj emp_deptno t₁) *
                        (denote_r rel_emp t₁ * (denote_r rel_dept t₁_1 * (denote_r rel_dept t₂ * (t'≃denote_c i)))))),
    { congr, funext, congr, funext, congr, funext, ucongr },
    rw assert₀, clear assert₀,
    canonize, TDP
end