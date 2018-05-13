import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants

import ..ucongr
import ..TDP ..canonize

open Expr
open Proj
open Pred
open SQL
open tree

notation `int` := datatypes.int

definition rule:  
    forall ( Γ scm_dept scm_emp: Schema) (rel_dept: relation scm_dept) (rel_emp: relation scm_emp) (dept_deptno : Column int scm_dept) (dept_name : Column int scm_dept) (emp_empno : Column int scm_emp) (emp_ename : Column int scm_emp) (emp_job : Column int scm_emp) (emp_mgr : Column int scm_emp) (emp_hiredate : Column int scm_emp) (emp_comm : Column int scm_emp) (emp_sal : Column int scm_emp) (emp_deptno : Column int scm_emp) (emp_slacker : Column int scm_emp) (ik1: isKey emp_empno rel_emp) (ik2: isKey dept_deptno rel_dept), 
    denoteSQL 
    ((SELECT1 (right⋅left⋅emp_ename) 
      (FROM1 (product (table rel_emp) (product (table rel_dept) (table rel_emp))) 
      WHERE (and (equal (uvariable (right⋅left⋅emp_deptno)) (uvariable (right⋅right⋅left⋅dept_deptno))) (equal (uvariable (right⋅left⋅emp_empno)) (uvariable (right⋅right⋅right⋅emp_empno)))))) : SQL Γ _ ) = 
    denoteSQL 
    ((SELECT1 (right⋅left⋅emp_ename) 
     (FROM1 (product (table rel_emp) (product (table rel_dept) (product (table rel_emp) (product (table rel_dept) (table rel_emp))))) 
    WHERE (and (and (and (equal (uvariable (right⋅left⋅emp_deptno)) (uvariable (right⋅right⋅left⋅dept_deptno))) (equal (uvariable (right⋅left⋅emp_empno)) (uvariable (right⋅right⋅right⋅left⋅emp_empno)))) (equal (uvariable (right⋅left⋅emp_deptno)) (uvariable (right⋅right⋅right⋅right⋅left⋅dept_deptno)))) (equal (uvariable (right⋅left⋅emp_empno)) (uvariable (right⋅right⋅right⋅right⋅right⋅emp_empno)))))): SQL Γ _ ) :=
begin
    intros,
    unfold_all_denotations,
    funext,
    simp,
    canonize,
  
end