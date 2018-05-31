/-
⟦ Γ ⊢ (SELECT  (combineGroupByProj PLAIN(uvariable (right⋅emp_job)) (combineGroupByProj PLAIN(uvariable (right⋅emp_empno)) (combineGroupByProj PLAIN(uvariable (right⋅emp_sal)) (SUM(uvariable (right⋅emp_sal)))))) FROM1  (table rel_emp) WHERE (equal (uvariable (right⋅emp_empno)) (constantExpr integer_10)) GROUP BY  (combine (right⋅emp_job) (combine (right⋅emp_empno) (right⋅emp_sal)))) : _ ⟧
⟦ Γ ⊢ (SELECT  (combineGroupByProj PLAIN(uvariable (right⋅emp_job)) (combineGroupByProj PLAIN(uvariable (e2p (constantExpr integer_10))) (combineGroupByProj PLAIN(uvariable (right⋅emp_sal)) (SUM(uvariable (right⋅emp_sal)))))) FROM1  (table rel_emp) WHERE (equal (uvariable (right⋅emp_empno)) (constantExpr integer_10)) GROUP BY  (combine (right⋅emp_job) (right⋅emp_sal))) : _ ⟧
-/

import ..extra_constants
import ..sql
import ..u_semiring
import ..meta.cosette_tactics

open SQL
open Proj
open Pred
open Expr

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
    denoteSQL (SELECT (combineGroupByProj PLAIN(uvariable (right⋅emp_job))
                        (combineGroupByProj PLAIN(uvariable (right⋅emp_empno))
                            (combineGroupByProj PLAIN(uvariable (right⋅emp_sal))
                                                SUM(uvariable (right⋅emp_sal)))))
               FROM1 (table rel_emp
                      WHERE (Pred.equal (uvariable (right⋅emp_empno)) (constantExpr i)))
               GROUP BY (combine (right⋅emp_job) (combine (right⋅emp_empno) (right⋅emp_sal))) : SQL Γ _) =
    denoteSQL (SELECT (combineGroupByProj PLAIN(uvariable (right⋅emp_job))
                        (combineGroupByProj PLAIN(uvariable (e2p (constantExpr i)))
                            (combineGroupByProj PLAIN(uvariable (right⋅emp_sal))
                                                SUM(uvariable (right⋅emp_sal)))))
               FROM1 (table rel_emp
                      WHERE (Pred.equal (uvariable (right⋅emp_empno)) (constantExpr i)))
               GROUP BY (combine (right⋅emp_job) (right⋅emp_sal)) : SQL Γ _) :=
begin
    intros,
    unfold_all_denotations,
    funext,
    simp,
    sorry
end