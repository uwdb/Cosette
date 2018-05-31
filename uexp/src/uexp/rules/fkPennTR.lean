import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants
import ..meta.cosette_tactics


open Expr
open Proj
open Pred
open SQL

variable str_security_ : const datatypes.int

theorem rule :
    forall (Γ scm_payroll scm_teams scm_depts : Schema)
           (rel_payroll : relation scm_payroll)
           (rel_teams : relation scm_teams)
           (rel_depts : relation scm_depts)
           (payroll_pdept : Column datatypes.int scm_payroll)
           (payroll_empl : Column datatypes.int scm_payroll)
           (teams_tproj : Column datatypes.int scm_teams)
           (teams_tmember : Column datatypes.int scm_teams)
           (depts_dname : Column datatypes.int scm_depts)
           (depts_dproj : Column datatypes.int scm_depts)
           (k : isKey payroll_empl rel_payroll)
           (fk : fKey payroll_empl teams_tmember rel_payroll rel_teams k),
    denoteSQL
    (SELECT1 (right⋅right⋅teams_tmember)
     FROM1 (product (table rel_depts) (table rel_teams))
     WHERE (and (equal (uvariable (right⋅left⋅depts_dproj))
                       (uvariable (right⋅right⋅teams_tproj)))
                (equal (uvariable (right⋅left⋅depts_dname))
                       (constantExpr str_security_))) : SQL Γ _) =
    denoteSQL
    (SELECT1 (right⋅left⋅right⋅right)
     FROM1 (product ((SELECT1 (combine (right⋅left⋅depts_dname)
                              (combine (right⋅left⋅depts_dproj)
                                       (right⋅right⋅payroll_empl)))
                      FROM1 (product (table rel_depts)
                                     (table rel_payroll))
                      WHERE (equal (uvariable (right⋅left⋅depts_dname))
                                   (uvariable (right⋅right⋅payroll_pdept)))))
                    ((SELECT1 (combine (right⋅left⋅teams_tmember)
                              (combine (right⋅right⋅payroll_pdept)
                                       (right⋅left⋅teams_tproj)))
                      FROM1 (product (table rel_teams)
                                     (table rel_payroll))
                      WHERE (equal (uvariable (right⋅left⋅teams_tmember))
                                   (uvariable (right⋅right⋅payroll_empl))))))
     WHERE (and (and (and (equal (uvariable (right⋅left⋅left))
                                 (constantExpr str_security_))
                          (equal (uvariable (right⋅left⋅right⋅left))
                                 (uvariable (right⋅right⋅right⋅right))))
                     (equal (uvariable (right⋅left⋅right⋅right))
                            (uvariable (right⋅right⋅left))))
                (equal (uvariable (right⋅left⋅left))
                       (uvariable (right⋅right⋅right⋅left)))) : SQL Γ _) :=
begin
admit
end