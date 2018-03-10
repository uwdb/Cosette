import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants

open Expr
open Proj
open Pred
open SQL

theorem rule :
    forall (Γ scm_itm scm_itp : Schema)
           (rel_itm : relation scm_itm)
           (rel_itp : relation scm_itp)
           (itm_itemno : Column datatypes.int scm_itm)
           (itm_type : Column datatypes.int scm_itm)
           (itp_itemno : Column datatypes.int scm_itp)
           (itp_np : Column datatypes.int scm_itp)
           (ik: isKey itm_itemno rel_itm),
    denoteSQL
    (SELECT1 (combine (right⋅right⋅itm_itemno)
                      (right⋅left⋅right))
     FROM1 (product (DISTINCT (SELECT1 (combine (right⋅itp_itemno)
                                                (right⋅itp_np))
                               FROM1 (table rel_itp)))
                    (table rel_itm))
     WHERE (equal (uvariable (right⋅left⋅left))
                  (uvariable (right⋅right⋅itm_itemno))) : SQL Γ _) =
    denoteSQL
    (DISTINCT (SELECT1 (combine (right⋅right⋅itm_itemno)
                                (right⋅left⋅itp_np))
               FROM1 (product (table rel_itp)
                              (table rel_itm))
               WHERE (equal (uvariable (right⋅left⋅itp_itemno))
                            (uvariable (right⋅right⋅itm_itemno)))) : SQL Γ _) :=
begin
admit
end