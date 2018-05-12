import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants
import ..cosette_tactics


open Expr
open Proj
open Pred
open SQL

variables i1 i20 i85 : const datatypes.int

theorem rule :
    forall (Γ scm_pur scm_itm scm_itp : Schema)
           (rel_pur : relation scm_pur)
           (rel_itm : relation scm_itm)
           (rel_itp : relation scm_itp)
           (pur_ponum : Column datatypes.int scm_pur)
           (pur_odate : Column datatypes.int scm_pur)
           (pur_vendn : Column datatypes.int scm_pur)
           (itm_itemn : Column datatypes.int scm_itm)
           (itm_type : Column datatypes.int scm_itm)
           (itp_itemn : Column datatypes.int scm_itp)
           (itp_ponum : Column datatypes.int scm_itp)
           (ik : isKey itm_itemn rel_itm),
    denoteSQL
    (SELECT1 (combine (right⋅left⋅itm_itemn)
                      (right⋅right⋅right))
     FROM1 (product (table rel_itm)
                    (DISTINCT (SELECT1 (combine (right⋅left⋅itp_itemn)
                                                (right⋅right⋅pur_vendn))
                               FROM1 (product (table rel_itp)
                                              (table rel_pur))
                               WHERE (and (equal (uvariable (right⋅left⋅itp_ponum))
                                                 (uvariable (right⋅right⋅pur_ponum)))
                                          (castPred (combine (right⋅right⋅pur_odate)
                                                             (e2p (constantExpr i85)))
                                                    predicates.gt)))))
     WHERE (and (and (equal (uvariable (right⋅left⋅itm_itemn))
                            (uvariable (right⋅right⋅left)))
                     (castPred (combine (right⋅left⋅itm_itemn)
                                        (e2p (constantExpr i1)))
                               predicates.gt))
                (castPred (combine (e2p (constantExpr i20))
                                   (right⋅left⋅itm_itemn))
                          predicates.gt)) : SQL Γ _) = 
    denoteSQL
    (DISTINCT (SELECT1 (combine (right⋅left⋅itm_itemn)
                                (right⋅right⋅right⋅pur_vendn))
               FROM1 (product (table rel_itm)
                              (product (table rel_itp)
                                       (table rel_pur)))
               WHERE (and (and (and (and (equal (uvariable (right⋅right⋅left⋅itp_ponum))
                                                (uvariable (right⋅right⋅right⋅pur_ponum)))
                                         (equal (uvariable (right⋅left⋅itm_itemn))
                                                (uvariable (right⋅right⋅left⋅itp_itemn))))
                                    (castPred (combine (right⋅right⋅right⋅pur_odate)
                                                       (e2p (constantExpr i85)))
                                              predicates.gt))
                               (castPred (combine (right⋅left⋅itm_itemn)
                                                  (e2p (constantExpr i1)))
                                         predicates.gt))
                          (castPred (combine (e2p (constantExpr i20))
                                             (right⋅left⋅itm_itemn))
                                    predicates.gt))) : SQL Γ _) :=
begin
    intros,
    unfold_all_denotations,
    funext,
    unfold pair,
    simp,
    sorry
end