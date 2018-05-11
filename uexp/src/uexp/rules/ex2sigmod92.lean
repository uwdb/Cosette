import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants
import ..UDP
import ..cosette_tactics


open Expr
open Proj
open Pred
open SQL

variable i1000 : const datatypes.int

theorem rule :
    forall (Γ scm_itm scm_itp : Schema)
           (rel_itm : relation scm_itm)
           (rel_itp : relation scm_itp)
           (itm_itemno : Column datatypes.int scm_itm)
           (itm_type : Column datatypes.int scm_itm)
           (itp_itemno : Column datatypes.int scm_itp)
           (itp_np : Column datatypes.int scm_itp)
           (ik : isKey itm_itemno rel_itm),
    denoteSQL
    (SELECT1 (combine (right⋅left⋅right)
                      (combine (right⋅right⋅itm_type)
                               (right⋅right⋅itm_itemno)))
     FROM1 (product (DISTINCT (SELECT1 (combine (right⋅itp_itemno)
                                                (right⋅itp_np))
                               FROM1 (table rel_itp)
                               WHERE (castPred (combine (right⋅itp_np)
                                                        (e2p (constantExpr i1000)))
                                               predicates.gt)))
                    (table rel_itm))
     WHERE (equal (uvariable (right⋅left⋅left))
                  (uvariable (right⋅right⋅itm_itemno))) : SQL Γ _) =
    denoteSQL
    (DISTINCT (SELECT1 (combine (right⋅left⋅itp_np)
                                (combine (right⋅right⋅itm_type)
                                         (right⋅right⋅itm_itemno)))
               FROM1 (product (table rel_itp)
                              (table rel_itm))
               WHERE (and (castPred (combine (right⋅left⋅itp_np)
                                             (e2p (constantExpr i1000)))
                                    predicates.gt)
                          (equal (uvariable (right⋅left⋅itp_itemno))
                                 (uvariable (right⋅right⋅itm_itemno))))) : SQL Γ _) :=
begin
    intros,
    unfold_all_denotations,
    funext,
    unfold pair,
    simp,
    sorry
end