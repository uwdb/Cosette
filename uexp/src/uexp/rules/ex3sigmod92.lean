import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants

open Expr
open Proj
open Pred
open SQL

variables i0 i468 : const datatypes.int

open tactic

meta def is_key_type (e : expr) : bool :=
    do let fn := expr.get_app_fn e,
    match fn with
    | (expr.const n _) := n = `isKey
    | _ := bool.ff
    end

meta def find_keys : tactic (list expr) :=
    do hyps ← local_context, 
       hyp_types ← monad.mapm infer_type hyps,
       let pairs := list.filter (fun (p: expr × expr), is_key_type p.snd = bool.tt) (list.zip hyps hyp_types),
       return $ (list.unzip pairs).fst

meta def try_me : tactic unit := do 
    ks ← find_keys,
    trace ks

theorem rule :
    forall (Γ scm_itl scm_itp : Schema)
           (rel_itl : relation scm_itl)
           (rel_itp : relation scm_itp)
           (itl_itemn : Column datatypes.int scm_itl)
           (itl_wkcen : Column datatypes.int scm_itl)
           (itl_locan : Column datatypes.int scm_itl)
           (itp_itemn : Column datatypes.int scm_itp)
           (itp_ponum : Column datatypes.int scm_itp)
           (ik: isKey itp_itemn rel_itp),
    denoteSQL
    (SELECT *
     FROM1 table rel_itp
     WHERE (EXISTS (SELECT *
                    FROM1 table rel_itl
                    WHERE (and (and (equal (uvariable (right⋅itl_itemn))
                                           (uvariable (left⋅right⋅itp_itemn)))
                                    (equal (uvariable (right⋅itl_wkcen))
                                           (constantExpr i468)))
                               (equal (uvariable (right⋅itl_locan))
                                      (constantExpr i0))))) : SQL Γ _) =
    denoteSQL
    (DISTINCT (SELECT1 (right⋅left⋅star)
               FROM1 (product (table rel_itp)
                              (table rel_itl))
               WHERE (and (and (equal (uvariable (right⋅left⋅itp_itemn))
                                      (uvariable (right⋅right⋅itl_itemn)))
                               (equal (uvariable (right⋅right⋅itl_wkcen))
                                      (constantExpr i468)))
                          (equal (uvariable (right⋅right⋅itl_locan))
                                 (constantExpr i0)))) : SQL Γ _) :=
begin
    intros,
    unfold isKey at *,
    try_me,
    sorry
end