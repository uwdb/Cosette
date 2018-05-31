import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants
import ..meta.ucongr
import ..meta.TDP
import ..meta.cosette_tactics


-- NOTE: this one cannot solved by ucongr, need to be revisited

open Expr
open Proj
open Pred
open SQL
open binary_operators

theorem rule :
    forall (Γ s1 : Schema) (a : relation s1)
           (x : Column datatypes.int s1) (y : Column datatypes.int s1),
           denoteSQL (SELECT1 (e2p (binaryExpr add_ (uvariable (right⋅x)) (uvariable (right⋅x))))
                      FROM1 (table a WHERE (equal (uvariable (right⋅x)) (uvariable (right⋅y)))) : SQL Γ _) =
           denoteSQL (SELECT1 (e2p (binaryExpr add_ (uvariable (right⋅x)) (uvariable (right⋅y))))
                      FROM1 (table a WHERE (equal (uvariable (right⋅x)) (uvariable (right⋅y)))) : SQL Γ _) :=
begin
    intros,
    funext,
    unfold_all_denotations,
    simp,
    congr,
    funext,
    apply congr_arg _,
    have eq_subst_l' : ∀ {s: Schema} (t₁ t₂: Tuple s) (R: Tuple s → Tuple s) (e : Tuple s), (t₁ ≃ t₂) * (e ≃ R t₁) = (t₁ ≃ t₂) * (e ≃ R t₂),
    { intros, rw eq_subst_l },
    rewrite eq_subst_l',
end