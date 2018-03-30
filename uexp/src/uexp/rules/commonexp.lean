import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants

open Expr
open Proj
open Pred
open SQL
open binary_operators

theorem rule :
    forall (Γ s1 : Schema) (a : relation s1)
           (x : Column datatypes.int s1) (y : Column datatypes.int s1),
           let xVar : Expr (Γ ++ s1) _ := uvariable (right⋅x),
               yVar : Expr (Γ ++ s1) _ := uvariable (right⋅y) in
           denoteSQL (SELECT1 (e2p (binaryExpr add xVar xVar))
                      FROM1 (table a WHERE (equal xVar yVar)) : SQL Γ _) =
           denoteSQL (SELECT1 (e2p (binaryExpr add xVar yVar))
                      FROM1 (table a WHERE (equal xVar yVar)) : SQL Γ _) :=
begin
    intros,
    funext,
    unfold_all_denotations,
    simp,
    congr,
    funext,
    apply congr_arg _,
    have eq_subst_l' : ∀ {s: Schema} (t₁ t₂: Tuple s) (R: Tuple s → Tuple s) (e : Tuple s), (t₁ ≃ t₂) * (R t₁ ≃ e) = (t₁ ≃ t₂) * (R t₂ ≃ e),
    { intros, rw eq_subst_l },
    rw eq_subst_l',
    --rw eq_subst_l (denoteProj x t) (denoteProj y t) _,-- (λ k, (denote_b add (denoteProj x t) k) ≃ t')   
end