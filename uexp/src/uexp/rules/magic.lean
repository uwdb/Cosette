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

variable integer_10: const datatypes.int

lemma IndexQ0: 
    forall Γ r (R: relation r) t0 (l: const t0)
              (a: Column t0 r) t1 (k: Column t1 r) (ik: isKey k R),
    denoteSQL ((SELECT * FROM1  (table R)
                       WHERE equal (uvariable (right⋅a)) (constantExpr l)): SQL Γ _) =
    denoteSQL ((project (right⋅right) (FROM1 (product (Index (@table Γ r R) k a) (table R))
                       WHERE and (equal (uvariable (right⋅left⋅right⋅left⋅star)) (constantExpr l))
                    (equal (uvariable (right⋅left⋅left⋅star)) (uvariable (right⋅right⋅k))) )) :SQL Γ _) :=
begin
  delta Index,
  intros,
  delta select2,
  delta projectCons,
  unfold_all_denotations,
  funext,
  unfold pair,
  simp,
  try_me,
  --unfold isKey at ik,
  apply ueq_symm,
  remove_dup_sigs,
  dsimp,
  remove_dup_sigs,
  dsimp,
  remove_dup_sigs,
  canonize,
  remove_dup_sigs,
  ac_refl
end

/-
(∑ (x : Tuple empty) (x_1 : Tuple r),
    denote_r R t *
      (denote_r R x_1 *
        ((denoteProj k t≃denoteProj k x_1) *
          ((x≃denoteProj projectNil (g, x_1)) *
           (denote_c l≃denoteProj a x_1)))))
-/