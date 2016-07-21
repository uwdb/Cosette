Require Import HoTT.
Require Import UnivalenceAxiom.

Require Import HoTTEx.
Require Import Denotation.
Require Import UnivalentSemantics.

Open Scope type.

Module RewriteOptimization (T : Types) (S : Schemas T) (R : Relations T S) (A : Aggregators T S).
  Import T S R A.
  Module SQL_TSRA := SQL T S R A.
  Import SQL_TSRA.

  Lemma selectRewrite Γ s a slct0 slct1 : 
    ⟦ slct0 ⟧ = ⟦ slct1 ⟧ -> 
    ⟦ Γ ⊢ (SELECT * FROM1 a WHERE slct0) : s ⟧ =
    ⟦ Γ ⊢ (SELECT * FROM1 a WHERE slct1) : s ⟧.
  Proof.
    cbn.
    intro e.
    rewrite e.
    reflexivity.
  Qed.

End RewriteOptimization.
