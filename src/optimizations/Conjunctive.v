Require Import HoTT.
Require Import UnivalenceAxiom.

Require Import HoTTEx.
Require Import Denotation.
Require Import UnivalentSemantics.
Require Import CQTactics.

Open Scope type.

Module ConjuctiveQuery (T : Types) (S : Schemas T) (R : Relations T S)  (A : Aggregators T S).
  Import T S R A.
  Module SQL_TSRA := SQL T S R A.
  Import SQL_TSRA.
  Module CQTac := CQTactics T S R A.
  Import CQTac.
  
  Definition CQExample0 : Type.
    refine (forall Γ s1 s2 (a: SQL Γ s1) (b: SQL Γ s2)
              ty0 ty1 (x: Column ty0 s1)
              (ya: Column ty1 s1) (yb: Column ty1 s2), _ ).
    pose (@variable _ (Γ ++ s1 ++ s2) (right⋅left⋅ya)) as ya'.
    pose (@variable _ (Γ ++ s1 ++ s2) (right⋅right⋅yb)) as yb'.
    pose (@variable _ (Γ ++ (s1 ++ s1) ++ s2) (right⋅left⋅left⋅x)) as x1'.
    pose (@variable _ (Γ ++ (s1 ++ s1) ++ s2) (right⋅left⋅right⋅x)) as x2'.
    pose (@variable _ (Γ ++ (s1 ++ s1) ++ s2) (right⋅left⋅left⋅ya)) as y1'.
    pose (@variable _ (Γ ++ (s1 ++ s1) ++ s2) (right⋅right⋅yb)) as y2'.
    refine (⟦ Γ ⊢ (DISTINCT SELECT1 right⋅left⋅x FROM a, b WHERE equal ya' yb') : _ ⟧ =
            ⟦ Γ ⊢ (DISTINCT SELECT1 right⋅left⋅left⋅x FROM a, a, b
                            WHERE and (equal x1' x2') (equal y1' y2') ) : _ ⟧).
  Defined.

  Arguments CQExample0 /.

  Lemma CQExample0Proof : CQExample0.
    conjuctiveQueryProof.
  Qed.
  
  Definition CQExample1 : Type.
    refine (forall Γ s1 (a: SQL Γ s1) ty (x: Column ty s1)
              (y: Column ty s1) (z: Column ty s1), _).
    refine (⟦ Γ ⊢ (DISTINCT SELECT *
                   FROM1 a
                   WHERE and      
                   (equal (variable (right⋅x)) (variable (right⋅y)))
                   (equal (variable (right⋅y)) (variable (right⋅z))))
             : _ ⟧
            =
            ⟦ Γ ⊢ (DISTINCT SELECT *
                   FROM1 a
                   WHERE and
                   (equal (variable (right⋅x)) (variable (right⋅z)))
                   (equal (variable (right⋅x)) (variable (right⋅y))))
              : _ ⟧).
  Defined.

  Arguments CQExample1 /.

  Lemma CQExample1Proof : CQExample1.
    conjuctiveQueryProof.
  Qed.
 
End ConjuctiveQuery.