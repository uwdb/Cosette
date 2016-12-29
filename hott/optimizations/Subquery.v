Require Import HoTT.
Require Import UnivalenceAxiom.

Require Import HoTTEx.
Require Import Denotation.
Require Import UnivalentSemantics.
Require Import AutoTactics.

Open Scope type.

Module SubqueryOptimization (T : Types) (S : Schemas T) (R : Relations T S)  (A : Aggregators T S).
  Import T S R A.
  Module SQL_TSRA := SQL T S R A.
  Import SQL_TSRA.
  Module AutoTac := AutoTactics T S R A.
  Import AutoTac.

  Definition InlineCorrelatedSubquery : Type.
    refine (forall (Γ s: Schema) (a : relation s) ty (c : Column ty s), _).
    pose (@variable ty ((Γ ++ s) ++ s) (left⋅right⋅c)) as v0.
    pose (@variable ty ((Γ ++ s) ++ s) (right⋅c)) as v1.
    refine (⟦ Γ ⊢ (SELECT * FROM1 table a WHERE (EXISTS (SELECT * FROM1 table a WHERE (equal v0 v1)))) : s ⟧ = 
            ⟦ Γ ⊢ (SELECT * FROM1 table a) : s ⟧); revgoals.
  Defined.
  Arguments InlineCorrelatedSubquery /. 

  Lemma inlineCorrelatedSubquery : InlineCorrelatedSubquery.
    solve_summation.
    
  Defined.
  
  (* 
  Pull up subqueries in FROM clause. Query before:
     SELECT *
     FROM A, (SELECT * FROM B WHERE <p>) as C
     WHERE slct
  Query after:
     SELECT *
     FROM A, B
     WHERE slct AND <p'>
  One thing that needs noticing is that <p> and <p'> are on different context
   *)
  Definition PullUpSubqueryInFrom : Type.
    refine (forall Γ (s1 s2: Schema) (a : SQL Γ s1) (b: SQL Γ s2)
                (slct1: Pred (Γ ++ s1 ++ s2)) 
                (slct0: Pred (Γ ++ s2)), 
        ⟦Γ ⊢ (SELECT * FROM2 a, (SELECT * FROM1 b WHERE slct0 ) WHERE slct1 ): _ ⟧ =
        ⟦Γ ⊢ (SELECT * FROM2 a, b WHERE slct1 AND _ slct0) : _ ⟧).
    refine (castPred (combine left (right⋅right))).
  Defined.
  
  Arguments PullUpSubqueryInFrom /.
   
  Lemma pullUpSubqueryInFrom : PullUpSubqueryInFrom.
    hott_ring. 
  Qed.
End SubqueryOptimization.
