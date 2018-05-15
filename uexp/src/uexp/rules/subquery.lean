import ..sql
import ..tactics
import ..u_semiring
import ..extra_constants
import ..ucongr
import ..TDP

set_option profiler true

open Expr
open Proj
open Pred
open SQL
open tree

notation `int` := datatypes.int

-- TODO: this should be easily solvable
lemma inlineCorrelatedSubquery :
    forall (Γ s: Schema) (a : relation s) ty (c : Column ty s), 
    denoteSQL 
    ((SELECT * FROM1 (table a) 
      WHERE 
      (EXISTS 
      (SELECT * 
      (FROM1 (table a) WHERE (equal (uvariable (left⋅right⋅c)) (uvariable (right⋅c))))))) : SQL Γ s) 
      = 
    denoteSQL 
    ((SELECT * FROM1 (table a)) : SQL Γ s) :=
begin
    intros,
    unfold_all_denotations,
    funext,
    simp,
    sorry
end    
  
lemma pullUpSubqueryInFrom : 
    forall Γ (s1 s2: Schema) (a : SQL Γ s1) (b: SQL Γ s2) (slct1: Pred (Γ ++ (s1 ++ s2))) (slct0: Pred (Γ ++ s2)), 
    denoteSQL 
    ((SELECT * 
     FROM1 ((product a (SELECT * FROM1 b WHERE slct0)) WHERE (slct1))): SQL Γ _ ) =
    denoteSQL ((SELECT * FROM1 (product a b) WHERE (and slct1 (castPred (combine left (right⋅right)) slct0))) : SQL Γ _) :=
begin
    intros,
    unfold_all_denotations,
    funext,
    simp,
    ucongr,
end