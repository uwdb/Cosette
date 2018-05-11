import ..u_semiring
import ..sql
import ..cosette_tactics

open SQL
open Pred
open Expr
open Proj

lemma CQExample0:
    forall Γ s1 s2 (a: SQL Γ s1) (b: SQL Γ s2)
              ty0 ty1 (x: Column ty0 s1)
              (ya: Column ty1 s1) (yb: Column ty1 s2),
    denoteSQL ((DISTINCT (SELECT1 (right⋅left⋅x) (FROM1 (product a b) 
                WHERE (equal (uvariable (right⋅left⋅ya)) (uvariable (right⋅right⋅yb)))))) : SQL Γ _) =
    denoteSQL ((DISTINCT (SELECT1 (right⋅left⋅left⋅x) 
                (FROM1 (product (product a a) b)
                 WHERE (and (equal (uvariable (right⋅left⋅left⋅x)) (uvariable (right⋅left⋅right⋅x)))
                            (equal (uvariable (right⋅left⋅left⋅ya)) (uvariable (right⋅right⋅yb))))))) : SQL Γ  _ ) :=
begin
    intros,
    unfold_all_denotations,
    funext,
    simp,
    sorry -- TODO: SDP should be used here
end
