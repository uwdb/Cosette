Require Import HoTT.
Require Import UnivalenceAxiom.

Require Import HoTTEx.
Require Import Denotation.
Require Import UnivalentSemantics.

Open Scope type.

Module AggregationOptimization (T : Types) (S : Schemas T) (R : Relations T S)  (A : Aggregators T S).
  Import T S R A.
  Module SQL_TSRA := SQL T S R A.
  Import SQL_TSRA.

  Parameter integer : type.
  Parameter count : forall {T}, aggregator T integer.
  Notation "'COUNT' ( e )" := (aggregatorGroupByProjection count e).
  
  Definition AggregationQuery : Type.
    refine (forall (Γ : Schema) s (a : relation s) C0 (value : Column C0 s) C1 (label: Column C1 s) (l : constant C1), _).
    pose (@variable C1 (Γ ++ s) (right⋅label)) as lbl.
    pose (@variable C0 (Γ ++ s) (right⋅value)) as val.
    pose  (@variable C1 (Γ ++ singleton C1 ++ singleton integer ++ empty) (right⋅left⋅star)) as lbl'. 
    refine (⟦ Γ ⊢ (SELECT *
                  FROM1
                  (SELECT PLAIN(lbl), COUNT(val) FROM1 table a GROUP BY label ) 
                  WHERE equal lbl' (constantExpr l)) : _ ⟧ = 
            ⟦ Γ ⊢ SELECT PLAIN(lbl), COUNT(val)
                  FROM1 table a
                  WHERE equal lbl (constantExpr l) 
                  GROUP BY label : _ ⟧).
  Defined.
  Arguments AggregationQuery /.
  
  Lemma aggregationQuery : AggregationQuery. 
    cbn.  
    by_extensionality g.
    by_extensionality t.
    apply path_universe_uncurried.  
    apply equiv_iff_hprop_uncurried.
    constructor.
    + intros [p u].  
      strip_truncations.
      destruct u as [t0 [a0 u]].
      apply tr.
      rewrite <- u in p.
      refine (t0; (_,  _)).      
      * refine (_, a0).
        assumption. 
      * rewrite <- u.
        rewrite p.
        repeat f_ap.
        by_extensionality t'.
        f_ap.
        by_extensionality t1.
        rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
        repeat f_ap.
        rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
        apply path_universe_uncurried.
        apply hprop_prod_l'.
        intros.
        symmetry.
        assumption.
    + intros p.
      strip_truncations.
      destruct p as [t0 [[c d] e]].
      rewrite <- e.
      cbn.
      constructor; try apply tr; try assumption.
      refine (t0; (d, _)).
      repeat f_ap.
      by_extensionality t'.
      f_ap.
      by_extensionality t1.
      rewrite <- c.
      f_ap.
      rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
      f_ap.
      rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
      symmetry.
      apply path_universe_uncurried.
      apply hprop_prod_l'.
      intros.
      symmetry.
      assumption.
  Qed.
  
End AggregationOptimization.

