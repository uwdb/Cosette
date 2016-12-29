Require Import HoTT.
Require Import UnivalenceAxiom.

Require Import HoTTEx.
Require Import Denotation.
Require Import UnivalentSemantics.
Require Import CQTactics.
Require Import AutoTactics.

Open Scope type.

Module MagicOptimization (T : Types) (S : Schemas T) (R : Relations T S)  (A : Aggregators T S).
  Import T S R A.
  Module SQL_TSRA := SQL T S R A.
  Import SQL_TSRA.
  Module CQTac := CQTactics T S R A.
  Import CQTac.

  Parameter integer : type.
  Parameter count : forall {T}, aggregator T integer.
  Notation "'COUNT' ( e )" := (aggregatorGroupByProj count e).

  Definition SelfJoin0 : Type.
    refine (forall (Γ : Schema) s (a : relation s), _).
    refine (⟦ Γ ⊢ (DISTINCT SELECT1 (right⋅left) FROM2 table a, table a) : _ ⟧ = 
            ⟦ Γ ⊢ (DISTINCT SELECT1 right FROM1 table a) : _ ⟧).
  Defined.
  Arguments SelfJoin0 /.

  Lemma selfJoin0 : SelfJoin0.
    conjunctiveQueryProof.
  Qed.
  (*Original Proof:
    start.
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried. 
    constructor.
    + intros u.
      strip_truncations.
      destruct u as [t0 [[a0 a1] p]].
      apply tr.
      destruct p.
      refine (fst t0; (a0, _)).
      reflexivity.
    + intros u.
      strip_truncations.
      destruct u as [t0 [a0 p]].
      destruct p.
      apply tr.
      refine ((t0, t0); _).
      refine (_, _); [|reflexivity].
      refine (a0, a0). 
  *)

  Definition SelfJoin1 : Type.
    refine (forall (Γ : Schema) s (a : relation s) ty (c0 : Column ty s), _).
    pose (@variable ty (Γ ++ s ++ s) (right⋅right⋅c0)) as v0.
    pose (@variable ty (Γ ++ s ++ s) (right⋅left⋅c0)) as v0'.
    refine (⟦ Γ ⊢ (DISTINCT SELECT1 right⋅right⋅c0 FROM2 table a, table a WHERE equal v0 v0') : _ ⟧ = 
            ⟦ Γ ⊢ (DISTINCT SELECT1 right⋅c0 FROM1 table a) : _ ⟧).
  Defined.
  Arguments SelfJoin1 /.

  Lemma selfJoin1 : SelfJoin1.
    conjunctiveQueryProof.
  Qed.
  (* Original Proof:
    start.
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor.
    + intros u.
      strip_truncations. 
      destruct u as [t0 [[p0 [a0 a1]] p]].
      apply tr.
      destruct p. 
      refine (fst t0; (a0, _)).
      rewrite p0.
      reflexivity.
    + intros u.
      strip_truncations.
      destruct u as [t0 [a0 p]].
      destruct p.
      apply tr.
      refine ((t0, t0); _).
      refine (_, _); [| reflexivity].
      refine (_, _); [reflexivity |].
      refine (a0, a0).
  *)

  Definition SelfJoin2 : Type.
    refine (forall (Γ : Schema) s (a : relation s) ty0 ty1 (c0: Column ty0 s) (c1 : Column ty1 s), _).
    pose (@variable ty0 (Γ ++ s ++ s) (right⋅right⋅c0)) as v0.
    pose (@variable ty0 (Γ ++ s ++ s) (right⋅left⋅c0)) as v0'.
    pose (@variable ty0 (Γ ++ s) (right⋅c0)) as v0''.
    pose (@variable ty1 (Γ ++ s ++ s) (right⋅right⋅c1)) as v1.
    pose (@variable ty1 (Γ ++ s ++ s) (right⋅left⋅c1)) as v1'.
    pose (@variable ty1 (Γ ++ s) (right⋅c1)) as v1''.
    refine (⟦ Γ ⊢ (DISTINCT SELECT2 v0 , v1 FROM2 table a, table a WHERE equal v0 v0' AND equal v1 v1') : _ ⟧ = 
            ⟦ Γ ⊢ (DISTINCT SELECT2 v0'', v1'' FROM1 table a) : _ ⟧).
  Defined.
  Arguments SelfJoin2 /.
    
  Lemma selfJoin2 : SelfJoin2.
    conjunctiveQueryProof.
  Qed.
  (* Original Proof:
    start. 
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried. 
    constructor.
    + intros u.
      strip_truncations.
      destruct u as [t0 [[[p0 p1] [a0 a1]] p]]. 
      apply tr.
      destruct p.
      refine (fst t0; (a0, _)).
      rewrite p1.
      rewrite p0.
      reflexivity.
    + intros u.
      strip_truncations.
      destruct u as [t0 [a0 p]].
      destruct p. 
      apply tr.
      refine ((t0, t0); _).
      refine (_, _); [| reflexivity].
      refine ((_,_), _); [reflexivity|reflexivity| ].
      refine (a0, a0).
   *)

  (*
   Push θ-semijoin through aggregation.
   =========================================
   ```SQL
   SELECT *
   FROM (SELECT E1.a, COUNT(E1.b) as cb FROM E1 GROUP BY E1.a) C
   WHERE EXISTS (SELECT * FROM E2 WHERE E2.a = C.a)
   ```
   can be rewritten to

   ```SQL
   SELECT C.a, COUNT(C.b)
   FROM (SELECT *
         FROM E1
         WHERE EXISTS (E1.a = SELECT E2.a as a FROM E2)
        ) C 
   GROUP BY C.a
   ``` 
   *)
  Definition PushSemiJoinThrAgg : Type.
    refine (forall (Γ : Schema) s1 s2 (e1: SQL Γ s1) (e2: SQL Γ s2) ta (a1: Column ta s1) (a2: Column ta s2) tb (b1: Column tb s1), _).
    pose (@variable ta (Γ ++ s1) (right⋅a1)) as a1'.
    pose (@variable tb (Γ ++ s1) (right⋅b1)) as b1'.
    refine (⟦ Γ ⊢ (SELECT (combineGroupByProj PLAIN(a1') COUNT(b1')) FROM1 e1 GROUP BY (right⋅a1))
                  SEMI_JOIN1 e2 ON SEQ left, a2: _ ⟧
            =
            ⟦ Γ ⊢ (SELECT (combineGroupByProj PLAIN(a1') COUNT(b1'))
                  FROM1 (e1 SEMI_JOIN1 e2 ON SEQ a1, a2 )
                  GROUP BY (right⋅a1)) : _ ⟧).
  Defined.
  
  Arguments PushSemiJoinThrAgg /.

  Lemma pushSemiJoinThrAgg: PushSemiJoinThrAgg.
    start.
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor. 
    + intros [x y].
      strip_truncations.
      destruct y as [ty [z a]].
      destruct x as [tx [q p]].
      apply tr.
      rewrite <- a in q.
      cbn in q.
      refine (ty; ((_, z), _)). 
      - apply tr.
        refine (tx; (q, p)).
      - rewrite <- a.
        repeat f_ap.
        by_extensionality t'.
        f_ap.
        by_extensionality t0.
        rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
        match goal with
        | |- ?X * ?Y * ?Z * _ = _ => assert (X*Y = X) as eqp
        end.
        * apply path_universe_uncurried.
          apply equiv_iff_hprop_uncurried.
          constructor.
          { intros [fst snd].
            exact fst. }
          { intro f.
            refine (f, _).
            apply tr.
            refine (tx; (_, p)).
            rewrite q in f.
            symmetry.
            exact f. }
        * rewrite eqp.
          reflexivity.
    + intros x.
      strip_truncations.
      destruct x as [t0 [[c d] f]].
      strip_truncations.
      destruct c as [t1 [h i]].
      refine (tr _, tr _).
      - refine (t1; (_, i)).
        rewrite <- f.
        cbn.
        exact h.
      - refine (t0; (d, _)).
        rewrite <- f.
        repeat f_ap.
        by_extensionality t'.
        f_ap.
        by_extensionality t2.
        rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
        match goal with
        | |- _ = ?X * ?Y * _ * _ => assert(X * Y = X) as eqp
        end.
        * apply path_universe_uncurried.
          apply equiv_iff_hprop_uncurried.
          constructor.
          { intros [a b].
            exact a. }
          { intros a.
            refine (a, _).
            apply tr.
            refine (t1; (_, i)).
            rewrite h in a.
            symmetry.
            exact a. }
        * rewrite eqp.
          reflexivity.
  Qed.
  
  Definition θ_SemiJoinIntro: Type.
    refine (forall (Γ s1 s2: Schema) (e1: SQL Γ s1) (e2: SQL Γ s2)
              (θ: Pred (Γ ++ s2 ++ s1)), _).
    refine ( ⟦ Γ ⊢ (SELECT * FROM2 e2, e1 WHERE θ ) : _ ⟧ =
             ⟦ Γ ⊢ (SELECT * FROM2 (e2 SEMI_JOIN e1 ON θ), e1 WHERE θ) : _ ⟧).
  Defined.

  Arguments θ_SemiJoinIntro /.

  Lemma θ_semiJoinIntro: θ_SemiJoinIntro.
    start.
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    f_ap.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    apply path_universe_uncurried.
    apply hprop_prod_l'.
    intros [h0 h1].
    apply tr.
    destruct t as [t1 t2].
    refine (t2; _).
    cbn in *.
    refine (h1, h0). 
  Qed.
 
  (* Introduction of θ-semijoin. *)
  Definition θ_SemiJoinIntro': Type.
    refine (forall (Γ s1 s2: Schema) ty (e1: SQL Γ s1) (e2: SQL Γ s2)
              (a1: Column ty s1) (a2: Column ty s2), _).
    pose (@variable ty (Γ ++ s1 ++ s2) (right⋅left⋅a1)) as a1'.
    pose (@variable ty (Γ ++ s1 ++ s2) (right⋅right⋅a2)) as a2'.
    refine (⟦Γ ⊢ (SELECT * FROM2 e1, e2 WHERE equal a1' a2' ) : _ ⟧
            =
            ⟦Γ ⊢ (SELECT * FROM2 e1, (e2 SEMI_JOIN1 e1 ON SEQ a2, a1)
                  WHERE equal a1' a2' ): _ ⟧ ).
  Defined.

  Arguments θ_SemiJoinIntro' /.

  Lemma θ_semiJoinIntro': θ_SemiJoinIntro'.
    start.
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    f_ap.
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    apply path_universe_uncurried.
    apply hprop_prod_l'.
    intros [h0 h1].
    apply tr.
    destruct t as [t1 t2].
    refine (t1; _).
    cbn in *.
    symmetry in h0.
    refine (h0, h1).
  Qed.

  (* Push θ-semijoin through join. *)
  Definition push_θ_semiJoinThroughJoin: Type.
    refine (forall (Γ s1 s2 s3: Schema) (e1: SQL Γ s1) (e2: SQL Γ s2)
              (e3: SQL Γ s3) (θ1: Pred (Γ ++ s1 ++ s2))
              (θ2: Pred (Γ ++ (s1 ++ s2) ++ s3)), _).
    refine (⟦ Γ ⊢ (SELECT * FROM2 e1, e2 WHERE θ1) SEMI_JOIN e3 ON θ2 : _  ⟧
            =
            ⟦ Γ ⊢ (SELECT *
                   FROM2 e1,
                   (e2 SEMI_JOIN (SELECT * FROM2 e1, e3 ) ON
                       and (castPred _ θ1) (castPred _ θ2))
                   WHERE θ1) SEMI_JOIN
                   e3 ON θ2 : _
           ⟧).
    refine (combine left (combine (right⋅right⋅left) (right⋅left))).
    refine (combine left (combine (combine (right⋅right⋅left) (right⋅left)) (right⋅right⋅right))).
  Defined.

  Arguments push_θ_semiJoinThroughJoin /.

  Lemma Push_θ_semiJoinThroughJoin : push_θ_semiJoinThroughJoin.
    start.
    symmetry.
    repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    match goal with
      |- ?A1 * ?A2 * ?A3 * ?A4 * ?A5 = _
      => assert (A1 * A2 * A3 * A5 -> A4) as H; revgoals
    end.
    + specialize (hprop_prod_l' H).
      match goal with
        |- ?X <~> ?Y -> ?Z => assert (X=Y) as eqx
      end.
      { apply path_universe_uncurried.
        exact (hprop_prod_l' H). }
      { intro eqy.
        clear eqy.
        clear H.
        rewrite <- eqx.
        repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _ )).
        f_ap.
        rewrite (path_universe_uncurried (equiv_prod_symm _ _ )).
        repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _ )).
        reflexivity. }
    + intros [[[p1 n1] n2] n3].
      strip_truncations.
      destruct p1 as [t1 [t2 p1]].
      apply tr.
      destruct t as [ts1 ts2].
      refine ((ts1, t1); _).
      cbn in *.
      refine (n1, p1, (n2, t2)).
  Qed.
  
End MagicOptimization.
