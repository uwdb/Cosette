Require Import HoTT.
Require Import UnivalenceAxiom.

Require Import HoTTEx.
Require Import Denotation.
Require Import UnivalentSemantics.

Open Scope type.

Module Index (T : Types) (S : Schemas T) (R : Relations T S)  (A : Aggregators T S).

  Import T S R A.
  Module SQL_TSRA := SQL T S R A.
  Import SQL_TSRA.

  Definition Index {s t0 t1} (R: SQL empty s) (k: Column t0 s) (ic: Column t1 s) :=
    SELECT2 (variable (right⋅k)), (variable (right⋅ic)) FROM1 R.

  
  Definition isUnique {s τ} (k: Column τ s) (R: SQL empty s) :=
    forall t, denoteSQL R tt t -> ⟦ empty ⊢ (SELECT1 right⋅k FROM1 R) : _ ⟧ tt (⟦k⟧ t) = Unit.
     
  Definition isKey {s t} (k: Column t s) (R: SQL empty s) :=
    forall t1 t2, denoteSQL R tt t1 -> denoteSQL R tt t2 -> ⟦k⟧ t1 = ⟦k⟧ t2 -> t1 = t2.

  Definition isKey2 {s t} (k: Column t s) (R: SQL empty s) :=
    ⟦ empty ⊢ R : _ ⟧ =
    ⟦ empty ⊢ ((project (right⋅left)) (FROM R, R
                WHERE equal (variable (right⋅left⋅k))
                (variable (right⋅right⋅k)))): _ ⟧.
    
  Definition IntroProj: Type.
    refine (forall r (R: SQL empty r) t0 (l: constant t0)
              (a: Column t0 r) t1 (k: Column t1 r) (ik: isKey k R)
              (ik2: isKey2 k R), _ ).
    pose (Index R k a) as I.
    pose (empty ++ (singleton t1 ++ singleton t0 ++ empty) ++ r) as qs.
    pose (@variable _ qs (right⋅left⋅right⋅left⋅star)) as ia.
    pose (@variable _ qs (right⋅left⋅left⋅star)) as ik'.
    pose (@variable _ qs (right⋅right⋅k)) as rk.
    refine ( ⟦ empty ⊢ (project (right⋅right)
                         (FROM I, R
                          WHERE and (equal ia (constantExpr l))
                                    (equal ik' rk))) :_ ⟧ =
             ⟦ empty ⊢ (project (right⋅right)
                         (FROM R, R
                          WHERE and (equal (variable (right⋅left⋅a)) (constantExpr l))
                                    (equal (variable (right⋅left⋅k)) (variable (right⋅right⋅k))))) :_ ⟧).
  Defined.

  Arguments IntroProj /.

  Definition IntroProjProof: IntroProj.
    cbn.
    by_extensionality g.
    by_extensionality t.
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    match goal with
   | |- ∑ a, @?A a * (@?B a * @?C a * (@?D a * @?E a)) = _ =>
     assert (∑ a, A a * (B a * C a * (D a * E a)) = ∑ a, (A a * B a * C a * E a) * D a) as h
    end.
    {  f_ap.
       by_extensionality a0.
       repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
       rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
       repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
       rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
       symmetry.
       rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
       f_ap.
       rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
       repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
       reflexivity. }
    rewrite h.
    clear h.
    rewrite (path_universe_uncurried agg_sum).
    rewrite (path_universe_uncurried sum_assoc).
    f_ap.
    by_extensionality t2.
    destruct t2 as [ta tb].
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    cbn.
    rewrite (path_universe_uncurried (sum_prod_assoc)).
    rewrite (path_universe_uncurried (equiv_prod_sigma_r _ _ _ )).
    repeat rewrite (path_universe_uncurried (sum_prod_assoc)).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    repeat rewrite (path_universe_uncurried (sum_prod_assoc)).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    repeat rewrite (path_universe_uncurried (sum_prod_assoc)).
    rewrite (path_universe_uncurried (equiv_prod_sigma_r _ _ _ )).
    repeat rewrite (path_universe_uncurried (sum_prod_assoc)).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    repeat rewrite (path_universe_uncurried (sum_prod_assoc)).
    rewrite (path_universe_uncurried (equiv_prod_sigma_r _ _ _)).
    unfold isKey2 in ik2.
    match goal with
    | |- ?A * _ * _ * _ = _ =>  assert (IsHProp A) as h1 end. {
      apply ishprop_sigma_disjoint.
      intros x y h1 h2.
      destruct x as [x1 [x2 x3]].
      destruct y as [y1 [y2 y3]].
      destruct h1 as [h1 [h3 h4]].
      destruct h2 as [h2 [h5 h6]].
      rewrite h3.
      rewrite h5.
      rewrite h4.
      rewrite h6.
      rewrite (unit_eq x3).
      rewrite (unit_eq y3).
      reflexivity. }
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    match goal with
      | |- _ * _ * ?C  = _ => assert ((ta = tb) * C = C) as h2 end. {
      apply path_universe_uncurried.
      apply hprop_prod_l'.
      intros [eq [ra rb]].
      unfold isKey in ik.
      rewrite (unit_eq g) in *.
      exact (ik ta tb ra rb eq). }
    rewrite <- h2.
    clear h2.
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    match goal with
    | |- _ = ?A * ?B * ?C * _ => assert (A * B * C = A * C * B) as h2 end. {
      rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
      rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
      match goal with
        | |- ?A * ?B * _  = _ => assert (A * B = B * A) as h3 end.
      + rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
        reflexivity.
      + rewrite h3.
        reflexivity. }
    rewrite h2.
    clear h2.
    symmetry.
    rewrite <- (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    assert ( denoteSQL R g tb * denoteSQL R g ta =  denoteSQL R g ta * denoteSQL R g tb ) as h2. {
      rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
      reflexivity. }
    rewrite h2.
    clear h2.
    match goal with
    | |- ?A = _ => assert ((ta = tb) * A = A) as h2 end. {
      apply path_universe_uncurried.
      apply hprop_prod_l'.
      intros [[[[i1 [i2 i3]] [e2 [e3 e4]]] e1] [ra rb]].
      apply pair_f_eq in e2.
      destruct e2 as [e2 e5].
      apply pair_f_eq in e5.
      destruct e5 as [e5 e6].
      unfold isKey in ik.
      rewrite (unit_eq g) in *.
      rewrite e4 in e2.
      symmetry in e2.
      exact (ik ta tb ra rb e2). }
    rewrite <- h2.
    clear h2.
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    f_ap.
    apply path_universe_uncurried.
    apply equiv_iff_hprop_uncurried.
    constructor.
    + intros [eq [[[i1 [i2 i3]] [p1 [p2 p3]]] h]].
      apply pair_f_eq in p1.
      destruct p1 as [p1 p4].
      apply pair_f_eq in p4.
      destruct p4 as [p4 p5].
      destruct h.
      destruct eq.
      destruct p4.
      destruct p2.
      refine (_, _, _, _); reflexivity.
    + intros [[[e1 e2] e3] e4].
      destruct e3.
      refine (_,( _, _)); try reflexivity.
    - refine (_; _).
      refine (denoteProj k ta, (⟦l⟧, tt)).
      cbn.
      destruct e2.
      refine (_, (_, _)); reflexivity.
    - exact e1.
  Defined.

  Definition IndexTransProj: Type.
    refine (forall r (R: SQL empty r) t0 (l: constant t0)
              (a: Column t0 r) t1 (k: Column t1 r) (ik: isKey k R)
              (ik2: isKey2 k R), _ ).
    refine ( ⟦ empty ⊢ (project (right⋅right)
                         (FROM R, R
                          WHERE and (equal (variable (right⋅left⋅a)) (constantExpr l))
                                    (equal (variable (right⋅left⋅k)) (variable (right⋅right⋅k))))) :_ ⟧ =
             ⟦ empty ⊢ (project (right⋅left)
                         (FROM R, R
                          WHERE and (equal (variable (right⋅left⋅a)) (constantExpr l))
                          (equal (variable (right⋅left⋅k)) (variable (right⋅right⋅k))))) :_ ⟧).
  Defined.

  Arguments IndexTransProj /.

  Definition IndexTransProjProof: IndexTransProj.
    unfold IndexTransProj.
    by_extensionality g.
    by_extensionality t.
    f_ap.
    by_extensionality t2.
    destruct t2 as [ta tb].
    cbn.
    unfold isKey in *.
    cbn in *.
    apply prod_eq_assoc.
    intros h.
    unfold isKey in ik.
    destruct h as [[h1 h2] [h3 h4]].
    apply ik.
    + rewrite <- (unit_eq g).
      refine h4.
    + rewrite <- (unit_eq g).
      refine h3.
    + cbn.
      symmetry in h2.
      refine h2.
  Defined.
 
  
  (*
     If k is R's primary key, I is R's index on column a.
     Then we want to prove:
     SELECT * FROM R WHERE R.a = l 
     can be rewritten to 
     SELECT * FROM I, R WHERE I.a = l and I.k = R.k  
   *)
  Definition IndexExample0: Type.
    refine (forall r (R: SQL empty r) t0 (l: constant t0)
              (a: Column t0 r) t1 (k: Column t1 r) (ik: isKey k R)
              (ik2: isKey2 k R), _).
    pose (Index R k a) as I.
    pose (empty ++ (singleton t1 ++ singleton t0 ++ empty) ++ r) as qs.
    pose (@variable _ qs (right⋅left⋅right⋅left⋅star)) as ia.
    pose (@variable _ qs (right⋅left⋅left⋅star)) as ik'.
    pose (@variable _ qs (right⋅right⋅k)) as rk.
    refine (⟦ empty ⊢ (SELECT * FROM1 R
                       WHERE equal (variable (right⋅a)) (constantExpr l)): _ ⟧ =
            ⟦ empty ⊢ (project (right⋅right) (FROM I, R
                       WHERE and (equal ia (constantExpr l))
                                 (equal ik' rk) )) : _ ⟧).
  Defined.

  Arguments IndexExample0 /.

   Definition f_ap_eq {A B C} {f g: A -> B -> C}:
    forall x y, f = g -> f x y = g x y.
    intros.
    rewrite X.
    reflexivity.
  Defined.  

  Definition IndexExampleProof0: IndexExample0.
    unfold IndexExample0.
    unfold Index.
    intros.
    rewrite (IntroProjProof r R t0 l a t1 k ik ik2).
    rewrite (IndexTransProjProof r R t0 l a t1 k ik ik2). 
    by_extensionality g.
    by_extensionality t.
    unfold isKey2 in ik2.
    cbn in ik2.
    apply (f_ap_eq g t) in ik2.
    cbn in ik2.
    rewrite ik2.
    rewrite (path_universe_uncurried (equiv_prod_sigma _ _ _)).
    f_ap.
    by_extensionality t2.
    repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    match goal with
      | |- ?a1 * _ * _ * _ * _   = ?a2 * _ * _ * _ * ?b => assert (b * a1 = b * a2) end.
    +  apply path_universe_uncurried.
       apply equiv_iff_hprop_uncurried.
       constructor.
       { intro h.
         destruct h as [h1 h2].
         refine (h1, _).
         rewrite <- h1 in h2.
         exact h2. }
       { intro h.
         destruct h as [h1 h2].
         refine (h1, _).
         rewrite <- h1.
         exact h2. }
    +  rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
       repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
       symmetry.
       rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
       repeat rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
       rewrite X.
       reflexivity.
  Defined.
      
End Index.