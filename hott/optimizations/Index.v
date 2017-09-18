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

  (* We would like a more fundamental definition like Dan proposed, but for now, we just use this one.*)
  Definition isKey2 {s ty} (k: Column ty s) (R: SQL empty s) :=
    forall (t: Tuple s), denoteSQL R tt t = {t': Tuple s & (⟦k⟧ t' = ⟦ k ⟧ t) * (denoteSQL R tt t') * denoteSQL R tt t}. 

  Lemma empty_is_tt {g: Tuple empty}:
    g = tt.
  Proof.
    unfold Tuple in g.
    symmetry.
    apply eta_unit.
  Defined.

  Lemma equiv_sigma_prod_assoc_h {A B C D E}:
    {a: A & B a * ((C a) * (D a)) * E a} <~> {a:A & B a * C a * D a * E a}.
  Proof.
    apply equiv_path.
    f_ap.
    by_extensionality a.
    rewrite (path_universe_uncurried (equiv_prod_assoc _ _ _)).
    reflexivity.
  Defined.
    
  Definition IndexQ0: Type.
    refine (forall r (R: SQL empty r) t0 (l: constant t0)
              (a: Column t0 r) t1 (k: Column t1 r) (ik: isKey2 k R), _).
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

  (* a fact about index, assumed for now. *)
  Definition indexFact0 {s ty} {k: Column ty s} {R: SQL empty s} (p: isKey2 k R) :
    forall (t:Tuple s) (p: Tuple s -> Type),
      {t': Tuple s & (denoteProj k t' = denoteProj k t) * (denoteSQL R tt t') * (denoteSQL R tt t) * p t'}
      = {t': Tuple s & (denoteProj k t' = denoteProj k t) * (denoteSQL R tt t') * (denoteSQL R tt t) * p t}.
   Admitted.

  Arguments IndexQ0 /.

  Definition IndexProof0: IndexQ0.
    unfold IndexQ0.
    intros.
    by_extensionality g.
    by_extensionality t.
    pose (indexFact0 ik) as pf.
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    (* "destruc" t on RHS *)
    rewrite <- (path_universe_uncurried (equiv_sigma_prod _)).
    rewrite equiv_2sigma_eq_subst.
    (* move sum around on RHS *)
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite equiv_sigma_sigma_prod.
    rewrite (path_universe_uncurried equiv_2sigma_prod_assoc). 
    rewrite (path_universe_uncurried equiv_2sigma_prod_symm).
    unfold fst.
    rewrite (path_universe_uncurried (equiv_sigma_symm _)).
    (* destruct t' on RHS*)
    rewrite (equiv_2sigma_eq_subst_r _).
    unfold snd.
    (* move p(t) to the right place. *)
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried (equiv_sigma_prod_symm _ _ _)).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc).
    rewrite (path_universe_uncurried equiv_sigma_prod_assoc_h).
    (* consolidate tt and g first *)
    rewrite <- (@eta_unit g).
    (* apply A1 *)
    rewrite (pf _ _).
    rewrite (path_universe_uncurried (equiv_prod_sigma_r _ _ _)).
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    f_ap.
    unfold isKey2 in ik.
    symmetry.
    (* apply index definition *)
    exact (ik t).
  Qed.
      
End Index.
