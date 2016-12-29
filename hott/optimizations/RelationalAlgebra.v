Require Import HoTT.
Require Import UnivalenceAxiom.

Require Import HoTTEx.
Require Import Denotation.
Require Import UnivalentSemantics.
Require Import AutoTactics.

Open Scope type.

(*

HoTT/theories/Basics/Overture.v

HoTT/theories/UnivalenceAxiom.v

HoTT/theories/Types/Prod.v

HoTT/theories/hit/Truncations.v

HoTT/theories/UnivalenceImpliesFunext.v

*)

Module RelationalAlgebraOptimization (T : Types) (S : Schemas T) (R : Relations T S)  (A : Aggregators T S).
  Import T S R A.
  Module SQL_TSRA := SQL T S R A.
  Import SQL_TSRA.
  Module AutoTac := AutoTactics T S R A.
  Import AutoTac.
  
  
  Lemma commutativeSelect Γ s a slct0 slct1 :
    ⟦ Γ ⊢ (SELECT * FROM1 (SELECT * FROM1 a WHERE slct1) WHERE slct0) : s ⟧ =
    ⟦ Γ ⊢ (SELECT * FROM1 (SELECT * FROM1 a WHERE slct0) WHERE slct1) : s ⟧.
  Proof.
    hott_ring.
  Qed.

    
  Lemma selectFalse Γ s a (E: relation s):
      ⟦ E ⟧ = (fun _ => Empty) -> 
      ⟦ Γ ⊢ (SELECT * FROM1 a WHERE FALSE): s ⟧ =
      ⟦ Γ ⊢ table E : s⟧.
  Proof.
    Abort.
  
    

  Lemma idempotentSelect Γ s a slct :
    ⟦ Γ ⊢ (SELECT * FROM1 (SELECT * FROM1 a WHERE slct) WHERE slct) : s ⟧ =
    ⟦ Γ ⊢ (SELECT * FROM1 a WHERE slct) : s ⟧.
  Proof.
    hott_ring.
  Qed.
  
 
  Lemma conjunctSelect Γ s a slct0 slct1 :
    ⟦ Γ ⊢ (SELECT * FROM1 a WHERE slct0 AND slct1) : s ⟧ =
    ⟦ Γ ⊢ (SELECT * FROM1 (SELECT * FROM1 a WHERE slct0) WHERE slct1) : s ⟧.
  Proof.
    hott_ring.
  Qed.

  Lemma pushdownSelect Γ s1 s2 (r: SQL Γ s1) (s: SQL Γ s2) slct: 
    ⟦ Γ ⊢ (SELECT * FROM r, (SELECT * FROM1 s WHERE slct)) : _ ⟧ =
    ⟦ Γ ⊢ (SELECT * FROM r, s WHERE
           castPred (combine left (right⋅right)) slct) : _ ⟧.
  Proof.
    hott_ring.
  Qed.

  (* The fact that we cannot rewrite
       (SELECT * FROM a WHERE slct0) UNION (SELECT * FROM a WHERE slct1)
     into
       SELECT * FROM a WHERE slct0 OR slct1
     should inspire us to have WHERE clauses that can influence multiplicity *)
  Lemma disjointSelect Γ s a slct0 slct1 :
    ⟦ Γ ⊢ (DISTINCT SELECT * FROM1 a WHERE slct0 OR slct1) : s ⟧ =
    ⟦ Γ ⊢ (DISTINCT ((SELECT * FROM1 a WHERE slct0) UNION ALL (SELECT * FROM1 a WHERE slct1))) : s ⟧.
  Proof.
    deductive_proof.
  Qed.
  
  Lemma projectionDistributesOverUnionn Γ s a0 a1 slct :
    ⟦ Γ ⊢ (SELECT * FROM1 (a0 UNION ALL a1) WHERE slct) : s ⟧ =
    ⟦ Γ ⊢ ((SELECT * FROM1 a0 WHERE slct) UNION ALL (SELECT * FROM1 a1 WHERE slct)) : s ⟧.
  Proof.
    hott_ring.
  Qed.
  
  Lemma productDistributesOverUnion Γ s s01 a a0 a1 :
    ⟦ Γ ⊢ (SELECT * FROM2 a, (a0 UNION ALL a1)) : (s ++ s01) ⟧ = 
    ⟦ Γ ⊢ ((SELECT * FROM2 a, a0) UNION ALL (SELECT * FROM2 a, a1)) : (s ++ s01) ⟧.
  Proof.
    hott_ring.
  Qed.

  Lemma joinCommute  Γ s1 s2 (a:SQL Γ s1) (b:SQL Γ s2):
              ⟦ Γ ⊢ (project (combine (right⋅right⋅star) (right⋅left⋅star))
                              (FROM b, a) ) : (s1 ++ s2) ⟧ =
              ⟦ Γ ⊢ (FROM a, b) : (s1 ++ s2) ⟧.
  Proof.
    start.
    symmetry.
    rewrite (path_universe_uncurried (equiv_prod_symm _ _)).
    rewrite (path_universe_uncurried sumPair).
    rewrite <- (path_universe_uncurried eqSum).
    reflexivity.
  Qed.

  Variable sqlUnit : type.
  Variable sqlTt  : constant sqlUnit.
  Variable denoteSqlUnit : @paths Type ⟦ sqlUnit ⟧ Unit.

  Definition DenoteSqlTt : Type.
    refine (⟦ sqlTt ⟧ = _).
    rewrite denoteSqlUnit.
    exact tt.
  Defined.

  Variable denoteSqlTt : DenoteSqlTt. 

  Variable unitTable : relation (leaf sqlUnit).

  Variable denoteUnitTable : @paths (_ -> Type) ⟦ unitTable ⟧ (fun _ => Unit).

  Lemma doubleUnitNeqUnit :
    ~(forall Γ s a, ⟦ Γ ⊢ a : s ⟧ = ⟦ Γ ⊢ a UNION ALL a : s ⟧).
  Proof.
    assert (exists Γ s a, ~⟦ Γ ⊢ a : s ⟧ = ⟦ Γ ⊢ a UNION ALL a : s ⟧) as h. {
      refine (exist _ (leaf sqlUnit) _).
      refine (exist _ (leaf sqlUnit) _).
      refine (exist _ (table unitTable) _).
      cbn.
      intros h.
      assert (forall t, (⟦ unitTable ⟧ t) = (⟦ unitTable ⟧ t + ⟦ unitTable ⟧ t)) as h'. {
        intros t.
        assert (⟦ sqlUnit ⟧) as tt. {
          rewrite denoteSqlUnit.
          exact tt.
        }
        apply happly in h.
        specialize (h tt).
        apply happly in h.
        specialize (h t).
        apply h.
      }
      clear h.
      rewrite denoteUnitTable in h'.
      unfold Tuple in *.
      rewrite denoteSqlUnit in h'.
      specialize (h' tt).
      apply onePlusOneNeqOne.
      apply equiv_path.
      assumption.
    }
    intros h'.
    destruct h as [Γ [s [a h]]].
    specialize (h' Γ s a).
    apply h.
    assumption.
  Qed.    
End RelationalAlgebraOptimization.
