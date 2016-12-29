Require Import HoTT.
Require Import UnivalenceAxiom.

Require Import HoTTEx.
Require Import Denotation.
Require Import UnivalentSemantics.
Require Import CQTactics.

Open Scope type.

Module CSE344 (T : Types) (S : Schemas T) (R : Relations T S)  (A : Aggregators T S).
  Import T S R A.
  Module SQL_TSRA := SQL T S R A.
  Import SQL_TSRA.
  Module CQTac := CQTactics T S R A.
  Import CQTac.

  Section CSE344.
    Variable null : forall T, constant T.
    Arguments null {_}.

    Variable integer : type.
    Variable count : forall T, aggregator T integer.
    Arguments count {_}.
    Notation "'COUNT' ( e )" := (aggregatorGroupByProj count e).

    Variable uid : type.
    Variable uname : type.
    Variable size : type.
    Variable city : type.
    Variable pid : type.
    
    Variable Usr : Schema.
    Variable usr : relation Usr.
    Variable usrUid : Column uid Usr.
    Variable usrUname : Column uname Usr.
    Variable usrCity : Column city Usr.

    Variable Pic : Schema.
    Variable pic : relation Pic.
    Variable picUid : Column uid Pic.
    Variable picSize : Column size Pic.
    Variable picPid : Column pid Pic.
 
    Variable denver : constant city.
    Variable denverNonNull : null <> denver.

    Variable gt1000000 : Pred (leaf size).
    Variable gt3000000 : Pred (leaf size).

    Variable Γ : Schema.

    Notation var := variable.
    Notation combine' := combineGroupByProj.

    Definition x'' : Proj (Γ ++ Usr) Usr := right.
    Definition x''' : Proj ((Γ ++ Usr) ++ Pic) Usr := left ⋅ right.
    Definition y'' : Proj ((Γ ++ Usr) ++ Pic) Pic := right.
  
    Definition x'''' : Proj (Γ ++ (Usr ++ Pic)) Usr := right ⋅ left.
    Definition y'''' : Proj (Γ ++ (Usr ++ Pic)) Pic := right ⋅ right.

    Definition leftOuterJoin {s0 s1} (q0:SQL Γ s0) (q1:SQL Γ s1) 
                             (b:Pred (Γ ++ (s0 ++ s1))) : SQL Γ (s0 ++ s1).
      exact (SELECT * FROM2 q0, q1 WHERE b).
      (* TODO missing union with nulls  *)
    Defined.

    Notation "q0 'LEFT' 'OUTER' 'JOIN' q1 'ON' b" := (leftOuterJoin q0 q1 b) (at level 45, b at level 45).

    Lemma problem3 :
      ⟦ DISTINCT SELECT1 combine (combine (x'' ⋅ usrUid) (x'' ⋅ usrUname))
          (e2p (aggregate count (
            SELECT1 (y'' ⋅ picPid) FROM1 table pic 
            WHERE equal (var (x''' ⋅ usrUid)) (var (y'' ⋅ picUid)) AND
                  castPred (y'' ⋅ picSize) gt1000000)))
        FROM1 table usr
        WHERE equal (var (x'' ⋅ usrCity)) (constantExpr denver)
      ⟧ = 
      ⟦ SELECT combine' (combine' PLAIN(var (x'''' ⋅ usrUid))
                                  PLAIN(var (x'''' ⋅ usrUname))) 
                                  COUNT(var (y'''' ⋅ picPid))
        FROM1 table usr LEFT OUTER JOIN table pic ON 
          equal (var (x'''' ⋅ usrUid)) (var (y'''' ⋅ picUid)) AND
          castPred (y'''' ⋅ picSize) gt1000000
        GROUP BY combine (combine (x'''' ⋅ usrUid) (x'''' ⋅ usrUname)) (x'''' ⋅ usrCity)
        (* TODO: HAVING x.usrCity = denver *)
      ⟧.
    Proof.
      prepareDistinctSQLProof.
      - prepareConjuctiveQueryProof.
        destruct t as [tUidUname tInteger].
        destruct tUidUname as [tUid tUname].
        simple refine (exist _ (t0, _) _).
    Admitted.
   
    Definition s := Γ ++ ((Usr ++ Pic) ++ Pic) ++ Pic.

    Definition x : Proj s Usr := right ⋅ left ⋅ left ⋅ left.
    Definition u : Proj s Pic := right ⋅ left ⋅ left ⋅ right.
    Definition v : Proj s Pic := right ⋅ left ⋅ right.
    Definition w : Proj s Pic := right ⋅ right.
   
    Definition original : Query Γ (leaf uid ++ leaf uname) :=
      ⟦ DISTINCT SELECT1 combine (x ⋅ usrUid) (x ⋅ usrUname)  
        FROM table usr, table pic, table pic, table pic
        WHERE equal (var (x ⋅ usrUid)) (var (u ⋅ picUid)) AND
              equal (var (x ⋅ usrUid)) (var (v ⋅ picUid)) AND
              equal (var (x ⋅ usrUid)) (var (w ⋅ picUid)) AND
              castPred (u ⋅ picSize) gt1000000 AND
              castPred (v ⋅ picSize) gt3000000 AND
              equal (var (w ⋅ picSize)) (var (u ⋅ picSize)) ⟧.

    Lemma problem1 : original = 
      ⟦ DISTINCT SELECT1 combine (x ⋅ usrUid) (x ⋅ usrUname)  
        FROM table usr, table pic, table pic, table pic
        WHERE equal (var (x ⋅ usrUid)) (var (u ⋅ picUid)) AND
              equal (var (x ⋅ usrUid)) (var (v ⋅ picUid)) AND
              equal (var (x ⋅ usrUid)) (var (w ⋅ picUid)) AND
              castPred (u ⋅ picSize) gt1000000 AND
              castPred (v ⋅ picSize) gt3000000 AND
              castPred (w ⋅ picSize) gt1000000 ⟧.
    Proof.
      unfold original.
      conjunctiveQueryProof.
    Qed.

    Lemma problem4 : original = 
      ⟦ DISTINCT SELECT1 combine (x ⋅ usrUid) (x ⋅ usrUname)  
        FROM table usr, table pic, table pic, table pic
        WHERE equal (var (x ⋅ usrUid)) (var (u ⋅ picUid)) AND
              equal (var (x ⋅ usrUid)) (var (v ⋅ picUid)) AND
              equal (var (x ⋅ usrUid)) (var (w ⋅ picUid)) AND
              castPred (u ⋅ picSize) gt1000000 AND
              castPred (v ⋅ picSize) gt3000000 AND
              equal (var (w ⋅ picSize)) (var (v ⋅ picSize)) ⟧.
    Proof.
      unfold original.
      conjunctiveQueryProof.
    Qed.

    Definition s' := Γ ++ (Usr ++ Pic) ++ Pic.

    Definition x' : Proj s' Usr := right ⋅ left ⋅ left.
    Definition u' : Proj s' Pic := right ⋅ left ⋅ right.
    Definition v' : Proj s' Pic := right ⋅ right.

    Lemma problem2 : original = 
      ⟦ DISTINCT SELECT1 combine (x' ⋅ usrUid) (x' ⋅ usrUname)  
        FROM table usr, table pic, table pic
        WHERE equal (var (x' ⋅ usrUid)) (var (u' ⋅ picUid)) AND
              equal (var (x' ⋅ usrUid)) (var (v' ⋅ picUid)) AND
              castPred (u' ⋅ picSize) gt1000000 AND
              castPred (v' ⋅ picSize) gt3000000 ⟧.
    Proof.
      unfold original.
      conjunctiveQueryProof.
    Qed.

  End CSE344.
End CSE344.