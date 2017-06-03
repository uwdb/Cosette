Require Import HoTT.
Require Import UnivalenceAxiom.

Require Import HoTTEx.
Require Import Denotation.
Require Import UnivalentSemantics.
Require Import CQTactics.
Require Import AutoTactics.


Open Scope type.

Module CSE344Final1 (T : Types) (S : Schemas T) (R : Relations T S)  (A : Aggregators T S).

    Import T S R A.
    Module SQL_TSRA := SQL T S R A.
    Import SQL_TSRA.
    Module CQTac := CQTactics T S R A.
    Import CQTac.

    Parameter int : type.
    Parameter count : forall {T}, aggregator T int.
    Notation "'COUNT' ( e )" := (aggregatorGroupByProj count e).

    Variable u : Schema.
    Variable p : Schema.
    
    Variable pic: relation p.
    Variable usr: relation u.
    
    Variable u_uid: Column int u.
    Variable u_uname: Column int u.
    Variable u_city: Column int u.
    Variable p_uid: Column int p.
    Variable p_pid: Column int p.
    Variable p_size: Column int p.

    Variable denver: constant int.
    
    Variable gt100000 : Pred (leaf int).

    Notation var := variable.
    Notation combine' := combineGroupByProj.

    (* select x.uid as uid, x.uname as uname,
        (select count(star ) as cnt from picture y
         where x.uid = y.uid and y.size > 1000000) as cnt
        from user x
        where x.city = 3 *)
     
    Lemma CSE344Final1 : Type.
      refine (forall {Γ:Schema},
      ⟦ Γ ⊢ (SELECT1 combine (combine (right ⋅ u_uid) (right ⋅ u_uname))
                        (e2p (aggregate count
                                        (SELECT1 (right ⋅ p_pid) FROM1 table pic
                                                 WHERE equal (var (left ⋅ right ⋅ u_uid))
                                                 (var (right ⋅ p_uid)) AND
                                                 castPred (right ⋅ p_size) gt100000)))
                        FROM1 table usr
                        WHERE equal (var (right ⋅ u_city)) (constantExpr denver)) : _ ⟧ = 
      ⟦ Γ ⊢ (SELECT combine' (combine' PLAIN(var (right ⋅ left ⋅ u_uid))
                                      PLAIN(var (right ⋅ left ⋅ u_uname))) 
                                  COUNT(var (right ⋅ right ⋅ p_pid))
             FROM1 (product (table usr) (table pic)) 
             WHERE  equal (var (right ⋅ left ⋅ u_uid)) (var (right ⋅ right ⋅ p_uid)) AND
             castPred (right ⋅ right ⋅ p_size) gt100000
             GROUP BY (combine (right ⋅ left ⋅ u_uid) (right ⋅ left ⋅ u_uname))) : _ ⟧).
    Defined.

    Arguments CSE344Final1 /.

    Lemma CSE344Final1Proof: CSE344Final1.
      Admitted.
  
End CSE344Final1.