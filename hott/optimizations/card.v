Require Import HoTT.
Require Import UnivalenceAxiom.
Require Import UnivalentSemantics.

Module Type Cards.

  Definition Card := Tr 0 hSet.

  Definition merely0 (A: Type):= (BuildhSet (Trunc 0 A)).
  
  Definition card (x: hSet) : Card := @tr (Tr 0) hSet x.
  
  Definition cplus (A B:Card) : Card.
    refine (Trunc_ind _ _ _ ).
    hnf in *.
    admit.
  
End Cards.