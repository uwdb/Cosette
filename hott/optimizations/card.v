Require Import HoTT.
Require Import UnivalenceAxiom.
Require Import UnivalentSemantics.

Module Type Cards.

  Definition Card := Tr 0 hSet.

  Definition merely0 (A: Type):= (BuildhSet (Trunc 0 A)).
  
  Definition card (x: hSet) : Card := @tr (Tr 0) hSet x.
  
  Definition cplus : Card -> Card -> Card.
    refine (fun a => _).
    refine (@Trunc_ind 0 hSet (fun (x: Card) => Card -> Card) _ (fun a' b => _) a).
    refine (@Trunc_ind 0 hSet (fun x => Card) _ (fun b' => card (BuildhSet (a' + b'))) b).
  Defined.

  Definition cmul : Card -> Card -> Card.
    refine (fun a => _).
    refine (@Trunc_ind 0 hSet (fun (x: Card) => Card -> Card) _ (fun a' b => _) a).
    refine (@Trunc_ind 0 hSet (fun x => Card) _ (fun b' => card (BuildhSet (a' * b'))) b).
  Defined.

  Definition card_sum_comm : forall (a b: Card), (cplus a b) = (cplus b a).
    intros.
    unfold cplus.   
    Admitted.
        
  End Cards.