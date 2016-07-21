Require Import HoTT.
Require Import UnivalenceAxiom.

Require Import Denotation.
Require Import HoTTEx.

Module Type Types.
  Parameter type : Type.
  Parameter denotationType : Denotation type Type.
  Parameter isHSetType : forall T:type, IsHSet ⟦ T ⟧.

  Parameter constant : type -> Type.
  Parameter unary : type -> type -> Type.
  Parameter binary : type -> type -> type -> Type.

  Parameter denotationConstant : forall S, Denotation (constant S) ⟦ S ⟧.
  Parameter denotationUnary : forall S T, Denotation (unary S T) (⟦ S ⟧ -> ⟦ T ⟧).
  Parameter denotationBinary : forall S T U, Denotation (binary S T U) (⟦ S ⟧ -> ⟦ T ⟧ -> ⟦ U ⟧).
End Types.

Inductive Tree (A:Type) := 
| node (t0 t1 : Tree A)
| leaf (a:A)
| empty
.

Arguments node {_} _ _.
Arguments leaf {_} _.
Arguments empty {_}. 

Module SQLDenotation (T : Types).
  Import T.
  (* definition of inductive types in 
     modules isn't supported by Coq in this case *)
  (* NOTE ideally schemas would have little structure, and users
          of this library would be free to implement products of
          schemas etc as they wish. All this structure is useful 
          though because it introduces more computation in our
          proofs, and thus leads to much simpler proofs. *)
  (* NOTE schemas should probably not have an empty and leaf constructor, but
          instead a leaf constructor with a list of types. The advantage is that
          this matches the fact that projections are lists of expressions *)
  Definition Schema := Tree type.
  Definition singleton := @leaf type.

  Notation "s0 ++ s1" := (node s0 s1).

  (* NOTE we could have `Tuple s -> nat` for the bag semantics,
          but this is more general as we support infinite types.
          this is useful for projection *)
  Fixpoint Tuple (s:Schema) : Type.
    refine (match s with
    | node t0 t1 => (Tuple t0) * (Tuple t1)
    | leaf T => ⟦T⟧
    | empty => Unit
    end).
  Defined.

  Instance isHSetTuple s : IsHSet (Tuple s).
    induction s; refine (_).
  Defined. 

  Definition Relation s := Tuple s -> Type.
  Definition Query Γ s := Tuple Γ -> Relation s.
End SQLDenotation.

(* universe stuff is needed because of Coq bug (fixed with 8.5pl1)
   https://groups.google.com/forum/#!topic/hott-cafe/YY5MF5O1288 *)
Unset Universe Polymorphism.
Module Type Schemas (T : Types).
  Import T.
  Module TD := SQLDenotation T.
  Import TD.
  Export TD.

  (* this module can be deleted *)
End Schemas.
Set Universe Polymorphism.

Module Type Relations (T : Types) (S : Schemas T).
  Import T S.

  Parameter relation : Schema -> Type.
  Parameter denotationRelation : forall s, Denotation (relation s) (Relation s).
End Relations.

Module Type Aggregators (T : Types) (S : Schemas T).
  Import T S.
  
  Parameter aggregator : type -> type -> Type.
  Parameter denotationAggregator : forall S T, Denotation (aggregator S T) (Relation (leaf S) -> ⟦ T ⟧).
End Aggregators.

(* We have SQL depend on modules instead of type class instances
   because type classes lead to bad unfolding behavior of 
   mutually inductive fixpoints. *)
Module SQL (T : Types) (S : Schemas T) (R : Relations T S) (A : Aggregators T S).
  Import T S R A.

  Inductive SQL : Schema -> Schema -> Type :=
  | table {Γ s} : relation s -> SQL Γ s
  | union {Γ s} : SQL Γ s -> SQL Γ s -> SQL Γ s
  | minus {Γ s} : SQL Γ s -> SQL Γ s -> SQL Γ s
  | select  {Γ s} : Pred (Γ ++ s) -> SQL Γ s -> SQL Γ s
  | product {Γ s0 s1} : SQL Γ s0 -> SQL Γ s1 -> SQL Γ (s0 ++ s1)
  | project {Γ s s'} : Proj (Γ ++ s) s' -> SQL Γ s -> SQL Γ s'
  | distinct {Γ s} : SQL Γ s -> SQL Γ s
  | castSQL {Γ Γ' s} : Proj Γ Γ' -> SQL Γ' s -> SQL Γ s
  
  with Pred : Schema -> Type :=
  | inhabited {Γ s} : SQL Γ s -> Pred Γ
  | equal {Γ T} : Expr Γ T -> Expr Γ T -> Pred Γ
  | negate {Γ} : Pred Γ -> Pred Γ
  | and {Γ} : Pred Γ -> Pred Γ -> Pred Γ
  | or {Γ} : Pred Γ -> Pred Γ -> Pred Γ
  | false {Γ} : Pred Γ
  | true {Γ} : Pred Γ
  | castPred {Γ Γ'} : Proj Γ Γ' -> Pred Γ' -> Pred Γ

  with Proj : Schema -> Schema -> Type :=
  | combine  {Γ Γ0 Γ1} : Proj Γ Γ0 -> Proj Γ Γ1 -> Proj Γ (Γ0 ++ Γ1)
  | left  {Γ0 Γ1} : Proj (Γ0 ++ Γ1) Γ0
  | right  {Γ0 Γ1} : Proj (Γ0 ++ Γ1) Γ1
  | compose  {Γ Γ' Γ''} : Proj Γ Γ' -> Proj Γ' Γ'' -> Proj Γ Γ''
  | star     {Γ} : Proj Γ Γ
  | e2p {T Γ} : Expr Γ T -> Proj Γ (singleton T)
  | erase    {Γ} : Proj Γ empty
 
  with Expr : Schema -> type -> Type :=
  | variable {T Γ} (c:Proj Γ (leaf T)) : Expr Γ T 
  | aggregate {Γ S T} : aggregator S T -> SQL Γ (singleton S) -> Expr Γ T
  | constantExpr {Γ S} : constant S -> Expr Γ S
  | unaryExpr {Γ S T} : unary S T -> Expr Γ S -> Expr Γ T
  | binaryExpr {Γ S T U} : binary S T U -> Expr Γ S -> Expr Γ T -> Expr Γ U
  | castExpr {Γ Γ' T} : Proj Γ Γ' -> Expr Γ' T -> Expr Γ T
  .

  Fixpoint denoteSQL {Γ s} (a : SQL Γ s) : Query Γ s 
  with     denotePred {Γ} (slct : Pred Γ) : Tuple Γ -> hProp
  with     denoteProj {Γ Γ'} (cast: Proj Γ Γ') {struct cast} : Tuple Γ -> Tuple Γ'
  with     denoteExpr {Γ T} (e : Expr Γ T) : Tuple Γ -> ⟦T⟧.
    - refine (
      match a in SQL Γ s return Query Γ s with
      | table _ _ r => fun _ => ⟦r⟧
      | union _ _ a a' => fun g t => denoteSQL _ _ a g t + denoteSQL _ _ a' g t
      | minus _ _ a a' => fun g t => denoteSQL _ _ a g t * hnot (merely (denoteSQL _ _ a' g t))
      | select _ _ slct a => fun g t => denotePred _ slct (g, t) *
                                    denoteSQL _ _ a g t 
      | product _ _ _ a0 a1 => fun g t => denoteSQL _ _ a0 g (fst t) * 
                                      denoteSQL _ _ a1 g (snd t)
      | project _ _ _ proj a => fun g t' => ∑ t, denoteSQL _ _ a g t * 
                                             BuildhProp (denoteProj _ _ proj (g, t) = t')
      | distinct _ _ a => fun g t => merely (denoteSQL _ _ a g t)
      | castSQL _ _ _ f a => fun g t => denoteSQL _ _ a (denoteProj _ _ f g) t
      end).
    - refine (
      match slct in Pred Γ return Tuple Γ -> hProp with
      | inhabited _ _ a => fun g => hexists (fun t => denoteSQL _ _ a g t)
      | equal _ _ e0 e1 => fun g => BuildhProp (denoteExpr _ _ e0 g = denoteExpr _ _ e1 g)
      | negate _ slct => fun g => hnot (denotePred _ slct g)
      | and _ slct0 slct1 => fun g => hand (denotePred _ slct0 g) (denotePred _ slct1 g)
      | or _ slct0 slct1 => fun g => hor (denotePred _ slct0 g) (denotePred _ slct1 g)
      | false _ => fun _ => False
      | true _ => fun _ => True
      | castPred _ _ f slct => fun g => denotePred _ slct (denoteProj _ _ f g)
      end).
    - refine (
      match cast with
      | combine _ _ _ c c' => _
      | left _ _ => _
      | right _ _ => _
      | compose _ _ _ c c' => _
      | star _ => _
      | e2p _ _ e => _ 
      | erase _ => _
      end).
      + exact (fun t => (denoteProj _ _ c t, denoteProj _ _ c' t)).
      + exact fst.
      + exact snd.
      + exact (fun t => denoteProj _ _ c' (denoteProj _ _ c t)).
      + exact (fun t => t).
      + exact (fun t => denoteExpr _ _ e t).
      + exact (fun _ => tt).
    - refine (
      match e in Expr Γ T return Tuple Γ -> ⟦T⟧ with
      | variable T _ c => fun g => denoteProj _ _ c g
      | aggregate _ _ _ aggr a => fun g => ⟦aggr⟧ (denoteSQL _ _ a g)
      | constantExpr _ _ c => fun _ => ⟦ c ⟧ 
      | unaryExpr _ _ _ f e => fun g => ⟦ f ⟧ (denoteExpr _ _ e g)
      | binaryExpr _ _ _ _ f e0 e1 => fun g =>  ⟦ f ⟧ (denoteExpr _ _ e0 g) (denoteExpr _ _ e1 g)
      | castExpr _ _ _ f e => fun g => denoteExpr _ _ e (denoteProj _ _ f g)
      end).
  Defined.

  Global Instance denotationProj {Γ Γ'} : Denotation (Proj Γ Γ') (Tuple Γ -> Tuple Γ') :=
    {| denote := denoteProj |}.

  Global Instance denotationSQL Γ s : Denotation (SQL Γ s) _ := {| 
    denote := denoteSQL 
  |}.

  Global Instance denotationPred Γ : Denotation (Pred Γ) _ := {| 
    denote := denotePred 
  |}.
  
  Global Instance denotationExpr Γ T : Denotation (Expr Γ T) _ := {| 
    denote := denoteExpr 
  |}.

  Definition Column T Γ := Proj Γ (leaf T).

  Definition getLeaf {T Γ} : Column T Γ -> Proj Γ (singleton T) :=
    fun c => e2p (variable c).

  Definition Projection Γ s s' := Proj (Γ ++ s) s'.

  Arguments Projection _ _ _ /.

  Definition projectStar {Γ s} : Projection Γ s s := right.
   
  Definition projectSingleton {Γ T s} (e:Expr (Γ ++ s) T) : Projection Γ s (singleton T) := e2p e.

  Definition projectNil {Γ s} : Projection Γ s empty := erase.

  Definition projectCons {Γ T s s'} (e:Expr (Γ ++ s) T) (proj:Projection Γ s s') : Projection Γ s (node (singleton T) s') :=
    combine (projectSingleton e) proj.

  Notation "p1 ⋅ p2" := (compose p1 p2) (at level 45).
  Notation "Γ ⊢ x : s" := (x:(SQL Γ s)) (at level 45, x at level 45).
  Notation "a 'WHERE' c" := (select c a) (at level 45, c at level 45).
  Notation "'SELECT' '*' a" := (a) (at level 45).
  Notation "'SELECT1' proj a" := (project proj a) (at level 45).
  Notation "'SELECT2' proj0 , proj1 a" := (project (projectCons proj0 (projectCons proj1 projectNil)) a) (at level 45).
  Notation "'FROM1' a" := (a) (at level 45).
  Notation "'FROM2' a , b" := (product a b) (at level 45).  (* TODO kill, and rename FROM2 to FROM *)
  Notation "'FROM' a , b , .. , c" := (product .. (product a b) .. c) (at level 46, c at level 44).
  Notation "a 'UNION' 'ALL' b" := (union a b) (at level 45).
  Notation "a 'MINUS' b" := (minus a b) (at level 45).
  Notation "'EXISTS' s" := (inhabited s) (at level 45).
  Notation "s0 'AND' s1" := (and s0 s1) (at level 45).
  Notation "s0 'OR' s1" := (or s0 s1) (at level 45).
  Notation "'NOT' s0" := (negate s0) (at level 45).
  Notation "'FALSE'" := (false) (at level 45).
  Notation "'TRUE'" := (true) (at level 45).
  Notation "'DISTINCT' s" := (distinct s) (at level 45).
  
  Definition GroupByProjection Γ s C T := SQL (Γ ++ s) s -> Column C s -> Expr (Γ ++ s) T.

  Definition plainGroupByProjection {Γ s C T} (e : Expr (Γ ++ s) T) : GroupByProjection Γ s C T := fun _ _ => e.
  Arguments plainGroupByProjection [_ _ _ _] _ / _ _.

  Definition aggregatorGroupByProjection {Γ s C S T} : aggregator S T -> Expr (Γ ++ s) S -> GroupByProjection Γ s C T.
    intros agg e a c.
    refine (aggregate agg (SELECT1 (e2p (castExpr left e))
                           FROM1 a WHERE (equal (variable (left⋅right⋅c)) 
                                                (variable (right⋅c))))).
  Defined. 
  Arguments aggregatorGroupByProjection [_ _ _ _ _] _ _ / _ _.

  (* TODO, can we add more projections to groupby *)
  Definition groupBy {Γ s C T0 T1} (a : SQL Γ s) (c : Column C s) 
                     (proj0 : GroupByProjection Γ s C T0) (proj1 : GroupByProjection Γ s C T1) : 
                     SQL Γ (singleton T0 ++ singleton T1 ++ empty).
    refine (let a' : SQL (Γ ++ s) s := castSQL left a in _). 
    refine (DISTINCT SELECT2 (proj0 a' c), (proj1 a' c) FROM1 a).
  Defined.

  Arguments groupBy [_ _ _ _ _] _ _ _ _ /.

  (*
    Semi-join with single equality predicate.
   *)
  Definition semiJoin1 {Γ s1 s2 ty} (a: SQL Γ s1)
             (b: SQL Γ s2) (c1: Column ty s1)
             (c2: Column ty s2) : SQL Γ s1.
  pose (c1' := @variable ty ((Γ ++ s1) ++ s2) (left⋅right⋅c1)).
  pose (c2' := @variable ty ((Γ ++ s1) ++ s2) (right⋅c2)).
  refine (SELECT * FROM1 a WHERE EXISTS (SELECT * FROM1 _ WHERE (equal c1' c2'))).
  refine (castSQL left b).
  Defined.

  Definition semiJoin {Γ s1 s2} (a: SQL Γ s1) (b: SQL Γ s2)
             (slct: Pred (Γ ++ s1 ++ s2)): SQL Γ s1.
    refine (SELECT * FROM1 a WHERE EXISTS (SELECT * FROM1 (castSQL left b) WHERE (castPred _ slct) )).
    refine (combine (left⋅left) (combine (left⋅right) right)).
  Defined.

  (* SEMI JOIN with single equality predicate *)
  Notation "a 'SEMI_JOIN1' b 'ON' 'SEQ' c1 , c2 " := (semiJoin1 a b c1 c2) (at level 45).

  (* SEMI JOIN with predicate *)
  Notation "a 'SEMI_JOIN' b 'ON' slct " := (semiJoin a b slct) (at level 45).
  
  Notation "'PLAIN' ( e )" := (plainGroupByProjection e).
  Notation "'SELECT' proj0 , proj1 'FROM1' a 'GROUP' 'BY' v " := (groupBy a v proj0 proj1) (at level 45).

End SQL.
