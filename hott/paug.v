Require Import HoTT.
Require Import UnivalenceAxiom.

Class Denotation A B := {
  denote : A -> B
}.

Notation "⟦ X ⟧" := (denote X) (at level 9, X at level 7).

Open Scope type.

Module Type Types.
  Parameter type : Type.
  Parameter denotationType : Denotation type Type.

  Parameter constant : type -> Type.
  Parameter unary : type -> type -> Type.
  Parameter binary : type -> type -> type -> Type.

  Parameter denotationConstant : forall S, Denotation (constant S) ⟦ S ⟧.
  Parameter denotationUnary : forall S T, Denotation (unary S T) (⟦ S ⟧ -> ⟦ T ⟧).
  Parameter denotationBinary : forall S T U, Denotation (binary S T U) (⟦ S ⟧ -> ⟦ T ⟧ -> ⟦ U ⟧).
End Types.

(* Now we show to different SQL denotations: *)
(* One we call it abstract, one we call it concrete. *)

(* -------------------------------------------------------------------------- *)
(* SQL denotation with abstract schema, mostly formalize the Alice book. *)

Module ASQLDenotation (T : Types).
  Import T.

  (* definition of inductive types in 
     modules isn't supported by Coq in this case *)
  Definition Schema := {column : Type & column -> type}.
  Definition column (s : Schema) := s.1.
  Definition types (s : Schema) (c : column s) := (s.2) c.

  (* NOTE we could have `Tuple s -> nat` for the bag semantics,
          but this is more general as we support infinite types.
          this is useful for projection *)
  Definition Tuple s := forall c:column s, ⟦types s c⟧.
  Definition Relation s := Tuple s -> Type.
  Definition Query Γ s := Tuple Γ -> Relation s.
End ASQLDenotation.

Module Type ASchemas (T : Types).
  Import T.
  Module TD := ASQLDenotation T.
  Import TD.
  Export TD.

  Parameter relationSchema : Type.
  Parameter relationColumn : relationSchema -> Type.
  Parameter relationColumnType : forall s, relationColumn s -> type.
End ASchemas.

Module Type ARelations (T : Types) (S : ASchemas T).
  Import T S.

  Parameter relation : relationSchema -> Type.
  Parameter denotationRelation : forall s, Denotation (relation s) (Relation (relationColumn s; relationColumnType _)).
End ARelations.

Module ASQL  (T : Types) (S : ASchemas T) (R : ARelations T S).
  Import T S R. 

  Inductive schema :=
  | schemaEmpty : schema
  | schemaCons : type -> schema -> schema
  | schemaProduct : schema -> schema -> schema
  | schemaLeaf : relationSchema -> schema.

  Notation "s0 ++ s1" := (schemaProduct s0 s1).

  Fixpoint denoteSchema (s : schema) : Schema.
    refine (match s with
    | schemaEmpty => _ 
    | schemaCons t s => _ 
    | schemaProduct s0 s1 => _
    | schemaLeaf s => _
            end).
    - refine (Empty; _).
      exact (Empty_rect _).
    - simple refine (_; _).
      refine (option (column (denoteSchema s))).
      exact (fun c => match c with None => t | Some c => types _ c end).
    - simple refine (_; _).
      refine (column (denoteSchema s0) + column (denoteSchema s1)).
      exact (fun c => match c with 
                    | inl c => types (denoteSchema s0) c 
                    | inr c => types (denoteSchema s1) c 
                    end).
    - exact (relationColumn s;  relationColumnType _).      
  Defined.

  Definition comb {s0 s1} : Tuple ⟦s0⟧ -> Tuple ⟦s1⟧ -> Tuple (⟦s0 ++ s1⟧).
    intros t0 t1.
    refine (fun c => match c with | inl c => t0 c
            | inr c => t1 c
            end).
  Defined.
 
End ASQL.

(*--------------------------------------------------------------------------*)
(* SQL denotation with concrete schema *)

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
  Definition Schema := Tree type.
  Definition singleton := @leaf type.
  Notation "s0 ++ s1" := (node s0 s1).

  Fixpoint Tuple (s:Schema) : Type.
    refine (match s with
    | node t0 t1 => (Tuple t0) * (Tuple t1)
    | leaf T => ⟦T⟧
    | empty => Unit
    end).
  Defined.

  (* NOTE we could have `Tuple s -> nat` for the bag semantics,
          but this is more general as we support infinite types.
          this is useful for projection *)
  Definition Relation s := Tuple s -> Type.
  Definition Query Γ s := Tuple Γ -> Relation s.
End SQLDenotation.

Module Type Schemas (T : Types).
  Import T.
  Module TD := SQLDenotation T.
  Import TD.
  Export TD.
End Schemas.

Module Type Relations (T : Types) (S : Schemas T).
  Import T S.

  Parameter relation : Schema -> Type.
  Parameter denotationRelation : forall s, Denotation (relation s) (Relation s).
End Relations.

