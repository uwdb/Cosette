Class Denotation A B := {
  denote : A -> B
}.

Notation "⟦ X ⟧" := (denote X) (at level 9, X at level 7).
