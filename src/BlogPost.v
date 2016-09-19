(**
SQL is the lingua franca for retrieving structured data. Existing semantics for SQL, however, either do not model crucial features of the language (e.g., relational algebra lacks bag semantics, correlated subqueries, and aggregation), or make it hard to formally reason about SQL query rewrites (e.g., the SQL standard's English is too informal). This post focuses on the ways that HoTT concepts (e.g., Homotopy Types, the Univalence Axiom, and Truncation) enabled us to develop HoTTSQL — a new SQL semantics that makes it easy to formally reason about SQL query rewrites. Our #<a href="https://arxiv.org/abs/1607.04822">paper</a># also details the rich set of SQL features supported by HoTTSQL.

You can download this #<a href="https://github.com/uwdb/DopCert/blob/master/src/BlogPost.v">blog post's source</a># (implemented in Coq using the #<a href="https://github.com/HoTT/HoTT">HoTT library</a>#). Learn more about HoTTSQL by visiting our #<a href="http://cosette.cs.washington.edu/">website</a>#.
**)

(* begin hide *)
Require Import HoTT.
Require Import UnivalenceAxiom.
(* end hide *)

(** ** Relations

The basic datatype in SQL is a relation, which is a _bag_ (i.e., multiset) of tuples with the same given schema. You can think of a tuple's schema as being like a variable's type in a programming language. We formalize a bag of some type [A] as a function that maps every element of [A] to a type.  The type's cardinality indicates how many times the element appears in the bag.
**)

Definition Bag A := A -> Type.

(**
For example, the bag [numbers = {| 7, 42, 7 |}] can be represented as:
**)

Definition numbers : Bag nat :=
  fun n => match n with
  | 7 =>  Bool
  | 42 => Unit
  | _ =>  Empty
  end.

(**
A SQL query maps one or more input relations to an output relation.  We can implement SQL queries as operations on bags.  For example, a disjoint union query in SQL can be implemented as a function that takes two input bags [r1] and [r2], and returns a bag in which every tuple [a] appears [r1 a + r2 a] times. Note that the cardinality of the sum type [r1 a + r2 a] is equal to the sum of the cardinalities of [r1 a] and [r2 a].  
**)

Definition bagUnion {A} (r1 r2:Bag A) : Bag A := 
  fun (a:A) => r1 a + r2 a.

(**
Most database systems contain a query optimizer that applies SQL rewrite rules to improve query performance. We can verify SQL rewrite rules by proving the equality of two bags. For example, we can show that the union of [r1] and [r2] is equal to the union of [r2] and [r1], using functional extensionality ([by_extensionality]), the univalence axiom ([path_universe_uncurried]), and symmetry of the sum type ([equiv_sum_symm]).
**)

Lemma bag_union_symm {A} (r1 r2 : Bag A) :
  bagUnion r1 r2 = bagUnion r2 r1.
Proof.
  unfold bagUnion.
  by_extensionality a.
  (* r1 a + r1 a = r2 a + r2 a *)
  apply path_universe_uncurried.
  (* r1 a + r1 a <~> r2 a + r2 a *)
  apply equiv_sum_symm.
Qed.

(**
Note that [+] and [*] on homotopy types are _like_ the operations of a commutative semi-ring, [Empty] and [Unit] are _like_ the identity elements of a commutative semi-ring, and there are paths witnessing the commutative semi-ring axioms for these operations and identity elements. We use the terminology _like_ here, because algebraic structures over higher-dimensional types in HoTT are usually defined using coherence conditions between the equalities witnessing the structure's axioms, which we have not yet attempted to prove.

Many SQL rewrite rules simplify to an expressions built using the operators of this semi-ring (e.g. [r1 a + r1 a = r2 a + r2 a] above), and could thus be potentially solved or simplified using a [ring] tactic (#<a href="https://coq.inria.fr/refman/Reference-Manual028.html">see</a>#). Unfortunately, Coq's [ring] tactic is not yet ported to the HoTT library. Porting [ring] may dramatically simplify many of our proofs (Anyone interested in porting the [ring] tactic? Let us know). 

It is reasonable to assume that SQL relations are bags that map tuples only to 0-truncated types (types with no higher homotopical information), because real-world databases' input relations only contain tuples with finite multiplicity ([Fin n] is 0-truncated), and because SQL queries only use type operators that preserve 0-truncation. However, HoTTSQL does not requires this assumption, and as future work, it may be interesting to understand what the "cardinality" of a type with higher homotopical information means.
**)

(* begin hide *)
Section Algebra.
  Class SemiRing : Type := {
    T : Type;
    O : T;
    I : T;
    plus : T -> T -> T;
    times : T -> T -> T;
  
    plusO n : plus O n = n;
    plusSym n m : plus n m = plus m n;
    plusAssoc n m p : plus n (plus m p) = plus (plus n m) p;
    timesI n : times I n = n;
    timesO n : times O n = O;
    timesSym n m : times n m = times m n;
    timesAssoc n m p : times n (times m p) = times (times n m) p;
    distr n m p : times (plus n m) p = plus (times n p) (times m p)
  }.
  
  Instance SemiRingHSet : SemiRing. 
    refine {|
      T := hSet;
      O := BuildhSet Empty;
      I := BuildhSet Unit;
      plus x y := BuildhSet (x + y);
      times x y := BuildhSet (x * y)
    |}.
  Proof.
    all: intros; simpl; apply path_trunctype.
    - apply sum_empty_l.
    - apply equiv_sum_symm. 
    - symmetry. apply equiv_sum_assoc.
    - apply prod_unit_l.
    - apply prod_empty_l. 
    - apply equiv_prod_symm.
    - apply equiv_prod_assoc.
    - apply sum_distrib_r.
  Defined.
End Algebra.
(* end hide *)

(**
How to model bags is a fundamental design decision for mechanizing formal proofs of SQL query equivalences. Our formalization of bags is unconventional but effective for reasoning about SQL query rewrites, as we will see.

Previous work has modeled bags as _lists_ (e.g., as done by #<a href="https://dl.acm.org/citation.cfm?doid=1707801.1706329">Malecha et al.</a>#), where SQL queries are recursive functions over input lists, and two bags are equal iff their underlying lists are equal up to element reordering. Proving two queries equal thus requires induction on input lists (including coming up with induction hypothesis) and reasoning about list permutations. In contrast, by modeling bags as functions from tuples to types, proving two queries equal just requires proving the equality of two HoTT types.

In the database research community, prior work has modeled bags as _functions to natural numbers_ (e.g., as done by #<a href="https://dl.acm.org/citation.cfm?doid=1265530.1265535">Green et al.</a>#). Using this approach, one cannot define the potentially infinite sum [∑ a, r a] that counts the number of elements in a bag [r]. This is important since a basic operation in SQL, projection, requires counting all tuples in a bag that match a certain predicate. In contrast, by modeling bags as functions from tuples to types, we can count the number of elements in a bag using the sigma type [∑], where the cardinality of the sigma type [∑ a, r a] is equal to the sum of the cardinalities of [r a] for all [a].
**)

(** ** Schemas

Traditionally, a relation is modeled as a bag of [n]-ary tuples, and a relation's _schema_ both describes how many elements there are in each tuple (i.e., [n]), and the the type of each element. Thus, a schema is formalized as a list of types.

In HoTTSQL, a relation is modeled as a bag of nested pairs (nested binary-tuples), and a relation's schema both describes the nesting of the pairs and the types of the leaf pairs. In HoTTSQL, a schema is thus formalized as a binary tree, where each node stores only its child nodes, and each leaf stores a type. Our formalization of schemas as trees and tuples as nested pairs is unconventional. We will see later how this choice simplifies reasoning.
**)

Inductive Schema := 
| node (s1 s2 : Schema)
| leaf (T:Type)
.

(**
For example, a schema for people (with a name, age, and employment status) can be expressed as [Person : Schema := node (leaf Name) (node (leaf Nat) (leaf Bool))].
 
We formalize a _tuple_ as a function [Tuple] that takes a schema [s] and returns a nested pair which matches the tree structure and types of [s].
**)

Fixpoint Tuple (s:Schema) : Type :=
  match s with
  | node s1 s2 => Tuple s1 * Tuple s2
  | leaf T => T
  end.

(**
For example, [Tuple Person = Name * (Nat * Bool)] and [(Alice, (23, false)) : Tuple Person].

Finally, we formalize a _relation_ as a bag of tuples that match a given schema [s]. 
**)

Definition Relation (s:Schema) := Bag (Tuple s).

(* begin hide *)
Inductive Name := Alice | Bob.
Definition Nat := nat.
Definition Person : Schema := node (leaf Name) (node (leaf Nat) (leaf Bool)).

Definition person : Tuple Person := (Alice, (23, false)).

Definition people : Relation Person :=
  fun t => match t with
  | (alice, (23, false)) => Unit
  | (bob, (27, true)) => Bool
  | _ => Empty
  end.

Class Denotation A B := {
  denote : A -> B
}.
Notation "⟦ X ⟧" := (denote X) (at level 9, X at level 7).

Variable Pred : Schema -> Type.
Variable denotePred : forall {s}, Pred s -> Tuple s -> Type.

Instance denotationPred s : Denotation (Pred s) _ := {| 
  denote := denotePred
|}.

Module SimpleSubset.
(* end hide *)

(** ** Queries

Recall that a SQL query maps one or more input relations to an output relation, and that we can implement SQL queries with operations on bags. In this section, we incrementally introduce various SQL queries, and describe their semantics in terms of bags.

*** Union and Selection

The following subset of the SQL language supports unioning relations, and selecting (i.e., filtering) tuples in a relation.
**)

Inductive SQL : Schema -> Type :=
| union {s} : SQL s -> SQL s -> SQL s
| select {s} : Pred s -> SQL s -> SQL s
(* ... *)
.

Fixpoint denoteSQL {s} (q : SQL s) : Relation s :=
  match q with 
  | union _ q1 q2 => fun t => denoteSQL q1 t + denoteSQL q2 t
  | select _ b q => fun t => denotePred b t * denoteSQL q t 
  (* ... *)
  end.

(* begin hide *)
Instance denotationSQL s : Denotation (SQL s) _ := {| 
  denote := denoteSQL 
|}.

Notation "q1 'UNION' 'ALL' q2" := (union q1 q2) (at level 45).
Notation "q 'WHERE' b" := (select b q) (at level 45, b at level 45).
Notation "'SELECT' '*' 'FROM' q" := q (q at level 45, at level 45).
(* end hide *)

(**
The query [select b q] removes all the tuples from the relation returned by the query [q] where the predicate [b] does not hold.  We denote the predicate as a function [denotePred(b) : Tuple s -> Type] that maps a tuple to a (-1)-truncated type. [denotePred(b) t] is [Unit] if the predicate holds for [t], and [Empty] otherwise. The query multiplies the relation with the predicate to implement the semantics of the query (i.e., [n * Unit = n] and [n * Empty = Empty], where [n] is the multiplicity of the input tuple [t]).

To syntactically resemble SQL, we write [q1 UNION ALL q2] for [union q1 q2], [q WHERE b] for [select b q], and [SELECT * FROM q] for [q].  We write [⟦q⟧] for the denotation of a query [denoteQuery q], and [⟦b⟧] for the denotation of a predicate [denotePred b]. 

To prove that two SQL queries are equal, one has to prove that their two denotations are equal, i.e., that two bags returned by the two queries are equal, given any input relation(s). The following example shows how we can prove that selection distributes over union, by reducing it to showing the distributivity of [*] over [+] (lemma [sum_distrib_l]).
**)

Lemma proj_union_distr s (q1 q2 : SQL s) (p:Pred s) :
  ⟦ SELECT * FROM (q1 UNION ALL q2) WHERE p ⟧ =
  ⟦ (SELECT * FROM q1 WHERE p) UNION ALL 
    (SELECT * FROM q2 WHERE p) ⟧.
Proof.
  simpl.
  by_extensionality t.
  (* ⟦p⟧ t * (⟦q1⟧ t + ⟦q2⟧ t) = ⟦p⟧ t * ⟦q1⟧ t + ⟦p⟧ t * ⟦q2⟧ t *)
  apply path_universe_uncurried.
  apply sum_distrib_l.
Qed.

(* begin hide *)
End SimpleSubset.
(* end hide *)

(**

*** Duplicate Elimination, Products, and Projections

So far, we have seen the use of homotopy types to model SQL relations, and have seen the use of the univalence axiom to prove SQL rewrite rules. We now show the use of truncation to model the removal of duplicates in SQL relations. To show an example of duplicate removal in SQL, we first have to extend our semantics of the SQL language with more features. 
**)

(* begin hide *)
Notation "║ P ║" := (Trunc (-1) P) (at level 45).
Notation "∑ x , T" := (sigT (fun x => T)) (at level 45) : type_scope.
(* end hide *)

Inductive Proj : Schema -> Schema -> Type :=
| left  {s s'} : Proj (node s s') s
| right {s s'} : Proj (node s' s) s
(* ... *)
.

Inductive SQL : Schema -> Type :=
(* ... *)
| distinct {s} : SQL s -> SQL s
| product {s1 s2} : SQL s1 -> SQL s2 -> SQL (node s1 s2)
| project {s s'} : Proj s s' -> SQL s -> SQL s'
(* ... *)
.

Fixpoint denoteProj {s s'} (p : Proj s s') : Tuple s -> 
                                             Tuple s' :=
  match p with 
  | left  _ _ => fst
  | right _ _ => snd
  (* ... *)
  end.

Fixpoint denoteSQL {s} (q : SQL s) : Relation s :=
  match q with 
  (* ... *)
  | distinct _ q => fun t => ║ denoteSQL q t ║ 
  | product _ _ q1 q2 => fun t => denoteSQL q1 (fst t) * 
                                  denoteSQL q2 (snd t)
  | project _ _ p q => fun t' => ∑ t, denoteSQL q t * 
                                      (denoteProj p t = t')
  (* ... *)
  end.

(**
The query [distinct q] removes duplicate tuples in the relation returned by the query [q] using the (-1)-truncation function [║ q ║] (see HoTT book, chapter 3.7). 

The query [product q1 q2] creates the cartesian product of [q1] and [q2], i.e., it returns a bag that maps every tuple consisting of two tuples [t1] and [t2] to the number of times [t1] appears in [q1] multiplied by the number of times [t2] appears in [q2].

The query [project p q] projects elements from each tuple contained in the query [q]. The projection is defined by [p], and is denoted as a function that takes a tuple of some schema [s] and returns a new tuple of some schema [s']. For example, [left] is the projection that takes a tuple and returns the tuple's first element. We assume that tuples have no higher homotopical information, and that equality between tuples is thus (-1)-truncated. 

Like before, we write [DISTINCT q] for [distinct q], [FROM q1, q2] for [product q1 q2], and [SELECT p q] for [project p q].  We write [⟦p⟧] for the denotation of a projection [denoteProj p].

Projection of products is the reason HoTTSQL must model schemas as nested pairs. If schemas were flat n-ary tuples, the [left] projection would not know which elements of the tuple formerly belonged to the left input relation of the product, and could thus not project them (feel free to contact us if you have ideas on how to better represent schemas)

Projection requires summing over all tuples in a bag, as multiple tuples may be merged into one. This sum is over an infinite domain (all tuples) and thus cannot generally be implemented with natural numbers. Implementing it using the [∑] (sigma) type is however trivial.

Equipped with these additional features, we can now prove the following rewrite rule. 
**)

(* begin hide *)

Instance denotationProj s s' : Denotation (Proj s s') _ := {| 
  denote := denoteProj
|}.

Instance denotationSQL s : Denotation (SQL s) _ := {| 
  denote := denoteSQL 
|}.

Notation "'DISTINCT' q" := (distinct q) (at level 45).
Notation "'SELECT' p 'FROM' q1 , q2" := (project p (product q1 q2)) (p at level 45, at level 45).
Notation "'SELECT' '*' 'FROM' q" := q (q at level 45, at level 45).

Lemma equiv_iff_trunc (P Q : Type) : (P <-> Q) -> ║ P ║ = ║ Q ║.
  intros [pq qp].
  apply path_universe_uncurried.
  apply equiv_iff_hprop_uncurried.
  split; intros h; strip_truncations; apply tr; auto.
Qed.

Definition Tuple2Sum {A B P} : {a : A & {b : B & P (a,b)}} -> {ab : A * B & P ab}.
  intros h.
  refine ((h.1,h.2.1); h.2.2).
Defined.

Ltac rewriteall := repeat
  match goal with
  | t: _ = _ |- _ => rewrite t in *; clear t
  end.

Ltac solveInstantiatedConjuctiveQuery :=
  simpl; repeat constructor; rewriteall;
  first [reflexivity | assumption].

Ltac searchInstantiation solv :=
  match goal with
  | |- { _ : ?T0 * ?T1 & _ } => refine (Tuple2Sum _); searchInstantiation solv
  | t:Tuple ?T |- { _ : Tuple ?T & _ } => refine (t; _); searchInstantiation solv
  | |- _ => solv
  end.

Ltac prepareDistinctSQLProof :=
  let t := fresh "t" in
  simpl;
  by_extensionality t;
  apply equiv_iff_trunc;
  constructor.

Ltac prepareConjuctiveQueryProof :=
  let h := fresh "h" in
  let t0 := fresh "t0" in
  intros h; try destruct h as [t0 h];
  repeat match goal with
         | h:?A * ?B |- _ => destruct h
         end;
  simpl in *.

Ltac conjuctiveQueryProof :=
  prepareDistinctSQLProof;
  prepareConjuctiveQueryProof;  
  searchInstantiation solveInstantiatedConjuctiveQuery.

(* end hide *)

Lemma self_join s (q : SQL s) :
  ⟦ DISTINCT SELECT left FROM q, q ⟧ = 
  ⟦ DISTINCT SELECT * FROM q ⟧.
 
(**
The two queries are equal, because the left query performs a redundant self-join. Powerful database query optimizations, such as #<a href="https://dl.acm.org/citation.cfm?id=15399">magic sets rewrites</a># and #<a href="http://webdam.inria.fr/Alice/">conjunctive query equivalences</a># are based on redundant self-joins elimination.

To prove the equivalence of any two (-1)-truncated types [║ q1 ║] and [║ q2 ║], it suffices to prove the bi-implication [q1 <-> q2] (lemma [equiv_iff_trunc]). This is one of the cases where concepts from HoTT simplify formal reasoning in a big way. Instead of having to apply a series of equational rewriting rules (which is complicated by the fact that they need to be applied under the variable bindings of [Σ]), we can prove the goal using deductive reasoning.
**)

Proof.  
  simpl.
  by_extensionality t.
  (* ║ ∑ t', ⟦q⟧ (fst t') * ⟦q⟧ (snd t') * (fst t' = t) ║ =
     ║ ⟦q⟧ t ║ *)
  apply equiv_iff_trunc.
  split.
  - (* ∃ t', ⟦q⟧ (fst t') ∧ ⟦q⟧ (snd t') ∧ (fst t' = t) →
       ⟦q⟧ t *)
    intros [[t1 t2] [[h1 h2] eq]].
    destruct eq.
    apply h1.
  - (* ⟦q⟧ t → 
       ∃ t', ⟦q⟧ (fst t') ∧ ⟦q⟧ (snd t') ∧ (fst t' = t) *)
    intros h.
    exists (t, t).
    (* ⟦q⟧ t ∧ ⟦q⟧ t ∧ (t = t) *)
    split; [split|].
    + apply h.
    + apply h.
    + reflexivity.

(**
The queries in the above rewrite rule fall in the well-studied category of conjunctive queries where equality is decidable (while equality between arbitrary SQL queries is #<a href="https://scholar.google.com/scholar?q=Impossibility+of+an+algorithm+for+the+decision+problem+in+finite+classes.+Trakhtenbrot&btnG=&hl=en&as_sdt=0%2C48">undecidable</a>#). Using Coq's support for automating deductive reasoning (with Ltac), we have implemented a #<a href="https://dl.acm.org/citation.cfm?id=803397">decision procedure</a># for the equality of conjunctive queries (it's only 40 lines of code; see this posts source for details), the aforementioned rewrite rule can thus be proven in one line of Coq code. 
**)

Restart.
  conjuctiveQueryProof.
Qed.

(** ** Conclusion

We have shown how concepts from HoTT have enabled us to develop HoTTSQL, a SQL semantics that makes it easy to formally reason about SQL query rewrites.

We model bags of type [A] as a function [A -> Type].  Bags can be proven equal using the univalence axiom.  In contrast to models of bags as [list A], we require no inductive or permutation proofs.  In contrast to models of bags as [A -> nat], we can count the number of elements in any bag.

Duplicate elimination in SQL is implemented using (-1)-truncation, which leads to clean and easily automatable deductive proofs.  Many of our proofs could be further simplified with a [ring] tactic for the 0-trucated type semi-ring.

Visit our #<a href="http://cosette.cs.washington.edu/">website</a># to access our source code, learn how we denote other advanced SQL features such as correlated subqueries, aggregation, advanced projections, etc, and how we proved complex rewrite rules (e.g., magic set rewrites). 

#<a href="http://goo.gl/JTZLgq">Contact us</a># if you have any question, feedback, or know how to improve HoTTSQL (e.g., you know how to use more concepts from HoTT to extend HoTTSQL).
**)
