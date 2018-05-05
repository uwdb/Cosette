import .u_semiring
open tree

constant relation : Schema → Type
constant aggregator : datatype → datatype → Type
constant const : datatype →  Type
constant unary: datatype → datatype → Type
constant binary: datatype → datatype → datatype → Type

noncomputable definition Relation (s : Schema) := Tuple s → usr
definition Query (Γ s: Schema) := Tuple Γ → Relation s.

constant denote_r : forall {s}, relation s → Relation s
constant denote_a : forall {s t}, aggregator s t → (Relation (leaf s) → Tuple (leaf t))
constant denote_c : forall {t}, const t → Tuple (leaf t) 
constant denote_u : forall {s t}, unary s t → (Tuple (leaf s) → Tuple (leaf t))
constant denote_b : forall {s t u}, binary s t u → (Tuple (leaf s) → Tuple (leaf t) → Tuple (leaf u))

-- desugared SQL AST/IR
mutual inductive SQL, Pred, Proj, Expr
with SQL : Schema → Schema → Type
| table {Γ s} : relation s → SQL Γ s
| union {Γ s} : SQL Γ s → SQL Γ s → SQL Γ s
| minus {Γ s} : SQL Γ s → SQL Γ s → SQL Γ s
| select  {Γ s} : Pred (Γ ++ s) → SQL Γ s → SQL Γ s
| product {Γ s0 s1} : SQL Γ s0 → SQL Γ s1 → SQL Γ (s0 ++ s1)
| project {Γ s s'} : Proj (Γ ++ s) s' → SQL Γ s → SQL Γ s'
| distinct {Γ s} : SQL Γ s → SQL Γ s
| castSQL{Γ Γ' s} : Proj Γ Γ' → SQL Γ' s → SQL Γ s

with Pred : Schema → Type
| inhabited {Γ s} : SQL Γ s → Pred Γ
| equal {Γ T} : Expr Γ T → Expr Γ T → Pred Γ
| negate {Γ} : Pred Γ → Pred Γ
| and {Γ} : Pred Γ → Pred Γ → Pred Γ
| or {Γ} : Pred Γ → Pred Γ → Pred Γ
| false {Γ} : Pred Γ
| true {Γ} : Pred Γ
| castPred {Γ Γ'} : Proj Γ Γ' → Pred Γ' → Pred Γ

with Proj : Schema → Schema → Type
| combine  {Γ Γ0 Γ1} : Proj Γ Γ0 → Proj Γ Γ1 → Proj Γ (Γ0 ++ Γ1)
| left  {Γ0 Γ1} : Proj (Γ0 ++ Γ1) Γ0
| right  {Γ0 Γ1} : Proj (Γ0 ++ Γ1) Γ1
| compose  {Γ Γ' Γ''} : Proj Γ Γ' → Proj Γ' Γ'' → Proj Γ Γ''
| star     {Γ} : Proj Γ Γ
| e2p {T Γ} : Expr Γ T → Proj Γ (leaf T)
| erase    {Γ} : Proj Γ empty

with Expr : Schema → datatype → Type
| uvariable {T Γ} (proj:Proj Γ (leaf T)) : Expr Γ T
| aggregate {Γ S T} : aggregator S T → SQL Γ (leaf S) → Expr Γ T
| constantExpr {Γ S} : const S → Expr Γ S
| unaryExpr {Γ S T} : unary S T → Expr Γ S → Expr Γ T
| binaryExpr {Γ S T U} : binary S T U → Expr Γ S → Expr Γ T → Expr Γ U
| castExpr {Γ Γ' T} : Proj Γ Γ' → Expr Γ' T → Expr Γ T

noncomputable mutual def denoteSQL, denotePred, denoteProj, denoteExpr
with denoteSQL : forall {Γ s} (a: SQL Γ s), Query Γ s 
| _ _ (SQL.table r) := λ _, (denote_r r)  
| _ _ (SQL.union q₁ q₂):= λ g t, denoteSQL q₁ g t + denoteSQL q₂ g t 
| _ _ (SQL.minus q₁ q₂) := λ g t, denoteSQL q₁ g t * (usr.not ∥ denoteSQL q₂ g t ∥ )
| _ _ (SQL.select p q) := λ g t, (denotePred p (pair g t)) * (denoteSQL q g t)
| _ _ (SQL.product q₁ q₂) := λ g t, (denoteSQL q₁ g t.1) * (denoteSQL q₂ g t.2)
| _ _ (SQL.project proj q) := λ g t', ∑ t, denoteSQL q g t * (denoteProj proj (pair g t) ≃  t')
| _ _ (SQL.distinct q) := λ g t, ∥ denoteSQL q g t ∥ 
| _ _ (SQL.castSQL f q) := λ g t, denoteSQL q (denoteProj f g) t
with denotePred : forall {Γ}, Pred Γ →  Tuple Γ → usr
| _ (Pred.inhabited q) := λ g, ∥ (∑ t, denoteSQL q g t) ∥ 
| _ (Pred.equal e₁ e₂) := λ g, (denoteExpr e₁ g ≃ denoteExpr e₂ g)
| _ (Pred.negate p) := λ g, usr.not (denotePred p g)
| _ (Pred.and p₁ p₂) := λ g, (denotePred p₁ g) * (denotePred p₂ g)
| _ (Pred.or p₁ p₂) := λ g, ∥ (denotePred p₁ g) + (denotePred p₂ g) ∥
| _ Pred.false := λ _, 0
| _ Pred.true := λ _, 1
| _ (Pred.castPred f p) := λ g, denotePred p (denoteProj f g)
with denoteProj: forall {Γ Γ'} (proj: Proj Γ Γ'), Tuple Γ  → Tuple Γ'
| _ _ (Proj.combine proj₁ proj₂) := λ t, pair (denoteProj proj₁ t) (denoteProj proj₂ t)
| _ _ Proj.left := prod.fst
| _ _ Proj.right := prod.snd
| _ _ (Proj.compose proj₁ proj₂) := λ t, denoteProj proj₂ (denoteProj proj₁ t)
| _ _ Proj.star := λ t, t
| _ _ (Proj.e2p e) := λ t, denoteExpr e t
| _ _ Proj.erase := λ t, unit.star
with denoteExpr: forall {Γ T} (e : Expr Γ T), Tuple Γ → Tuple (leaf T)
| _ _ (Expr.uvariable proj) := λ g, denoteProj proj g
| _ _ (Expr.aggregate aggr q) := λ g, denote_a aggr (denoteSQL q g)
| _ _ (Expr.constantExpr c) := λ g, denote_c c
| _ _ (Expr.unaryExpr f e) := λ g, denote_u f (denoteExpr e g)
| _ _ (Expr.binaryExpr f e₁ e₂) := λ g, denote_b f (denoteExpr e₁ g) (denoteExpr e₂ g)
| _ _ (Expr.castExpr f e) := λ g, denoteExpr e (denoteProj f g)  
using_well_founded { 
    dec_tac := tactic.admit}

infix `⋅`:80 := Proj.compose
--notation Γ `⊢` x `:` s := (x:(SQL Γ s))
notation a `WHERE`:45 c:45 := SQL.select c a
notation `SELECT`:45 `*` a := a
notation `SELECT1`:45 := SQL.project
noncomputable definition projectSingleton {Γ T s} (e : Expr (Γ ++ s) T)
  := Proj.e2p e
noncomputable definition projectNil {Γ s}
  : Proj (Γ ++ s) empty := Proj.erase
noncomputable definition projectCons {Γ T s s'}
  (e : Expr (Γ ++ s) T)
  (proj : Proj (Γ ++ s) s')
  : Proj (Γ ++ s) (node (leaf T) s')
  := Proj.combine (Proj.e2p e) proj
noncomputable definition select2 {Γ s : Schema} {T T' : datatype}
    (proj0 : Expr (Γ ++ s) T)
    (proj1 : Expr (Γ ++ s) T')
    := SELECT1 (projectCons proj0
               $ projectCons proj1
                 projectNil)
notation `SELECT2`:45 := select2
    
notation `FROM1`:45 a := a
notation `FROM2`:45 a `,` b := (SQL.product a b) 
notation a `UNION`:45 `ALL` b := (SQL.union a b)
notation a `MINUS`:45 b := (SQL.minus a b) 
notation `EXISTS`:45 s := (Pred.inhabited s)
notation s0 `AND`:45 s1 := (Pred.and s0 s1)
notation s0 `OR`:45 s1 := (Pred.or s0 s1) 
notation `NOT`:45 s0 := (Pred.negate s0)
notation `FALSE`:45 := (Pred.false) 
notation `TRUE`:45 := (Pred.true) 
notation `DISTINCT`:45 s := (SQL.distinct s)

definition Column (T : datatype) (Γ : Schema) := Proj Γ (leaf T)

open SQL
open Proj
open Expr

section constraints

noncomputable definition Index {Γ s t0 t1}
  (R : SQL Γ s) (k : Column t0 s) (ic : Column t1 s) :=
  SELECT2 (uvariable (right ⋅ k)) (uvariable (right ⋅ ic)) FROM1 R

definition isKey {s ty} (k : Column ty s) (R : relation s) :=
  Π t : Tuple s,
  denote_r R t = (∑ t', (denoteProj k t' ≃ denoteProj k t)
                      * denote_r R t' * denote_r R t)

definition fKey {s1 s2 ty} (k : Column ty s1)
                (fk : Column ty s2) (R : relation s1)
                (S : relation s2) (pk : isKey k R) :=
    forall (t : Tuple s2),
      denote_r S t = (∑ t': Tuple s1, (denoteProj k t' ≃ denoteProj fk t)
                                    * denote_r R t' * denote_r S t)

end constraints

section groupByProjections
/-
A group by projection has access to the context, a selected tuple t,
and a query that returns all tuples that match t
-/
definition GroupByProj (Γ s s') := SQL (Γ ++ s) s → Proj (Γ ++ s) s'

noncomputable definition combineGroupByProj {Γ s s' s''}
  (p1 : GroupByProj Γ s s') (p2 : GroupByProj Γ s s'')
  : GroupByProj Γ s (s' ++ s'') := λ a, combine (p1 a) (p2 a)

definition plainGroupByProj {Γ s s'}
  (p : Proj (Γ ++ s) s') : GroupByProj Γ s s' := λ _, p

noncomputable definition aggregatorGroupByProj {Γ s S T}
  : aggregator S T → Expr (Γ ++ s) S → GroupByProj Γ s (leaf T)
  := λ agg e sql,
  let ll_r : Proj (Γ ++ s ++ s) (Γ ++ s)
      := (left.compose left).combine right,
      e_proj : Proj (Γ ++ s ++ s) (leaf S)
      := e2p $ castExpr ll_r e
  in e2p $ aggregate agg $ SELECT1 e_proj FROM1 sql

noncomputable definition proj_agree {Γ} : Π {s}, Proj Γ s → Proj Γ s → Pred Γ
| (node x y) p0 p1 := proj_agree (p0.compose left) (p1.compose left)
                AND proj_agree (p0.compose right) (p1.compose right)
| (leaf t) p0 p1 := Pred.equal (uvariable p0) (uvariable p1)
| empty _ _ := TRUE

noncomputable definition groupBy {Γ s s' C}
  (gb_proj : GroupByProj Γ s s')
  (query : SQL Γ s)
  (proj2c : Proj (Γ ++ s) C)
  : SQL Γ s' :=
  let ll_r : Proj (Γ ++ s ++ s) (Γ ++ s)
      := combine (left⋅left) right,
      -- This should have a more descriptive name
      subquery : SQL (Γ ++ s) s
      := SELECT * FROM1 query.castSQL left 
         WHERE proj_agree (left ⋅ proj2c)
                          (ll_r ⋅ proj2c)
  in DISTINCT SELECT1 (gb_proj subquery) FROM1 query

notation `PLAIN` `(` e `)` := plainGroupByProj (e2p e)
notation `SELECT` proj `FROM1`:1 a `GROUP` `BY` v := groupBy proj a v

end groupByProjections
