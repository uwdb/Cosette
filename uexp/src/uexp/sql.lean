import .u_semiring
constant relation : Schema → Type
constant aggregator : datatype → datatype → Type
constant const : datatype →  Type
constant unary: datatype → datatype → Type
constant binary: datatype → datatype → datatype → Type

noncomputable definition Relation (s : Schema) := Tuple s → usr
definition Query (Γ s: Schema) := Tuple Γ → Relation s.

constant denote_r : forall s, relation s → Relation s
constant denote_a : forall s t, aggregator s t → (Relation (tree.leaf s) → Tuple (tree.leaf t))
constant denote_c : forall t, const t → Tuple (tree.leaf t) 
constant denote_u : forall s t, unary s t → (Tuple (tree.leaf s) → Tuple (tree.leaf t))
constant denote_b : forall s t u, binary s t u → (Tuple (tree.leaf s) → Tuple (tree.leaf t) → Tuple (tree.leaf u))

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
| e2p {T Γ} : Expr Γ T → Proj Γ (tree.leaf T)
| erase    {Γ} : Proj Γ tree.empty

with Expr : Schema → datatype → Type
| uvariable {T Γ} (proj:Proj Γ (tree.leaf T)) : Expr Γ T
| aggregate {Γ S T} : aggregator S T → SQL Γ (tree.leaf S) → Expr Γ T
| constantExpr {Γ S} : const S → Expr Γ S
| unaryExpr {Γ S T} : unary S T → Expr Γ S → Expr Γ T
| binaryExpr {Γ S T U} : binary S T U → Expr Γ S → Expr Γ T → Expr Γ U
| castExpr {Γ Γ' T} : Proj Γ Γ' → Expr Γ' T → Expr Γ T

noncomputable mutual def denoteSQL, denotePred, denoteProj, denoteExpr
with denoteSQL : forall {Γ s} (a: SQL Γ s), Query Γ s 
| _ _ (SQL.table r) := λ _, (denote_r _ r)  
| _ _ (SQL.union q₁ q₂):= λ g t, denoteSQL q₁ g t + denoteSQL q₂ g t 
| _ _ (SQL.minus q₁ q₂) := λ g t, denoteSQL q₁ g t * (usr.not ∥ denoteSQL q₂ g t ∥ )
| _ _ (SQL.select p q) := λ g t, (denotePred p (g, t)) * (denoteSQL q g t)
| _ _ (SQL.product q₁ q₂) := λ g t, (denoteSQL q₁ g t.1) * (denoteSQL q₂ g t.2)
| _ _ (SQL.project proj q) := λ g t', ∑ t, denoteSQL q g t * (denoteProj proj (g, t) ≃  t')
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
| _ _ (Proj.combine proj₁ proj₂) := λ t, (denoteProj proj₁ t, denoteProj proj₂ t)
| _ _ Proj.left := prod.fst
| _ _ Proj.right := prod.snd
| _ _ (Proj.compose proj₁ proj₂) := λ t, denoteProj proj₂ (denoteProj proj₁ t)
| _ _ Proj.star := λ t, t
| _ _ (Proj.e2p e) := λ t, denoteExpr e t
| _ _ Proj.erase := λ t, unit.star
with denoteExpr: forall {Γ T} (e : Expr Γ T), Tuple Γ → Tuple (tree.leaf T)
| _ _ (Expr.uvariable proj) := λ g, denoteProj proj g
| _ _ (Expr.aggregate aggr q) := λ g, denote_a _ _ aggr (denoteSQL q g)
| _ _ (Expr.constantExpr c) := λ g, denote_c _ c
| _ _ (Expr.unaryExpr f e) := λ g, denote_u _ _ f (denoteExpr e g)
| _ _ (Expr.binaryExpr f e₁ e₂) := λ g, denote_b _ _ _ f (denoteExpr e₁ g) (denoteExpr e₂ g)
| _ _ (Expr.castExpr f e) := λ g, denoteExpr e (denoteProj f g)  
using_well_founded { 
    dec_tac := tactic.admit}

notation p1 `⋅` p2 := (Proj.compose p1 p2)
notation Γ `⊢` x `~` s := (x:(SQL Γ s))
notation a `WHERE` c := (SQL.select c a) 
notation `SELECT` `*` a := (a)
-- notation `SELECT1` proj q := (Proj.project proj q)
notation `FROM1` a := (a) 
notation `FROM2` a , b := (SQL.product a b) 
notation a `UNION` `ALL` b := (SQL.union a b)
notation a `MINUS` b := (SQL.minus a b) 
notation `EXISTS` s := (Pred.inhabited s)
notation s0 `AND` s1 := (Pred.and s0 s1)
notation s0 `OR` s1 := (Pred.or s0 s1) 
notation `NOT` s0 := (Pred.negate s0)
notation `FALSE` := (Pred.false) 
notation `TRUE` := (Pred.true) 
notation `DISTINCT` s := (SQL.distinct s)