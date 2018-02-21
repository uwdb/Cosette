import .u_semiring

constant relation : Schema → Type
constant aggregator : datatype → datatype → Type
constant const : datatype →  Type
constant unary: datatype → datatype → Type
constant binary: datatype → datatype → datatype → Type

definition Relation (s : Schema) := Tuple s → usr
definition Query (Γ s: Schema) := Tuple Γ → Relation s.

constant denote_r : forall s, relation s → Relation s
constant denote_a : forall s t, aggregator s t → (Relation (tree.leaf s) → denote t)
constant denote_c : forall t, const t → denote t 
constant denote_u : forall s t, unary s t → (denote s → denote t)
constant denote_b : forall s t u, binary s t u → (denote s → denote t → denote u)

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
| uvariable {T Γ} (c:Proj Γ (tree.leaf T)) : Expr Γ T
| aggregate {Γ S T} : aggregator S T → SQL Γ (tree.leaf S) → Expr Γ T
| constantExpr {Γ S} : const S → Expr Γ S
| unaryExpr {Γ S T} : unary S T → Expr Γ S → Expr Γ T
| binaryExpr {Γ S T U} : binary S T U → Expr Γ S → Expr Γ T → Expr Γ U
| castExpr {Γ Γ' T} : Proj Γ Γ' → Expr Γ' T → Expr Γ T

mutual def denoteSQL, denotePred, denoteProj, denoteExpr
with denoteSQL : forall {Γ s} (a: SQL Γ s), Query Γ s
with denotePred : forall {Γ}, Pred Γ →  Tuple Γ → usr
with denoteProj: forall {Γ Γ'} (cast: Proj Γ Γ'), Tuple Γ  → Tuple Γ'
with denoteExpr: forall {Γ T} (e : Expr Γ T), Tuple Γ → denote T
    
