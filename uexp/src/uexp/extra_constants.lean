import .sql
import .u_semiring

open tree

namespace datatypes

constant int : datatype

end datatypes

namespace aggregators

constant count {T} : aggregator T datatypes.int
notation `COUNT` `(` e `)` := aggregatorGroupByProj count e

constant sum {T} : aggregator T datatypes.int
notation `SUM` `(` e `)` := aggregatorGroupByProj sum e

constant max {T} : aggregator T datatypes.int
notation `MAX` `(` e `)` := aggregatorGroupByProj max e

constant min {T} : aggregator T datatypes.int
notation `MIN` `(` e `)` := aggregatorGroupByProj min e

constant avg {T} : aggregator T datatypes.int
notation `AVG` `(` e `)` := aggregatorGroupByProj avg e

end aggregators

namespace predicates

constant gt : Pred (leaf datatypes.int ++ leaf datatypes.int)
infix `>u`:50 := gt

end predicates

namespace binary_operators

constant add_ : binary datatypes.int datatypes.int datatypes.int
constant divide_ : binary datatypes.int datatypes.int datatypes.int

end binary_operators

constant null {T : datatype} : const T

axiom pred_cancel {s: Schema} {p: Pred s} {t: Tuple s}:
    (denotePred p t) * (denotePred p t) = (denotePred p t) 
