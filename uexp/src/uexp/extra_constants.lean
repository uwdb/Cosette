import .sql
import .u_semiring

open tree

namespace datatypes

constant int : datatype

end datatypes

namespace aggregators

constant count {T} : aggregator T datatypes.int
notation `COUNT` := aggregatorGroupByProj count

constant sum {T} : aggregator T datatypes.int
notation `SUM` := aggregatorGroupByProj sum

constant max {T} : aggregator T datatypes.int
notation `MAX` := aggregatorGroupByProj max

constant min {T} : aggregator T datatypes.int
notation `MIN` := aggregatorGroupByProj min

constant avg {T} : aggregator T datatypes.int
notation `AVG` := aggregatorGroupByProj avg

end aggregators

namespace predicates

constant gt : Pred (leaf datatypes.int ++ leaf datatypes.int)
infix `<u`:50 := gt

end predicates