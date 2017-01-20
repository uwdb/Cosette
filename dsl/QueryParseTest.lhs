= Tests for Parsers

> module QueryParseTest where

> import Text.Parsec.String (Parser)
> import Control.Applicative ((<$>))
> import CosetteParser
> import Text.Parsec (parse,ParseError)
> import qualified Test.HUnit as H
> import Debug.Trace

> testQuery1 :: QueryExpr
> testQuery1 = Select [DStar "x", Proj (DIden "x" "a") "a"]
>              (Just [(TR (TRBase "a") "x"), TR (TRQuery (Select [Star] Nothing Nothing Nothing False)) "y"])
>              (Just TRUE)
>              Nothing
>              False

> testQuery2 :: QueryExpr
> testQuery2 = Select [Proj (DIden "t2" "c1") "tc1",Proj (DIden "t2" "c2") "tc2",Proj (DIden "t2" "c3") "tc3"]
>            (Just [TR (TRQuery (Select [Proj (DIden "t1" "c1") "c1",Proj (DIden "t1" "c2") "c2",Proj (DIden "t1" "c3") "c3"]
>                           (Just [TR (TRBase "t1") "t1"])
>                           (Just (Vlt (DIden "t1" "c1") (DIden "t1" "c2"))) Nothing False)) "t2"])
>            (Just (Vlt (DIden "t2" "c1") (DIden "t2" "c3")))
>            Nothing
>            False

> testQuery3 :: QueryExpr
> testQuery3 = Select [Proj (DIden "t1" "c1") "tc1",Proj (DIden "t1" "c2") "tc2",Proj (DIden "t1" "c3") "tc3"]
>              (Just [TR (TRBase "t1") "t1"])
>              (Just (And (Vlt (DIden "t1" "c1") (DIden "t1" "c2")) (Vlt (DIden "t1" "c1") (DIden "t1" "c3"))))
>              Nothing
>              False

> testQuery4 :: QueryExpr
> testQuery4 = Select [Star] (Just [TR (TRBase "a") "a"]) (Just (Exists (Select [Star] (Just [TR (TRBase "a") "a"]) Nothing Nothing False))) Nothing False

> testQuery5 :: QueryExpr
> testQuery5 = Select [Proj (Constant "a") "a"] Nothing Nothing Nothing False

> testQuery6 :: QueryExpr
> testQuery6 = Select [Star] (Just [TR (TRBase "a") "x"]) (Just (PredVar "e" ["x"])) Nothing False

> testQuery7 :: QueryExpr
> testQuery7 = Select [Star]
>                     (Just [TR (TRBase "a") "x",
>                            TR (TRQuery (Select [Star] (Just [TR (TRBase "b") "y"]) (Just (PredVar "b0" ["y"])) Nothing False)) "z"])
>                     (Just (PredVar "b1" ["x", "z"]))
>                     Nothing
>                     False

> testQuery8 :: QueryExpr
> testQuery8 = Select [Proj (DIden "x1" "a") "x1a"]
>                 (Just [TR (TRQuery (Select [Proj (DIden "x" "a") "a", Proj (DIden "x" "k") "k"]
>                                (Just [TR (TRBase "x") "x"]) Nothing Nothing False)) "x1",
>                        TR (TRBase "y") "y"])
>                 (Just (Veq (DIden "x1" "k") (DIden "y" "k")))
>                 Nothing
>                 False

> testQuery9 :: QueryExpr
> testQuery9 = Select [Proj (DIden "x" "x") "ax"]
>                     (Just [TR (TRBase "a") "x", TR (TRBase "b") "y"])
>                     (Just (Veq (DIden "x" "ya") (DIden "y" "yb")))
>                     Nothing
>                     True

> testQuery10 :: QueryExpr
> testQuery10 = UnionAll
>               (Select [Star] Nothing Nothing Nothing False)
>               (UnionAll (Select [Star] Nothing Nothing Nothing False)
>                         (Select [Star] (Just [TR (TRBase "a") "a"]) Nothing Nothing False))

> testQuery11 :: QueryExpr
> testQuery11 = Select [Star]
>               (Just [TR (TRUnion (TRBase "a") (TRUnion (TRBase "b") (TRBase "c"))) "x"])
>               Nothing Nothing False

> testQuery12 :: QueryExpr
> testQuery12 = Select [Proj (DIden "x" "uid") "xu",Proj (Agg "count" AStar) "xn"]
>               (Just [TR (TRBase "a") "x"])
>               Nothing
>               (Just [DIden "x" "uid",DIden "x" "uname"])
>               False

> queryParseTests :: [(String, QueryExpr)]
> queryParseTests =
>   [("select x.*, x.a as a from a x, (select *) y where TRUE", testQuery1),
>    ("select t2.c1 as tc1, t2.c2 as tc2, t2.c3 as tc3 from (select t1.c1 as c1, t1.c2 as c2, t1.c3 as c3 from t1 t1 where t1.c1 < t1.c2) t2 where t2.c1 < t2.c3", testQuery2),
>    ("select t1.c1 as tc1, t1.c2 as tc2, t1.c3 as tc3 from t1 t1 where t1.c1 < t1.c2 and t1.c1 < t1.c3", testQuery3),
>    ("select * from a a where exists (select * from a a)", testQuery4),
>    ("select a as a", testQuery5),
>    ("select * from a x where e(x)", testQuery6),
>    ("select * from a x, (select * from b y where b0(y)) z where b1(x, z)", testQuery7),
>    ("select x1.a as x1a from (select x.a as a, x.k as k from x x) x1, y y where x1.k = y.k",
>     testQuery8),
>    ("select distinct x.x as ax from a x, b y where x.ya = y.yb", testQuery9),
>    ("select * union all (select * union all select * from a a)", testQuery10),
>    ("select * from (a union all b union all c) x", testQuery11),
>    ("select x.uid as xu, count(*) as xn from a x group by x.uid, x.uname", testQuery12)]

> main :: IO H.Counts
> main =  H.runTestTT $ H.TestList $ makeTest queryExpr <$> queryParseTests
