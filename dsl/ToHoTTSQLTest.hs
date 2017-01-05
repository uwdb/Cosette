module ToHoTTSQLTest where

import ToHoTTSQL
import CosetteParser
import qualified Test.HUnit as H
 

xs :: HSSchema
xs = MakeSchema "xs" [("a", "int"), ("k", "int")]

ys :: HSSchema
ys = MakeSchema "ys" [("k", "int")]

env :: HSEnv
env = MakeHSEnv [("x", "xs"), ("y", "ys")] [xs, ys]

q2hst :: Either String HSQueryExpr
q2hst = toHSQuery env HSEmpty query2

toHoTTTest1 :: (Either String HSQueryExpr, String)
toHoTTTest1 = (q2hst, "(SELECT right\8901left\8901a FROM (product ((SELECT (combine right\8901a right\8901k) FROM (table x) WHERE true)) (table y)) WHERE (equal right\8901left\8901k right\8901right\8901k))")

makeToHoTTTest :: (Either String HSQueryExpr, String) -> H.Test
makeToHoTTTest (v, exp) = H.TestLabel (show v) $ H.TestCase $ do
  case v of
    Left e -> H.assertFailure $ show e
    Right a -> H.assertEqual (show v) exp (toCoq a)

main :: IO H.Counts
main = H.runTestTT $ H.TestList $ (makeToHoTTTest <$> [toHoTTTest1])
