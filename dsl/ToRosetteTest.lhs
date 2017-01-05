= Test for Cosette to Rosette

> module ToRosetteTest where

> import ToRosette
> import CosetteParser
> import qualified Test.HUnit as H

> vExpTest1 =
>   (BinOp (BinOp (DIden "x" "y") "=" (NumLit 12)) ">" (NumLit 15),
>    "(BINOP (BINOP \"x.y\" = 12) > 15)")

> makeVexpTest :: (ValueExpr, String) -> H.Test
> makeVexpTest (v, exp) = H.TestLabel (show v) $ H.TestCase $
>                      H.assertEqual (show v) exp (toSexp v)


> main :: IO H.Counts
> main = H.runTestTT $ H.TestList $ (makeVexpTest <$> [vExpTest1])

