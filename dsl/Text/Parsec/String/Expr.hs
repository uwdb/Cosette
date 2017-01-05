
module Text.Parsec.String.Expr (buildExpressionParser
                               ,Operator(..)
                               ,OperatorTable
                               ,E.Assoc(..)
                               )where

{-

Wrappers for the Text.Parsec.Expr module with simplified types.

-}

import Text.Parsec.String (Parser)
import qualified Text.Parsec.Expr as E

-- not sure if this is neccessary, or a type alias would be good
-- enough
data Operator a = Infix (Parser (a -> a -> a)) E.Assoc
                | Prefix (Parser (a -> a))
                | Postfix (Parser (a -> a))

type OperatorTable a = [[Operator a]]

buildExpressionParser :: OperatorTable a -> Parser a -> Parser a
buildExpressionParser t = E.buildExpressionParser (map (map f) t)
  where
    f (Infix p a) = E.Infix p a
    f (Prefix p) = E.Prefix p
    f (Postfix p) = E.Postfix p
