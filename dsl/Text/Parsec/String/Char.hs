module Text.Parsec.String.Char where

{-

Wrappers for the Text.Parsec.Char module with the types fixed to
'Text.Parsec.String.Parser a', i.e. the stream is String, no user
state, Identity monad.

-}

import qualified Text.Parsec.Char as C
import Text.Parsec.String (Parser)

spaces :: Parser ()
spaces = C.spaces

space :: Parser Char
space = C.space

newline :: Parser Char
newline = C.newline

tab :: Parser Char
tab = C.tab

upper :: Parser Char
upper = C.upper

lower :: Parser Char
lower = C.lower

alphaNum :: Parser Char
alphaNum = C.alphaNum

letter :: Parser Char
letter = C.letter

digit :: Parser Char
digit = C.digit

hexDigit :: Parser Char
hexDigit = C.hexDigit

octDigit :: Parser Char
octDigit = C.octDigit

char :: Char -> Parser Char
char = C.char

string :: String -> Parser String
string = C.string

anyChar :: Parser Char
anyChar = C.anyChar

oneOf :: [Char] -> Parser Char
oneOf = C.oneOf

noneOf :: [Char] -> Parser Char
noneOf = C.noneOf

satisfy :: (Char -> Bool) -> Parser Char
satisfy = C.satisfy
