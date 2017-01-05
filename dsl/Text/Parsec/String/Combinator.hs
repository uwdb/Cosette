
module Text.Parsec.String.Combinator where

{-

Wrappers for the Text.Parsec.Combinator module with the types fixed to
'Text.Parsec.String.Parser a', i.e. the stream is String, no user
state, Identity monad.

-}

import qualified Text.Parsec.Combinator as C
import Text.Parsec.String (Parser)

choice :: [Parser a] -> Parser a
choice = C.choice


count :: Int -> Parser a -> Parser [a]
count = C.count

between :: Parser open -> Parser close -> Parser a -> Parser a
between = C.between


option :: a -> Parser a -> Parser a
option = C.option

optionMaybe :: Parser a -> Parser (Maybe a)
optionMaybe = C.optionMaybe

optional :: Parser a -> Parser ()
optional = C.optional

skipMany1 :: Parser a -> Parser ()
skipMany1 = C.skipMany1

many1 :: Parser a -> Parser [a]
many1 = C.many1

sepBy :: Parser a -> Parser sep -> Parser [a]
sepBy = C.sepBy

sepBy1 :: Parser a -> Parser sep -> Parser [a]
sepBy1 = C.sepBy1

endBy :: Parser a -> Parser sep -> Parser [a]
endBy = C.endBy

endBy1 :: Parser a -> Parser sep -> Parser [a]
endBy1 = C.endBy1

sepEndBy :: Parser a -> Parser sep -> Parser [a]
sepEndBy = C.sepEndBy

sepEndBy1 :: Parser a -> Parser sep -> Parser [a]
sepEndBy1 = C.sepEndBy1

chainl :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl = C.chainl

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 = C.chainl1

chainr :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainr = C.chainr

chainr1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 = C.chainr1

eof :: Parser ()
eof = C.eof

notFollowedBy :: Show a => Parser a -> Parser ()
notFollowedBy = C.notFollowedBy

manyTill :: Parser a -> Parser end -> Parser [a]
manyTill = C.manyTill

lookAhead :: Parser a -> Parser a
lookAhead = C.lookAhead

anyToken :: Parser Char
anyToken = C.anyToken
