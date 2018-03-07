Generates an AST in JSON from Cosette


> import CosetteParser
> import Data.Aeson.Encode.Pretty
> import Text.Parsec (parse,ParseError)
> import Text.Parsec.String.Combinator

> import Data.Char
> import GHC.Generics
> import qualified Data.ByteString.Lazy.Char8 as C

> getStmt :: String -> [Char]
> getStmt txt = 
>   case ret of
>       Right ret' ->
>           C.unpack ((encodePretty ret))
>       Left err -> "ERROR: " ++ (show err)
>   where
>       ret = (parse (whitespace *> cosetteProgram <* eof) "" p)

> main = do
>   cont <- getContents
>   putStr $ getStmt cont
