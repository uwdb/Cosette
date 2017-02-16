= Solver Interface

 It is the entrance of the program, so it is not a module.

> import CosetteParser
> import ToHoTTSQL
> import ToRosette
> import Text.Parsec (parse,ParseError)
> import Text.Parsec.String.Combinator

FIXME: import ToRosette

> import Data.Char

> getResult :: String -> String -> String
> getResult p o =
>   case cs of
>     Right cs' ->
>       case o of
>         "coq" ->
>           case genCoq cs' of
>             Right ans -> ans
>             Left err -> "ERROR: " ++ err
>         "rosette" ->
>           case genRos cs' of
>             Right ans -> ans
>             Left err -> "ERROR: " ++ err 
>         _ -> "ERROR: output lang. is not supported."
>     Left err -> "ERROR: " ++ (show err)
>   where
>     cs = (parse (whitespace *> cosetteProgram <* eof) "" p)

> main = do
>   cont <- getContents
>   (putStr $ getResult cont "coq")

toCoqString :: String -> String
toCoqString 
