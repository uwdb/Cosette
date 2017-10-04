 Coq Code generation

 It is the entrance of the program, so it is not a module.

> import CosetteParser
> import ToHoTTSQL
> import Text.Parsec (parse,ParseError)
> import Text.Parsec.String.Combinator
> import System.IO

FIXME: import ToRosette

> import Data.Char

> getResult :: String -> String
> getResult p =
>   case cs of
>     Right cs' ->
>       case genCoq cs' of
>         Right ans -> ans
>         Left err -> "ERROR: " ++ err
>     Left err -> "ERROR: " ++ (show err)
>   where
>     cs = parseCosette p

> main = do
>   hSetEncoding stdout utf8
>   cont <- getContents
>   (putStr $ getResult cont)
