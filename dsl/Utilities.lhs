
> module Utilities where

shared utilities function

look up an element from a list.

> lkUp :: Show b => [a] -> (a -> b -> Bool) -> b -> Either String a
> lkUp [] _ q = Left $ "cannot find " ++ (show q) ++ " in list."
> lkUp (h:t) f q = if f h q then Right h else lkUp t f q

check a list and return the first error.

> checkListErr :: [Either String a] -> Either String [a]
> checkListErr lt = foldE lt (Right [])
>   where foldE [] x = x
>         foldE (h:t) (Left es) =
>           case h of Left es' -> foldE t (Left (es ++ es'))
>                     Right e  -> foldE t (Left es)
>         foldE (h:t) (Right l) =
>           case h of Left es' -> foldE t (Left es')
>                     Right e  -> foldE t (Right (l ++ [e]))

join strings with line breaks

> joinWithBr :: [String] -> String
> joinWithBr = foldr (\a b -> if a == "" then b else a ++ " \n" ++ b) "" 
