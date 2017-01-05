
[[functions-and-types-for-parsing]]
= Functions and types for parsing

In this file is the source and explanation for the parsing functions
which we've been using, and some limited notes about the wrappers and
full types in Parsec.

> module FunctionsAndTypesForParsing where
>
> import Text.Parsec (ParseError)
> import Text.Parsec.String (Parser)
> import Text.Parsec.String.Parsec (parse)
> import Text.Parsec.String.Char (oneOf)
> import Text.Parsec.String.Combinator (eof,manyTill,anyToken)
> import Control.Applicative ((<$>), (<*>), (<*), (*>), many)
> import Control.Monad (void)


== Functions for parsing

Here are the testing functions which were used earlier:

The basic parse function: this is a pretty simple wrapper. The parse
function from parsec just adds a filename to use in parse errors,
which is set as the empty string here.

> regularParse :: Parser a -> String -> Either ParseError a
> regularParse p = parse p ""

'parse' is a basic function in the family of functions for running
parsers in Parsec. You can compose the parser functions in the Parser
monad, then run the top level function using 'parse' and get back an
'Either ParserError a' as the result. There are a few alternatives to
'parse' in Parsec, mostly when you are using a more general parser
type instead of 'Parser a' (which is an alias for 'ParsecT String ()
Identity a'). Have a look in the Text.Parsec.Prim module for these
<http://hackage.haskell.org/package/parsec-3.1.3/docs/Text-Parsec-Prim.html>.

This function will run the parser, but additionally fail if it doesn't
consume all the input.

> parseWithEof :: Parser a -> String -> Either ParseError a
> parseWithEof p = parse (p <* eof) ""

This function will apply the parser, then also return any left over
input which wasn't parsed.

> parseWithLeftOver :: Parser a -> String -> Either ParseError (a,String)
> parseWithLeftOver p = parse ((,) <$> p <*> leftOver) ""
>   where leftOver = manyTill anyToken eof

TODO: what happens when you use 'many anyToken <* eof' variations
instead? Maybe should talk about greediness? Or talk about it in a
better place in the tutorial.

> parseWithWSEof :: Parser a -> String -> Either ParseError a
> parseWithWSEof p = parseWithEof (whiteSpace *> p)
>   where whiteSpace = void $ many $ oneOf " \n\t"

== Util functions

> checkListErr :: [Either String a] -> Either String [a]
> checkListErr lt = foldE lt (Right [])
>   where foldE [] x = x
>         foldE (h:t) (Left es) =
>           case h of Left es' -> foldE t (Left (es ++ es'))
>                     Right e  -> foldE t (Left es)
>         foldE (h:t) (Right l) =
>           case h of Left es' -> foldE t (Left es')
>                     Right e  -> foldE t (Right (l ++ [e]))

> addParen :: String -> String
> addParen s = "(" ++ s ++ ")"

You should have a look at the two helper executables, and see if you
can understand the code now. You can see them online here:

<https://github.com/JakeWheat/intro_to_parsing/blob/master/ParseFile.lhs>

<https://github.com/JakeWheat/intro_to_parsing/blob/master/ParseString.lhs>

== type signatures revisited

todo: update this to refer to real parsec instead of the string
wrappers here.

I think you should always use type signatures with Parsec. Because the
Parsec code is really generalized, without the type GHC will refuse to
compile this code. Try commenting out the type signature above and
loading into ghci to see the error message.

There is an alternative: you can get this code to compile without a
type signature by using the NoMonomorphismRestriction language
pragma. You can also see the type signature that GHC will choose for
this function by commenting the type signature and using -Wall and
-XNoMonomorphismRestriction together. Using NoMonomorphismRestriction
is a popular solution to these sorts of problems in haskell.

It's up to you whether you prefer to always write type signatures when
you are developing parsing code, or use the NoMonomorphismRestriction
pragma. Even if you can use NoMonomorphismRestriction, when using
explicit type signatures you usually get much simpler compiler error
messages.


== Parser

The definition of Parser and a partial explanation of the full type
signature.

```
type Parser = Parsec String ()
```

This means that a function returning Parser a parses from a String
with () as the initial state.

The Parsec type is defined like this:

```
type Parsec s u = ParsecT s u Identity
```

ParsecT is a monad transformer, I think it is the primitive one in the
Parsec library, and the 'Parsec' type is a type alias which sets the
base monad to be Identity.

Here is the haddock for the ParsecT type:

`ParsecT s u m a` is a parser with stream type `s`, user state type `u`,
underlying monad `m` and return type `a`.

The full types that you see like this:

```
satisfy :: Stream s m Char => (Char -> Bool) -> ParsecT s u m Char
```

refer to the same things (stream type s, user state type u, underlying
monad m).

We are using String as the stream type (i.e. the input type), () as
the user state type (this effectively means no user state, since ()
only has one value), and the underlying monad is Identity: we are
using no other underlying monad, so `Parser a` expands to `ParsecT
String () Identity a`.

I.e. the source is String, the user state is (), and the underlying monad
is Identity.

== Other information

TODO: Here is some other information on Parsec and Haskell:
links, tutorials on fp, section in rwh, lyah?, old parsec docs,
parsec docs on hackage, other parser combinator libs (uu, polyparse,
trifecta?)
