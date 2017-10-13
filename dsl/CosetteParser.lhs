= Parser for Cosette

Syntax and Parser for Cosette.

> module CosetteParser where
>
> import Text.Parsec.String (Parser)
> import Text.Parsec.String.Parsec (try)
> import Text.Parsec.String.Char
> import Text.Parsec.String.Combinator
> import Text.Parsec (parse,ParseError)
> import Control.Applicative ((<$>),(<*), (*>),(<*>), (<$), (<|>), many)
> import qualified Text.Parsec.String.Expr as E
> import Control.Monad
> import Data.Maybe
> import Data.Char
> import Data.List (nub, find)
> import Test.HUnit.Base (Test (TestLabel, TestCase), assertEqual, assertFailure)
> import FunctionsAndTypesForParsing
> import Utilities
> import Debug.Trace

== SQL keywords

> sqlKeywords :: [String]                      
> sqlKeywords = [--join keywords
>                "natural"
>                ,"inner"
>                ,"outer"
>                ,"cross"
>                ,"left"
>                ,"right"
>                ,"full"
>                ,"join"
>                ,"on"
>                ,"using"
>                  -- subsequent clause keywords
>                ,"select"
>                ,"where"
>                ,"group"
>                ,"by"
>                ,"having"
>                ,"order"
>                ,"as"
>                ,"distinct"
>                ]

== Abstract Syntax

=== value expression

> data ValueExpr = NumLit Integer
>                | DIden String String              -- a.b
>                | BinOp ValueExpr String ValueExpr -- a.b + b.c etc
>                | Constant String                  -- constant variable
>                | VQE QueryExpr                    -- query expressions
>                | Agg String AggExpr             -- aggregation function
>                  deriving (Eq, Show)

> data AggExpr = AV ValueExpr
>              | AStar
>                deriving (Eq, Show)

=== predicate

> data Predicate = TRUE
>                | FALSE
>                | PredVar String [String]   -- generic predicate
>                | And Predicate Predicate
>                | Or Predicate Predicate
>                | Not Predicate
>                | Exists QueryExpr 
>                | Veq ValueExpr ValueExpr   -- equal
>                | Vgt ValueExpr ValueExpr   -- greater than
>                | Vlt ValueExpr ValueExpr   -- less than
>                  deriving (Eq, Show)

=== select item

> data SelectItem = Star         -- *
>                 | DStar String -- t.*
>                 | Proj ValueExpr String
>                   deriving (Eq, Show)


=== table ref (in from clause)

TODO: add Left Join, Semi join etc to table expression

> data TableExpr = TRBase String                -- base table
>                | TRUnion TableExpr TableExpr  -- union
>                | TRQuery QueryExpr            -- query
>                deriving (Eq, Show)

consider add the following to the definition of TableRef
| TRXProd TableRef TableRef
if convert list of relation to nested join is move to Cosette AST level

> data TableRef = TR TableExpr String           -- table expr, alias
>               | TRJoin TableRef JoinType TableRef (Maybe Predicate) 
>                 deriving (Eq, Show)

> data JoinType = InnerJoin | LeftJoin | RightJoin | FullOuterJoin
>                 deriving (Eq, Show)

> getTe :: TableRef -> TableExpr
> getTe (TR t _) = t

> getAlias :: TableRef -> String
> getAlias (TR _ s) = s

=== query expression

TODO: currently, grouping only supports columns rather than arbitrary value expressions

> data QueryExpr = Select
>                {qSelectList :: [SelectItem]
>                ,qFrom :: Maybe [TableRef]
>                ,qWhere :: Maybe Predicate
>                ,qGroup :: Maybe Grouping
>                ,qDistinct:: Bool}
>                | UnionAll QueryExpr QueryExpr
>                deriving (Eq, Show)

> data Grouping = GroupBy [ValueExpr] (Maybe Predicate)
>                 deriving (Eq, Show)

=== Cosette Statement

> data CosetteStmt = Schema String [(String, String)]
>                  | Table String String
>                  | Pred String [String]
>                  | Const String String
>                  | Query String QueryExpr
>                  | Verify String String
>                    deriving (Eq, Show)

== parsing ValueExp

> integer :: Parser Integer
> integer = do
>   n <- lexeme $ many1 digit
>   return $ read n

> num :: Parser ValueExpr
> num = NumLit <$> integer

> dIden :: Parser ValueExpr
> dIden = DIden <$> identifier <*> (dot *> identifier)

> constant :: Parser ValueExpr
> constant = Constant <$> identifier


> aggExpr :: Parser AggExpr
> aggExpr = AV <$> valueExpr []
>       <|> AStar <$ symbol "*"


> aggTerm :: Parser ValueExpr
> aggTerm = Agg <$> identifier <*> parens aggExpr

term

> term :: [String] -> Parser ValueExpr
> term blackList = try dIden
>              <|> try aggTerm
>              <|> num
>              <|> constant
>              <|> parens (valueExpr [])

operators on values

> vtable :: [[E.Operator ValueExpr]]
> vtable = [[binary "*" E.AssocLeft
>           ,binary "/" E.AssocLeft]
>          ,[binary "+" E.AssocLeft
>           ,binary "-" E.AssocLeft]]
>   where
>     binary name assoc =
>         E.Infix (mkBinOp name <$ symbol name) assoc
>     mkBinOp nm a b = BinOp a nm b

valueExpr

> valueExpr' :: [String] -> Parser ValueExpr
> valueExpr' blackList = E.buildExpressionParser vtable (term blackList)

> valueExpr :: [String] -> Parser ValueExpr
> valueExpr blacklist = try (VQE <$> queryExpr)
>                   <|> valueExpr' blacklist


== parsing select item

> star :: Parser SelectItem
> star = Star <$ symbol "*"

> dstar :: Parser SelectItem
> dstar = DStar <$> (identifier <* dot <* symbol "*")

> selectList :: Parser [SelectItem]
> selectList = keyword_ "select" *> commaSep1 selectItem

> distSelectList :: Parser [SelectItem]
> distSelectList = keyword_ "select" *> keyword_ "distinct" *> commaSep1 selectItem

> proj :: Parser SelectItem
> proj = try (Proj <$> valueExpr sqlKeywords <*> alias)
>        <|> (Proj <$> valueExpr sqlKeywords <*> return "")
>   where alias = keyword_ "as" *> identifierBlacklist sqlKeywords

> selectItem :: Parser SelectItem
> selectItem = star <|> try dstar <|> proj

== parsing predicate 

negation

> neg :: Parser Predicate
> neg = Not <$> (keyword "not" *> pterm)

predicate meta variable

> predVar :: Parser Predicate
> predVar = PredVar <$> identifier <*> (parens $ commaSep1 identifier)

binary operations on values

> binOpValue :: (ValueExpr -> ValueExpr -> Predicate) -> Parser Char -> Parser Predicate
> binOpValue con opParser = con <$> (valueExpr []) <*> (opParser *> (valueExpr []))

equal predicate

> eqp :: Parser Predicate
> eqp = binOpValue Veq eq

greater than

> gtp :: Parser Predicate
> gtp = binOpValue Vgt gt

less than

> ltp :: Parser Predicate
> ltp = binOpValue Vlt lt

exists clause

> exists :: Parser Predicate
> exists = Exists <$> (keyword_ "exists" *> parens queryExpr)

> pterm' :: Parser Predicate
> pterm' = try (parens predicate)
>      <|> try eqp
>      <|> try ltp
>      <|> try gtp
>      <|> exists
>      <|> try predVar
>      <|> neg
>      <|> (void $ keyword "true") *> return TRUE
>      <|> (void $ keyword "false") *> return FALSE

> pterm :: Parser Predicate
> pterm = lexeme pterm'

=== conjuctive predicate, 

> conp :: Parser Predicate
> conp = chainl1 pterm op
>   where
>     op = do
>       void $ lexeme $ keyword "and" 
>       return And

=== predicate

> predicate :: Parser Predicate 
> predicate = chainl1 conp op
>   where
>     op = do
>       void $ lexeme $ keyword "or"
>       return Or

== Query expression parsing

> whereClause :: Parser Predicate
> whereClause = keyword_ "where" *> predicate

=== from clause

TODO: for now, only base relations can be unioned in from clause.

> tableExpr :: Parser TableExpr
> tableExpr = try unionTe
>         <|> (TRQuery <$> queryExpr)

> baseTe :: Parser TableExpr
> baseTe = TRBase <$> identifier
>      <|> (parens unionTe)

> unionTe :: Parser TableExpr
> unionTe = try (TRUnion <$> baseTe <*> (unionall *> unionTe))
>       <|> baseTe

> baseTableRef :: Parser TableRef
> baseTableRef = try (TR <$> tableExpr <*> aliasIdentifier)
>        <|> TR <$> tableExpr <*> (keyword_ "as" *> aliasIdentifier)
>             where aliasIdentifier = identifierBlacklist sqlKeywords

only support inner join now

> joinType :: Parser JoinType
> joinType = InnerJoin <$ keyword_ "inner" <* keyword_ "join"
>        <|> InnerJoin <$ keyword_ "join"

> joinCondition :: Parser Predicate
> joinCondition = keyword_ "on" *> predicate

> tableRef :: Parser TableRef
> tableRef = baseTableRef >>= suffixWrapper joinTableRef
>   where joinTableRef t =
>           (do TRJoin t
>               <$> joinType <*> baseTableRef <*> optionMaybe joinCondition)
>           >>= suffixWrapper joinTableRef

> fromClause :: Parser [TableRef]
> fromClause = keyword_ "from" *> commaSep1 tableRef

=== grouping clause

> groupby :: Parser ()
> groupby = keyword_ "group" *> keyword_ "by"

> having :: Parser ()
> having = keyword_ "having"

> grouping :: Parser Grouping
> grouping = GroupBy
>            <$> (groupby *> commaSep1 dIden)
>            <*> optionMaybe (having *> predicate)

=== queryExpr

Query without distinct

> bagQuery :: Parser QueryExpr
> bagQuery = Select
>            <$> selectList
>            <*> optionMaybe fromClause
>            <*> optionMaybe whereClause
>            <*> optionMaybe grouping
>            <*> (do return False)

Query with distinct

> setQuery :: Parser QueryExpr
> setQuery = Select
>            <$> distSelectList
>            <*> optionMaybe fromClause
>            <*> optionMaybe whereClause
>            <*> optionMaybe grouping
>            <*> (do return True)

Query expression

> spjQueryExpr :: Parser QueryExpr
> spjQueryExpr = try setQuery <|> bagQuery <|> (parens queryExpr)

> unionQueryExpr :: Parser QueryExpr
> unionQueryExpr = UnionAll <$>
>                  (spjQueryExpr <* unionall) <*>
>                  queryExpr

> queryExpr :: Parser QueryExpr
> queryExpr = try unionQueryExpr
>         <|> spjQueryExpr
>         <|> (parens queryExpr)
             
=== Parse Cosette statement 

Parse schema declaration

Note: we always treat "??"  as unknowns: type

> schemaItem :: Parser (String, String)
> schemaItem =  unknowns <|> normalAttr
>   where normalAttr = (,) <$> identifier
>                          <*> (symbol_ ":" *> identifier)
>         unknowns = (\_ -> ("unknowns", "type")) <$> unknown

> schemaStmt :: Parser CosetteStmt
> schemaStmt = Schema <$> (keyword_ "schema" *> identifier) <*> schema
>   where schema = parens $ commaSep1 schemaItem

Parse table declaration

> tableStmt :: Parser CosetteStmt
> tableStmt = Table <$> (keyword_ "table" *> identifier)
>                   <*> (parens $ identifier)

Parse predicate declaration

> predStmt :: Parser CosetteStmt
> predStmt = Pred <$> (keyword_ "predicate" *> identifier)
>                 <*> (parens $ commaSep1 identifier)

Parse constant declaration

> constStmt :: Parser CosetteStmt
> constStmt = Const <$> (keyword_ "constant" *> identifier)
>                   <*> (symbol_ ":" *> identifier)

Parse query declarations

> queryStmt :: Parser CosetteStmt
> queryStmt = Query <$> (keyword_ "query" *> identifier)
>                   <*> qp queryExpr
>   where qp = between st st
>         st = lexeme $ char '`'

Parse verify statement

> verifyStmt :: Parser CosetteStmt
> verifyStmt = Verify <$> (keyword_ "verify" *> identifier) <*> identifier

Parse cosette statement

> cosetteStmt :: Parser CosetteStmt
> cosetteStmt = schemaStmt
>           <|> tableStmt
>           <|> predStmt
>           <|> constStmt
>           <|> queryStmt
>           <|> verifyStmt

Parse cosette program

> cosetteProgram :: Parser [CosetteStmt]
> cosetteProgram = (`sepEndBy1` semiColon) $ cosetteStmt

> class Namely a where
>   toName :: a -> Either String String

you must explicitly name a query expr

> instance Namely ValueExpr where
>   toName (NumLit n) = Right $ "num" ++ (show n)
>   toName (DIden r a) = Right a
>   toName (BinOp v1 op v2) = do
>      s1 <- toName v1
>      so <- opToName op
>      s2 <- toName v2
>      return (s1 ++ "_" ++ so ++ "_" ++ s2)
>   toName (Constant s) = Right s
>   toName (Agg s ae) = do
>      an <- toName ae
>      return (s ++ "_" ++ an)
>   toName (VQE _) = Left "a query must be explicitly named."

> opToName :: String -> Either String String
> opToName "+" = Right "add"
> opToName "-" = Right "minus"
> opToName "*" = Right "times"
> opToName "/" = Right "div"
> opToName other = Left $ "unsupported op: " ++ other

> instance Namely AggExpr where
>   toName (AV v) = toName v
>   toName AStar = Right "star"

AST transformations.

define a type class of context for apply passes on Cosette ASTs.

> class CosCtx a where
>   update :: a -> a

do nothing.

> data Void = VOID

> instance CosCtx Void where
>   update a = a

> newtype Counter = MakeCounter Integer
 
> instance CosCtx Counter where
>   update (MakeCounter i) = MakeCounter $ i + 1

extra pass 1: infer alias if there no alias

> addAlias :: Void -> QueryExpr -> Either String QueryExpr
> addAlias _ (Select sl fr w g d) = do
>  sl' <- checkListErr $ map f sl
>  return (Select sl' fr w g d)
>   where f (Proj v s) = if s == ""
>                        then Proj <$> Right v <*> toName v
>                        else Right (Proj v s)
>         f other = Right other 

extra pass 2: remove inner join

> removeIJ :: Void -> QueryExpr -> Either String QueryExpr
> removeIJ _ (Select sl fr w g d) =
>   let (trs, newP) = rmInFr fr in
>     Right $ Select sl trs (conj newP <$> wh) g d 
>   where wh = if w == Nothing then Just TRUE else w
>         rmInFr Nothing = (Nothing, TRUE)
>         rmInFr (Just fl) =
>           let (newF, p) = foldl m ([], TRUE) (rmJoin <$> fl)
>               in (Just newF, p)
>         m x y = (fst x ++ fst y, conj (snd x) (snd y))
>         conj a b = case (a, b) of
>                      (TRUE, TRUE) -> TRUE
>                      (TRUE, x') -> x'
>                      (x', TRUE) -> x'
>                      (x', y') -> And x' y'
>         rmJoin (TR te a) = ([TR te a], TRUE)
>         rmJoin (TRJoin tr1 InnerJoin tr2 (Just p)) =
>            let (t, p') = m (rmJoin tr1) (rmJoin tr2) in (t, conj p' p)
>         rmJoin (TRJoin tr1 InnerJoin tr2 Nothing) = m (rmJoin tr1) (rmJoin tr2)

extra pass 3: convert having
Note this pass is only required when generating Coq code

> removeHaving :: Counter -> QueryExpr -> Either String QueryExpr
> removeHaving (MakeCounter i) (Select sl fr w (Just (GroupBy gl (Just p))) d) = 
>   do  asl <- checkListErr $ (makeSl <$> aggs)
>       esl <- checkListErr $ (mc2SI <$> missCols)
>       subq <- Right $ Select (sl ++ esl  ++ asl) fr w (Just $ GroupBy gl Nothing) False
>       newP <- convP sl qn p
>       newSl <- checkListErr $ (convS qn <$> sl)
>       return $ Select newSl (Just [TR (TRQuery subq) qn]) (Just newP) Nothing d
>   where qn = "sub_q" ++ (show i) ++ "_"
>         aggs = nub $ collectAgg p
>         makeSl v = Proj v  <$> toName v
>         -- substitute rel name in having, and put it to where in outer query
>         convP dic n (And p1 p2) = And <$> convP dic n p1 <*> convP dic n p2
>         convP dic n (Or p1 p2) = Or <$> convP dic n p1 <*> convP dic n p2
>         convP dic n (Not pr) = Not <$> convP dic n pr
>         convP dic n (Exists q) = Left "do not support subq in having"
>         convP dic n (Veq v1 v2) = Veq <$> convV dic n v1 <*> convV dic n v2
>         convP dic n (Vgt v1 v2) = Vgt <$> convV dic n v1 <*> convV dic n v2
>         convP dic n (Vlt v1 v2) = Vlt <$> convV dic n v1 <*> convV dic n v2
>         convP dic n other = Right other
>         convV dic n (DIden r a) =
>           Right $ DIden n (case findVinSl (DIden r a) sl of
>                               Just (Proj v' a') -> a'
>                               _ -> a)
>         convV dic n (BinOp v1 op v2) =
>           BinOp <$> convV dic n v1 <*> Right op <*> convV dic n v2
>         convV dic n (Agg f a) = DIden n <$> toName (Agg f a)
>         convV dic n other = Right other
>         findVinSl v sel = find (\x -> case x of
>                                         Proj v' a -> v == v'
>                                         _ -> False) sel
>         -- substitute rel name in select clause
>         convS n (Proj v a) = Right $ Proj (DIden n a) a
>         convS n other = Right other
>         -- get the pure column refs from orginal select clause
>         colDic = getPureCols sl
>         -- get column refs that are used in having
>         hvCols = collectColRef p
>         -- get column refs that in having but not in select
>         missCols = filter rFind hvCols
>         rFind x = case lookup x colDic of
>                     Just x' -> False
>                     Nothing -> True
>         mc2SI c = if elem c gl
>                   then Proj c <$> toName c
>                   else Left "cannot use a non group by column in having"
> -- do nothing for queries without having         
> removeHaving (MakeCounter i) (Select sl fr w g d) = Right $ Select sl fr w g d

collect aggregation from Predicate

> collectAgg :: Predicate -> [ValueExpr]
> collectAgg p = nub $ findVinP f p
>   where f (Agg f a) = True
>         f other = False

collect column refs from Predicate

> collectColRef :: Predicate -> [ValueExpr]
> collectColRef p = nub $ findVinP f p
>   where f (DIden v c) = True
>         f other = False

> findVinP :: (ValueExpr -> Bool) -> Predicate -> [ValueExpr]
> findVinP f (And p1 p2) = (findVinP f p1) ++ (findVinP f p2)
> findVinP f (Or p1 p2) = (findVinP f p1) ++ (findVinP f p2)
> findVinP f (Not p) = findVinP f p
> findVinP f (Veq v1 v2) = (findVinV f v1) ++ (findVinV f v2)
> findVinP f (Vgt v1 v2) = (findVinV f v1) ++ (findVinV f v2)
> findVinP f (Vlt v1 v2) = (findVinV f v1) ++ (findVinV f v2)
> findVinP f other = []

collect aggregation from ValueExpr

> findVinV :: (ValueExpr -> Bool) -> ValueExpr -> [ValueExpr]
> findVinV f v =
>   if f v
>   then [v]
>   else case v of
>     BinOp v1 op v2 -> (findVinV f v1) ++ (findVinV f v2)
>     other -> []

get a collection of pure column ref projection (VE, alias)

> getPureCols :: [SelectItem] -> [(ValueExpr, String)]
> getPureCols sl = nub $ f sl
>   where f [Proj (DIden r c) a] = [(DIden r c, a)]
>         f [other] = []
>         f (h:t) = case h of
>                    Proj (DIden r c) a -> (DIden r c, a) : (f t)
>                    other -> f t

apply transformation pass recursively on Cosette ASTs

> applyCosPass :: CosCtx a => (a -> QueryExpr -> Either String QueryExpr)
>                  -> a -> QueryExpr -> Either String QueryExpr
> applyCosPass p c (UnionAll q1 q2) =
>   UnionAll <$> applyCosPass p c q1 <*> applyCosPass p c q2
> applyCosPass p c (Select sl f w g d) =
>   do (Select sl' f' w' g' d') <- p c (Select sl f w g d)
>      nsl <- (checkListErr $ map convSI sl')
>      nf <- newFr f'
>      nw <- newWh w'
>      return $ Select nsl nf nw g' d'        
>   where c' = update c
>         convVE (BinOp v1 op v2) = BinOp <$> convVE v1 <*> Right op <*> convVE v2
>         convVE (VQE q) = VQE <$> applyCosPass p c' q
>         convVE other = Right other
>         convSI (Proj v a) = Proj <$> convVE v <*> Right a
>         convSI other = Right other
>         convTR (TR te a) = TR <$> convTE te <*> Right a
>         convTR (TRJoin t1 jt t2 mp) =
>           do newMp <- case mp of
>                         Nothing -> Right Nothing
>                         Just p -> Just <$> convP p
>              t1' <- convTR t1
>              t2' <- convTR t2
>              return $ TRJoin t1' jt t2' newMp
>         convTE (TRUnion t1 t2) = TRUnion <$> convTE t1 <*> convTE t2
>         convTE (TRQuery q) = TRQuery <$> applyCosPass p c' q
>         convTE other = Right other
>         newFr from = case from of
>                        Nothing -> Right Nothing
>                        Just fl -> Just <$> (checkListErr $ map convTR fl)
>         convP (And p1 p2) = And <$> convP p1 <*> convP p2
>         convP (Or p1 p2) = And <$> convP p1 <*> convP p2
>         convP (Not p') = Not <$> convP p'
>         convP (Exists q) = Exists <$> applyCosPass p c' q
>         convP (Veq v1 v2) = Veq <$> convVE v1 <*> convVE v2
>         convP (Vgt v1 v2) = Vgt <$> convVE v1 <*> convVE v2
>         convP (Vlt v1 v2) = Vlt <$> convVE v1 <*> convVE v2
>         convP other = Right other
>         newWh wh = case wh of
>                      Nothing -> Right Nothing
>                      Just wh' -> Just <$> (convP wh')

This function should be used to parse cosette program

> parseCosette :: String -> Either String [CosetteStmt]
> parseCosette source = 
>   let cs = parse (whitespace *> cosetteProgram <* eof) "" (toLower <$> source) in
>   case cs of
>     Left emsg -> Left (show emsg)
>     Right asts -> checkListErr $ map passCos asts 


> passCos :: CosetteStmt -> Either String CosetteStmt
> passCos (Query n q) = Query n <$> passQuery q           
> passCos o = Right o

> passQuery :: QueryExpr -> Either String QueryExpr
> passQuery q =
>   do q1 <- applyCosPass addAlias VOID q
>      q2 <- applyCosPass removeIJ VOID q1
>      return q2

== tokens

> whitespace :: Parser ()
> whitespace =
>     choice [simpleWhitespace *> whitespace
>            ,lineComment *> whitespace
>            ,blockComment *> whitespace
>            ,return ()]
>   where
>     lineComment = try (string "--")
>                   *> manyTill anyChar (void (char '\n') <|> eof)
>     blockComment = try (string "/*")
>                    *> manyTill anyChar (try $ string "*/")
>     simpleWhitespace = void $ many1 (oneOf " \t\n")

> lexeme :: Parser a -> Parser a
> lexeme p = p <* whitespace

> identifier :: Parser String
> identifier = lexeme ((:) <$> firstChar <*> many nonFirstChar)
>   where
>     firstChar = letter <|> char '_'
>     nonFirstChar = digit <|> firstChar

> symbol :: String -> Parser String
> symbol s = try $ lexeme $ do
>     u <- many1 (oneOf "<>=+-^%/*!|:")
>     guard (s == u)
>     return s

> openParen :: Parser Char
> openParen = lexeme $ char '('

> closeParen :: Parser Char
> closeParen = lexeme $ char ')'

> stringToken :: Parser String
> stringToken = lexeme (char '\'' *> manyTill anyChar (char '\''))

> dot :: Parser Char
> dot = lexeme $ char '.'

> eq :: Parser Char
> eq = lexeme $ char '='

> gt :: Parser Char
> gt = lexeme $ char '>'

> lt :: Parser Char
> lt = lexeme $ char '<'

> comma :: Parser Char
> comma = lexeme $ char ','

> semiColon :: Parser Char
> semiColon = lexeme $ char ';'

> unknown :: Parser ()
> unknown = char '?' *> (void $ char '?')

> unionall :: Parser ()
> unionall = keyword_ "union" *> (void $ keyword_ "all")

== helper functions

> keyword :: String -> Parser String
> keyword k = try $ do
>     i <- identifier
>     guard (i == k || map toLower i == k)
>     return k

> parens :: Parser a -> Parser a
> parens = between openParen closeParen

> commaSep :: Parser a -> Parser [a]
> commaSep = (`sepBy` comma)

> keyword_ :: String -> Parser ()
> keyword_ = void . keyword

> symbol_ :: String -> Parser ()
> symbol_ = void . symbol

> commaSep1 :: Parser a -> Parser [a]
> commaSep1 = (`sepBy1` comma)

> identifierBlacklist :: [String] -> Parser String
> identifierBlacklist bl = do
>     i <- identifier
>     guard (i `notElem` bl)
>     return i

> suffixWrapper :: (a -> Parser a) -> a -> Parser a
> suffixWrapper p a = p a <|> return a

== the parser api

> parseQueryExpr' :: String -> Either ParseError QueryExpr
> parseQueryExpr' = parse (whitespace *> queryExpr <* eof) "" 

> parseQueryExpr :: String -> Either String QueryExpr
> parseQueryExpr source = 
>   let r = parseQueryExpr' (toLower <$> source) in
>   case r of
>     Left e -> Left (show e)
>     Right ast -> passQuery ast

> parseValueExpr :: String -> Either ParseError ValueExpr
> parseValueExpr = parse (whitespace *> valueExpr [] <* eof) ""

== test cases

> makeSelect :: QueryExpr
> makeSelect = Select {qSelectList = []
>                     ,qFrom = Nothing
>                     ,qWhere = Nothing
>                     ,qGroup = Nothing
>                     ,qDistinct = False}

> makeTest :: (String, QueryExpr) -> Test
> makeTest (src, expected) = TestLabel src $ TestCase $ do
>     let gote = parseQueryExpr src
>     case gote of
>       Left e -> assertFailure $ e
>       Right got -> assertEqual src expected got
