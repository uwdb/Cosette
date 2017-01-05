{-# LANGUAGE OverloadedStrings #-}
= Convert Cosette AST to rosette program

> module ToRosette where

> import CosetteParser
> import Text.Parsec.Error as PE
> import Data.List (unwords)

== TO BE Deleted

> testQuery2 :: QueryExpr
> testQuery2 = Select [Proj (DIden "t2" "c1") "tc1",Proj (DIden "t2" "c2") "tc2",Proj (DIden "t2" "c3") "tc3"]
>            (Just [(TRQuery (Select [Proj (DIden "t1" "c1") "c1",Proj (DIden "t1" "c2") "c2",Proj (DIden "t1" "c3") "c3"]
>                           (Just [(TRBase "t1" "t1")])
>                           (Just (Vlt (DIden "t1" "c1") (DIden "t1" "c2")))) "t2")])
>            (Just (Vlt (DIden "t2" "c1") (DIden "t2" "c3")))

> testQuery3 :: QueryExpr
> testQuery3 = Select [Proj (DIden "t1" "c1") "tc1",Proj (DIden "t1" "c2") "tc2",Proj (DIden "t1" "c3") "tc3"]
>              (Just [(TRBase "t1" "t1")])
>              (Just (And (Vlt (DIden "t1" "c1") (DIden "t1" "c2")) (Vlt (DIden "t1" "c1") (DIden "t1" "c3"))))

== Rosette Abstract Syntax

> data RosTableRef = RosTRBase String String
>                  | RosTRQuery RosQueryExpr String
>                  | RosJoin RosTableRef RosTableRef
>                    deriving (Eq, Show)

> data RosQueryExpr = RosQuery {rosSelectList :: [ValueExpr]
>                              ,rosFrom :: Maybe [RosTableRef]
>                              ,rosWhere :: Maybe Predicate
>                              ,rosSchema :: (String, [String])
>                              } deriving (Eq, Show)

=== convert select

the base case

> makeRosSelectItem :: SelectItem -> Either String (ValueExpr, String)
> makeRosSelectItem Star = Left "* \n"
> makeRosSelectItem (Proj v s) =  Right (v, s)
> makeRosSelectItem (DStar s) = Left (s ++ ".* \n")

convert select

> makeRosSelect :: [SelectItem]  -> Either String [(ValueExpr, String)]
> makeRosSelect sl = checkListErr $ (makeRosSelectItem <$> sl) 

=== convert from

the base case

> makeRosFromItem :: TableRef -> Either String RosTableRef
> makeRosFromItem (TRBase tn alias) = Right (RosTRBase tn alias)
> makeRosFromItem (TRQuery query alias) =
>   RosTRQuery <$> makeRosQuery query alias <*> Right alias

convert from

> makeRosFrom :: Maybe [TableRef] -> Either String (Maybe [RosTableRef])
> makeRosFrom Nothing = Right Nothing
> makeRosFrom (Just fr) =  Just <$> checkListErr (makeRosFromItem <$> fr)

=== Cosette AST -> Rosette AST

unzip result

> makeRosQuery :: QueryExpr -> String -> Either String RosQueryExpr
> makeRosQuery qe name = RosQuery
>                        <$> (fst <$> sl)  -- select list
>                        <*> (makeRosFrom $ qFrom qe)
>                        <*> Right (qWhere qe)
>                        <*> ((,) <$> Right name <*> (snd <$> sl))
>   where sl  = unzip <$> (makeRosSelect $ qSelectList qe) -- unzip result

convert list of tables (or subqueries) in from clause to joins

> convertFrom :: RosQueryExpr -> RosQueryExpr
> convertFrom q = RosQuery
>                   (rosSelectList q)
>                   ((\a -> [a]) <$> (toJoin fr))
>                   (rosWhere q)
>                   (rosSchema q)
>   where fr' = rosFrom q
>         fr =  fmap (\t ->
>                      (case t of RosTRQuery q a
>                                   -> RosTRQuery (convertFrom q) a
>                                 _ -> t)) <$> fr'
>         toJoin Nothing = Nothing
>         toJoin (Just []) = Nothing
>         toJoin (Just [x]) = Just x
>         toJoin (Just [x1, x2]) = Just $ RosJoin x1 x2
>         toJoin (Just (h:t)) = RosJoin <$> Just h <*> toJoin (Just t)

Finally, convert Cosette AST to Rosette AST

> toRosQuery :: QueryExpr -> String -> Either String RosQueryExpr
> toRosQuery q s = convertFrom <$> makeRosQuery q s

=== RosQuery to sexp string

> class Sexp a where
>   toSexp :: a -> String

> addSParen :: String -> String
> addSParen s = "[" ++ s ++ "]"

> addEscStr :: String -> String
> addEscStr s = "\"" ++ s ++ "\""

["a", "b", "c"] to "a b c"

> uw :: [String] -> String
> uw = unwords

convert ValueExpr to sexp

> instance Sexp ValueExpr where
>   toSexp (NumLit i) = show i
>   toSexp (DIden s1 s2) = "\"" ++ s1 ++ "." ++ s2 ++ "\""
>   toSexp (BinOp v1 op v2) =  addParen 
>     $ unwords ["BINOP", toSexp v1, op, toSexp v2]

convert Predicate to sexp

> instance Sexp Predicate where
>   toSexp TRUE = "#t"
>   toSexp FALSE = "#f"
>   toSexp (And p1 p2) = addParen $ uw ["AND", toSexp p1, toSexp p2]
>   toSexp (Or p1 p2) = addParen $ uw ["OR", toSexp p1, toSexp p2]
>   toSexp (Not p) = addParen $ uw ["NOT", toSexp p]
>   toSexp (Veq v1 v2) = addParen $ uw [toSexp v1, "=", toSexp v2]
>   toSexp (Vgt v1 v2) = addParen $ uw [toSexp v1, ">", toSexp v2]
>   toSexp (Vlt v1 v2) = addParen $ uw [toSexp v1, "<", toSexp v2]

convert RosTableRef to sexp

> instance Sexp RosTableRef where
>   toSexp (RosTRBase t a) = addParen $ uw ["RENAME", t, addEscStr a]
>   toSexp (RosTRQuery q a) = addParen $ uw ["RENAME", toSexp q, addEscStr a]
>   toSexp (RosJoin q1 q2) = addParen $ uw ["JOIN", toSexp q1, toSexp q2]

convert RosQueryExpr to sexp

-- TODO: handle from nothing in rosette ("UNIT")

> instance Sexp RosQueryExpr where
>   toSexp q = addParen $ uw ["AS", spj, sch]
>     where spj = addParen $ uw ["SELECT", sl, "FROM", fl, "WHERE", p]
>           sl = addParen $ uw ("VALS": (toSexp <$> rosSelectList q))
>           fl = addParen $ case rosFrom q of Nothing -> "UNIT"
>                                             Just fr -> toSexp $ head fr
>           p = addParen $ case rosWhere q of Nothing -> "filter-empty"
>                                             Just wh -> toSexp wh
>           sch' = rosSchema q
>           sch = addSParen $ uw [addEscStr (fst sch'), al]
>           al = addParen $ uw ("list":(addEscStr <$> snd sch'))
