{-# LANGUAGE OverloadedStrings #-}
= Convert Cosette AST to rosette program

> module ToRosette where

> import CosetteParser
> import Text.Parsec.Error as PE
> import Data.List (unwords)

== Rosette Abstract Syntax

> data RosTableExpr = RosTRBase String
>                   | RosTRQuery RosQueryExpr
>                   | RosUnion RosTableExpr RosTableExpr
>                     deriving (Eq, Show)

> data RosTableRef = RosTR RosTableExpr String
>                  | RosTRXProd RosTableRef RosTableRef
>                    deriving (Eq, Show)

> data RosQueryExpr = RosQuery {rosSelectList :: [ValueExpr]
>                              ,rosFrom :: Maybe [RosTableRef]
>                              ,rosWhere :: Maybe Predicate
>                              ,rosGroup :: Maybe [ValueExpr]
>                              ,rosDistinct :: Bool
>                              ,rosSchema :: (String, [String])
>                              } deriving (Eq, Show)

> data RosSchema = MakeRosSchema {hsSName :: String   -- schema name
>                                ,hsAttrs :: [(String, String)] -- name, typename
>                                } deriving (Eq, Show)

== Util function

> checkListErr :: [Either String a] -> Either String [a]
> checkListErr lt = foldE lt (Right [])
>   where foldE [] x = x
>         foldE (h:t) (Left es) =
>           case h of Left es' -> foldE t (Left (es ++ es'))
>                     Right e  -> foldE t (Left es)
>         foldE (h:t) (Right l) =
>           case h of Left es' -> foldE t (Left es')
>                     Right e  -> foldE t (Right (l ++ [e]))

=== convert select

the base case

TODO: revisit this one for adding support of "*"

> makeRosSelectItem :: SelectItem -> Either String (ValueExpr, String)
> makeRosSelectItem Star = Left "* \n"
> makeRosSelectItem (Proj v s) =  Right (v, s)
> makeRosSelectItem (DStar s) = Left (s ++ ".* \n")

convert select

> makeRosSelect :: [SelectItem]  -> Either String [(ValueExpr, String)]
> makeRosSelect sl = checkListErr $ (makeRosSelectItem <$> sl) 

=== convert from

the base case

TODO: the handling of union of tables is not ideal, need to be revised

> makeRosFromItem :: TableRef -> Either String RosTableRef
> makeRosFromItem (TR te al) = RosTR <$> conv te <*> Right al
>   where conv (TRBase tn) = Right (RosTRBase tn)
>         conv (TRQuery q) = RosTRQuery <$> makeRosQuery q al 
>         conv (TRUnion t1 t2) = RosUnion <$> conv t1 <*> conv t2  

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
>                        <*> Right (qGroup qe)
>                        <*> Right (qDistinct qe)
>                        <*> ((,) <$> Right name <*> (snd <$> sl))
>   where sl  = unzip <$> (makeRosSelect $ qSelectList qe) -- unzip result

convert list of tables (or subqueries) in from clause to joins

> convertFrom :: RosQueryExpr -> RosQueryExpr
> convertFrom q = RosQuery
>                   (rosSelectList q)
>                   ((\a -> [a]) <$> (toJoin fr))
>                   (rosWhere q)
>                   (rosGroup q)
>                   (rosDistinct q)
>                   (rosSchema q)
>   where fr' = rosFrom q
>         fr =  fmap convTr <$> fr'
>         convTr (RosTR te al) = RosTR (convTe te) al
>         convTr tr = tr
>         convTe (RosTRQuery q) = RosTRQuery (convertFrom q)
>         convTe (RosUnion t1 t2) = RosUnion (convTe t1) (convTe t2)
>         convTe b = b
>         toJoin Nothing = Nothing
>         toJoin (Just []) = Nothing
>         toJoin (Just [x]) = Just x
>         toJoin (Just [x1, x2]) = Just $ RosTRXProd x1 x2
>         toJoin (Just (h:t)) = RosTRXProd <$> Just h <*> toJoin (Just t)

Finally, convert Cosette AST to Rosette AST

> toRosQuery :: QueryExpr -> String -> Either String RosQueryExpr
> toRosQuery q s = convertFrom <$> makeRosQuery q s

=== RosQuery to sexp string

> class Sexp a where
>   toSexp :: a -> String

> addParen :: String -> String
> addParen s = "(" ++ s ++ ")"

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

> instance Sexp RosTableExpr where
>   toSexp (RosTRBase tn) = tn
>   toSexp (RosTRQuery q) = toSexp q
>   toSexp (RosUnion t1 t2) = addParen $ uw ["TABLE-UNION-ALL", toSexp t1, toSexp t2]

> instance Sexp RosTableRef where
>   toSexp (RosTR t a) = addParen $ uw ["RENAME", toSexp t, addEscStr a]
>   toSexp (RosTRXProd q1 q2) = addParen $ uw ["JOIN", toSexp q1, toSexp q2]

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

generate rosette code

> genRos :: [CosetteStmt] -> Either String String
> genRos sts = genRos' [] [] [] [] [] sts

the first pass of the statements

> genRos' :: [(String, String)] -> [(String, String)]-> [(String, [String])] -> [RosSchema] -> [(String, QueryExpr)] -> [CosetteStmt] -> Either String String
> genRos' tsl cl pl sl ql (h:t) =
>   case h of
>     Schema sn sl' -> genRos' tsl cl pl (MakeRosSchema sn sl':sl) ql t
>     Table tn sn -> genRos' ((tn, sn):tsl) cl pl sl ql t  
>     Pred pn sn -> genRos' tsl cl ((pn, sn):pl) sl ql t
>     Const cn tn -> genRos' tsl ((cn, tn):cl) pl sl ql t
>     Query qn q -> genRos' tsl cl pl sl ((qn, q): ql) t
>     Verify q1 q2 -> genRosCode tsl cl pl sl ql q1 q2
> genRos' tsl cl pl sl ql _ = Left "Cannot find verify statement."

The actual working horse:
Table-Schema map, constant list, predicate list, schema list, query list,
statement list

> genRosCode ::  [(String, String)] -> [(String, String)]-> [(String, [String])] -> [RosSchema] -> [(String, QueryExpr)] -> String -> String -> Either String String
> genRosCode tsl cl pl sl ql q1 q2 =
>   do qe1 <- findQ q1 ql
>      qe2 <- findQ q2 ql
>      rsq1 <- toRosQuery qe1 q1
>      rsq2 <- toRosQuery qe2 q2
>      rs1 <- Right (toSexp rsq1)
>      rs2 <- Right (toSexp rsq2)
>      return (rs1 ++ "\n" ++ rs2)
>   where
>     findQ q' ql' = case lookup q' ql' of
>                      Just qe -> Right qe
>                      Nothing -> Left ("Cannot find " ++ q' ++ ".")
