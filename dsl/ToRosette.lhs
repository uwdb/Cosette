{-# LANGUAGE OverloadedStrings #-}
= Convert Cosette AST to rosette program

> module ToRosette where

> import CosetteParser
> import Text.Parsec.Error as PE
> import Data.List (unwords, lookup, findIndex)
> import Data.Char (toLower)
> import Data.Foldable (foldMap)
> import Utilities

== Rosette Abstract Syntax

> data RosTableExpr = RosTRBase String
>                   | RosTRQuery RosQueryExpr
>                   | RosUnion RosTableExpr RosTableExpr
>                     deriving (Eq, Show)

> data RosTableRef = RosTR RosTableExpr String
>                  | RosTRXProd RosTableRef RosTableRef
>                    deriving (Eq, Show)

> data RosValueExpr = RosNumLit Integer
>                   | RosDIden String String
>                   | RosBinOp RosValueExpr String RosValueExpr
>                   | RosConstant String
>                   | RosVQE RosQueryExpr
>                   | RosAggVQE String RosQueryExpr  -- query, aggregate fun
>                   | RosAgg String RosValueExpr
>                     deriving (Eq, Show)

> data RosPredicate = RosTRUE
>                   | RosFALSE
>                   | RosNaryOp String [String]      -- nary func. int-> ... -> bool
>                   | RosAnd RosPredicate RosPredicate
>                   | RosOr RosPredicate RosPredicate
>                   | RosNot RosPredicate
>                   | RosExists RosQueryExpr 
>                   | RosVeq RosValueExpr RosValueExpr   -- equal
>                   | RosVgt RosValueExpr RosValueExpr   -- greater than
>                   | RosVlt RosValueExpr RosValueExpr   -- less than
>                  deriving (Eq, Show)

> data RosQueryExpr = RosQuery {rosSelectList :: [RosValueExpr]
>                              ,rosFrom :: Maybe [RosTableRef]
>                              ,rosWhere :: Maybe RosPredicate
>                              ,rosGroup :: Maybe [RosValueExpr]
>                              ,rosDistinct :: Bool
>                              ,rosSchema :: (String, [String])
>                              }
>                   | RosQueryUnion RosQueryExpr RosQueryExpr
>                   | RosQueryAgg {rosAggQE:: RosQueryExpr
>                                 ,rosAggGB::[RosValueExpr]
>                                 ,rosAggFun:: String
>                                 ,rosAggTarget:: RosValueExpr
>                                 ,rosAggSchema:: (String, [String])}
>                         -- to SELECT-GROUP 
>                   deriving (Eq, Show)

> data RosSchema =
>   MakeRosSchema {rosSName :: String   -- schema name
>                 ,rosAttrs :: [(String, String)] -- name, typename
>                 } deriving (Eq, Show)

Some Utility functions

rename schema

> renameSchema :: RosSchema -> String -> RosSchema
> renameSchema r n = MakeRosSchema n (rosAttrs r)

find a schema from a list by name

> findScm :: [RosSchema] -> String -> Either String RosSchema
> findScm rs a = lkUp rs (\e n -> (rosSName e == n)) a

This function takes a list of table-schema mappings and a list of schemas,
generate a list of schemas with names replaced by table names.
It returns [(tableSchema, indexStr)] or error message.

> tableScms :: [(String, String)] -> [RosSchema]
>   -> Either String [RosSchema]
> tableScms tsl sl =
>   checkListErr $
>   map (\a -> renameSchema <$> findScm sl (snd a) <*> Right (fst a)) tsl

=== convert * to concrete projections

> elimStar :: [RosSchema] -> QueryExpr -> Either String QueryExpr
> elimStar scms (UnionAll q1 q2) =
>   UnionAll <$> elimStar scms q1 <*> elimStar scms q2
> elimStar scms (Select sl fr wh g d) =
>   do rs <- getFromScms scms fr
>      sl' <- checkListErr (map (starToSelect rs scms) sl)
>      fr' <- convFr fr
>      wh' <- convWh wh
>      return (Select (foldl (++) [] sl') fr' wh' g d)
>   where convWh Nothing = Right Nothing
>         convWh (Just w) = Just <$> elimStarInPred scms w
>         convFr Nothing  = Right Nothing
>         convFr (Just tl) = Just <$> (checkListErr $ map convTR tl)
>         convTR (TR te a) = TR <$> convTE te <*> Right a
>         convTE (TRQuery q) = TRQuery <$> elimStar scms q
>         convTE (TRUnion t1 t2) = TRUnion <$> convTE t1 <*> convTE t2
>         convTE t = Right t
 
extract [RosSchema] from FROM clause
the first argument is a list of RosSchemas from the environment
(schema name replaced with table name already)

> getFromScms :: [RosSchema] -> Maybe [TableRef] -> Either String [RosSchema]
> getFromScms rs (Nothing) = Right []
> getFromScms rs (Just tl) = checkListErr (getTRScm rs <$> tl)

extract RosSchema from a TableRef
the first argument is a list of RosSchemas fromt the environment
(schema name replaced with table name already)

> getTRScm :: [RosSchema] -> TableRef -> Either String RosSchema
> getTRScm rs (TR te a) = convTE te a
>   where convTE (TRBase r) a = renameSchema <$> (findScm rs r) <*> Right a
>         convTE (TRUnion t1 t2) a = convTE t1 a
>         convTE (TRQuery q) a = MakeRosSchema
>                                <$> Right a
>                                <*> getQueryScms rs q

extract output schema from a query. we don't care data type in rosette code for now,
so every type is int.

> getQueryScms :: [RosSchema] -> QueryExpr
>   -> Either String [(String, String)]
> getQueryScms rs (UnionAll q1 q2) = getQueryScms rs q1
> getQueryScms rs (Select sl fr wh g d) =
>   foldMap id <$> checkListErr (f <$> sl)
>   where f (Proj v a) = Right [(a, "int")]
>         f Star = foldMap rosAttrs <$> getFromScms rs fr
>         f (DStar r) = do scms <- getFromScms rs fr
>                          scm <- findScm scms r
>                          return (rosAttrs scm)

star to select item
rs: the schema list from the FROM clause 
sl: the schema list from the env, this is needed for subqueries in SELECT

> starToSelect :: [RosSchema] -> [RosSchema] -> SelectItem -> Either String [SelectItem]
> starToSelect rs sl (Proj v s) =
>   do v' <- elimStarInVE rs sl v
>      return [Proj v' s]
> starToSelect rs sl Star = Right (foldMap scmToList rs)
> starToSelect rs sl (DStar a) = scmToList <$> findScm rs a 

> scmToList :: RosSchema -> [SelectItem]
> scmToList (MakeRosSchema n al) =
>   (\a -> Proj (DIden n a) a) <$> (map fst al)

remove star in predicate

> elimStarInPred :: [RosSchema] -> Predicate -> Either String Predicate
> elimStarInPred sl (And p1 p2) = And
>                                 <$> elimStarInPred sl p1
>                                 <*> elimStarInPred sl p2
> elimStarInPred sl (Or p1 p2) = Or
>                                <$> elimStarInPred sl p1
>                                <*> elimStarInPred sl p2
> elimStarInPred sl (Not p) = Not <$> elimStarInPred sl p
> elimStarInPred sl (Exists q) = Exists <$> elimStar sl q
> elimStarInPred sl (Veq v1 v2) = Veq
>                                 <$> elimStarInVE [] sl v1
>                                 <*> elimStarInVE [] sl v2
> elimStarInPred sl (Vgt v1 v2) = Vgt
>                                 <$> elimStarInVE [] sl v1
>                                 <*> elimStarInVE [] sl v2
> elimStarInPred sl (Vlt v1 v2) = Vlt
>                                 <$> elimStarInVE [] sl v1
>                                 <*> elimStarInVE [] sl v2
> elimStarInPred sl other = Right other

remove star in value expression

here, we put the last attribute of the last relation in place of star if the aggregation
function is count. star should not appear in any other aggregation function.

rs: the schema list from the FROM clause 
sl: the schema list from the env, this is needed for subqueries in SELECT

> elimStarInVE :: [RosSchema] -> [RosSchema] -> ValueExpr -> Either String ValueExpr
> elimStarInVE rs sl (BinOp v1 o v2) =
>   BinOp <$> elimStarInVE rs sl v1 <*> Right o <*> elimStarInVE rs sl v2
> elimStarInVE rs sl (VQE q) = VQE <$> elimStar sl q
> elimStarInVE rs sl (Agg s a) = Agg s <$> f a
>   where f AStar = if (map toLower s == "count")
>                   then let r = last rs
>                        in let a' = fst $ head (rosAttrs r)
>                           in Right (AV (DIden (rosSName r) a'))
>                   else Left ("you cannot use * in aggregation " ++ s)
>         f (AV v) = AV <$> elimStarInVE rs sl v
> elimStarInVE rs sl other = Right other

=== convert select

the base case

> makeRosSelectItem :: [RosSchema] -> [RosSchema] ->
>                      SelectItem -> Either String (RosValueExpr, String)
> makeRosSelectItem tl al Star = Left "* shouldn't appear at this stage. \n"
> makeRosSelectItem tl al (Proj v s) =  (,) <$> makeRosVE tl al v <*> Right s
> makeRosSelectItem tl al (DStar s) =
>   Left (s ++ ".* shouldn't appear at this stage \n")

> makeRosVE :: [RosSchema] -> [RosSchema] -> ValueExpr
>           -> Either String RosValueExpr
> makeRosVE tl al (NumLit i) = Right (RosNumLit i)
> makeRosVE tl al (DIden r a) = Right (RosDIden r a)
> makeRosVE tl al (BinOp v1 o v2) =  RosBinOp
>                                    <$> makeRosVE tl al v1
>                                    <*> Right o <*> makeRosVE tl al v2
> makeRosVE tl al (VQE q) = RosVQE <$> cosToRos tl al q "anyname"
> makeRosVE tl al (Agg o e) =
>   case (map toLower o) of
>     "sum" -> RosAgg "aggr-sum" <$> aggToVE e
>     "count" -> RosAgg "aggr-count" <$> aggToVE e
>     "max" -> RosAgg "aggr-max" <$> aggToVE e
>     "min" -> RosAgg "aggr-min" <$> aggToVE e
>     o' -> Left (o' ++ " is not supported as an aggregation function.")
>   where aggToVE (AV (DIden t a)) = Right $ RosDIden t a
>         aggToVE _ = Left "only support aggregate on an attribute."

convert select

> makeRosSelect :: [RosSchema] -> [RosSchema] -> [SelectItem] ->
>                  Either String [(RosValueExpr, String)]
> makeRosSelect tl al sl = checkListErr $ (makeRosSelectItem tl al <$> sl) 

=== convert from

the base case

TODO: the handling of union of tables is not ideal, need to be revised

1st argument: a list of schemas (with table names) from env.

> makeRosFromItem :: [RosSchema] -> TableRef -> Either String RosTableRef
> makeRosFromItem tl (TR te alias) = RosTR <$> conv te <*> Right alias
>   where conv (TRBase tn) = RosTRBase <$> tnToIdxStr tn 
>         conv (TRQuery q) = RosTRQuery <$> cosToRos tl [] q alias 
>         conv (TRUnion t1 t2) = RosUnion <$> conv t1 <*> conv t2
>         tnToIdxStr tn =
>           let i = findIndex (\a -> (rosSName a == tn)) tl in
>             case i of
>               Nothing -> Left $ "Cannot find " ++ tn 
>               Just i' -> Right $
>                          "(list-ref tables " ++ (show i') ++ ")" 


convert from

> makeRosFrom :: [RosSchema] -> Maybe [TableRef]
>             -> Either String (Maybe [RosTableRef])
> makeRosFrom tl Nothing = Right Nothing
> makeRosFrom tl (Just fr) =
>   Just <$> checkListErr (makeRosFromItem tl <$> fr)

=== convert where

1st argument: a list of schemas (with table names) from env.
2nd argument: a list of schemas (with alias names) from FROM clause and env.

> makeRosPred :: [RosSchema] -> [RosSchema] -> Predicate
>             -> Either String RosPredicate
> makeRosPred tl al TRUE = Right RosTRUE
> makeRosPred tl al FALSE = Right RosFALSE
> makeRosPred tl al (PredVar n s) = convPredVar al n s
> makeRosPred tl al (And p1 p2) = RosAnd <$> makeRosPred tl al p1
>                              <*> makeRosPred tl al p2
> makeRosPred tl al (Or p1 p2) = RosOr <$> makeRosPred tl al p1
>                             <*> makeRosPred tl al p2
> makeRosPred tl al (Not p) = RosNot <$> makeRosPred tl al p
> makeRosPred tl al (Exists q) = RosExists <$> cosToRos tl al q "anyname"
> makeRosPred tl al (Veq v1 v2) = RosVeq <$> makeRosVE tl al v1 <*>
>                                 makeRosVE tl al v2
> makeRosPred tl al (Vgt v1 v2) = RosVgt <$> makeRosVE tl al v1 <*>
>                                 makeRosVE tl al v2
> makeRosPred tl al (Vlt v1 v2) = RosVlt <$> makeRosVE tl al v1 <*>
>                                 makeRosVE tl al v2

> convPredVar ::  [RosSchema] -> String -> [String]
>             -> Either String RosPredicate
> convPredVar rs n s = RosNaryOp <$> Right n <*> al
>   where al = do scms <- checkListErr $ map (findScm rs) s
>                 scms' <- Right (map toRosAttr scms)
>                 return (foldl (++) [] scms')
>         toRosAttr (MakeRosSchema n attrs) =
>           map (\a -> n ++ "." ++ (fst a)) attrs         

> makeRosWhere :: [RosSchema] -> [RosSchema] -> Maybe Predicate ->
>                 Either String (Maybe RosPredicate)
> makeRosWhere tl al Nothing = Right Nothing
> makeRosWhere tl al (Just p) = Just <$> makeRosPred tl al p

=== Cosette AST -> Rosette AST

unzip result

tl: a list of schemas (with table names) from env.
al: a list of schemas (with alias names) from env.
qe: query expression
name: alias of the query

> makeRosQuery :: [RosSchema] -> [RosSchema] -> QueryExpr
>   -> String -> Either String RosQueryExpr
> makeRosQuery tl al qe name =
>   do sl' <- (fst <$> sl)  -- select list
>      fr <- (makeRosFrom tl $ qFrom qe)
>      fr_al <- (convFr $ qFrom qe)
>      wh <- (makeRosWhere tl (al++fr_al) $ qWhere qe)
>      gr <- (convGr $ qGroup qe)
>      dis <- Right (qDistinct qe)
>      scm <- ((,) <$> Right name <*> (snd <$> sl))
>      return (RosQuery sl' fr wh gr dis scm)
>   where sl  = unzip <$> (makeRosSelect tl al $ qSelectList qe) -- unzip result
>         convFr Nothing = Right []
>         convFr (Just fl) = checkListErr $ map (getTRScm tl) fl
>         convGr Nothing =  Right Nothing
>         convGr (Just grl) =
>           case checkListErr $ map (makeRosVE tl al) grl of
>             Right l -> Right (Just l)
>             Left e -> Left e
 
convert list of tables (or subqueries) in from clause to joins

> convertFrom :: RosQueryExpr -> RosQueryExpr
> convertFrom (RosQueryUnion q1 q2) = RosQueryUnion (convertFrom q1) (convertFrom q2)
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

Finally, convert Cosette AST to Rosette AST, and transform Rosette AST

pass 0: generate Rosette AST

tl: a list of schemas (with table names) from env.
al: a list of schemas (with alias names) from env.

> cosToRos :: [RosSchema] -> [RosSchema] -> QueryExpr
>          -> String -> Either String RosQueryExpr
> cosToRos tl al (UnionAll q1 q2) s =
>   RosQueryUnion <$> cosToRos tl al q1 s <*> cosToRos tl al q2 s
> cosToRos tl al q s = convertFrom <$> makeRosQuery tl al q s   -- basic query

pass 1 on Rosette AST, handle aggregate without group by

> handleAgg :: [RosSchema] -> [RosSchema] -> RosQueryExpr
>           -> Either String RosQueryExpr
> handleAgg tl al q =
>   if length sl == 1 then
>     case head sl of
>       RosAgg af ve -> case rosGroup q of
>                         Just gl -> Right q            -- already group by, do nothing
>                         Nothing -> Right (RosQuery sl -- group by with empty group 
>                                            (rosFrom q)
>                                            (rosWhere q)
>                                            (Just [])
>                                            (rosDistinct q)
>                                            (rosSchema q))
>       _ -> Right q
>   else Right q
>   where sl = (rosSelectList q)
  
pass 2 on Rosette AST, handle QueryExpr in ValueExpr,
currently only support aggregate without group by

> handleQueryAsValue :: [RosSchema] -> [RosSchema] -> RosQueryExpr
>                    -> Either String RosQueryExpr
> handleQueryAsValue tl al (RosQuery sl fr wh gr dis sch) =
>   RosQuery <$> (checkListErr $ map convVE sl)
>            <*> Right fr
>            <*> convWhere wh
>            <*> Right gr
>            <*> Right dis
>            <*> Right sch
>   where convVE (RosVQE (RosQuery sl' fr' wh' gr' dis' sch')) =
>           case sl' of
>             [RosAgg af v] -> if gr' == Just []
>                              then Right (RosAggVQE af (RosQuery [v] fr' wh' gr' dis' sch'))
>                              else Left "QueryExpr as Value can only be aggregate."
>             _ -> Left "QueryExpr as Value can only be aggregate."
>         convVE other = Right other
>         convPred (RosVeq v1 v2) = RosVeq <$> convVE v1 <*> convVE v2
>         convPred (RosVgt v1 v2) = RosVgt <$> convVE v1 <*> convVE v2
>         convPred (RosVlt v1 v2) = RosVlt <$> convVE v1 <*> convVE v2
>         convPred (RosAnd p1 p2) = RosAnd <$> convPred p1 <*> convPred p2
>         convPred (RosOr p1 p2) = RosOr <$> convPred p1 <*> convPred p2
>         convPred (RosNot p) = RosNot <$> convPred p
>         convPred other = Right other
>         convWhere Nothing = Right Nothing
>         convWhere (Just p) = Just <$> convPred p


pass 3 on Rosette AST, handle group by. Only need to do basic query form here.
Union is handled in applyPass.

> handleGroupBy :: [RosSchema] -> [RosSchema] -> RosQueryExpr
>               -> Either String RosQueryExpr
> handleGroupBy tl al q =
>   case rosGroup q of
>     Nothing -> Right q           -- do nothing if there is no group by
>     Just gbc ->                  -- to RosQueryAgg
>       case lastField of
>         RosAgg aggf target -> RosQueryAgg
>                           <$> Right (RosQuery (initFields ++ [target])
>                                       (rosFrom q)
>                                       (rosWhere q)
>                                       (rosGroup q)
>                                       (rosDistinct q)
>                                       (rosSchema q))
>                           <*> sl
>                           <*> Right aggf
>                           <*> Right tar
>                           <*> Right (rosSchema q)
>         _ -> Right $ RosQuery     -- to distinct if no aggregation 
>                        (rosSelectList q)
>                        (rosFrom q)
>                        (rosWhere q)
>                        Nothing
>                        True
>                        (rosSchema q)
>       where scm = rosSchema q
>             lastField = last $ rosSelectList q
>             initFields = init $ rosSelectList q
>             alias = last $ snd (rosSchema q)
>             noOnAgg (RosAgg _ _) = Left "We currently only support single aggregation in the end of SELECT list."
>             noOnAgg other = Right other
>             sl = case checkListErr $ map noOnAgg initFields of
>                    Left err -> Left err
>                    Right _ -> Right $ map (RosDIden (fst scm)) (init $ snd scm) 
>             (n, attrs) = rosSchema q
>             tar = RosDIden n alias

> type RosPass =
>   [RosSchema] -> [RosSchema] -> RosQueryExpr -> Either String RosQueryExpr

recursively apply query passes to query. query pass must has type RosPass

> applyPass :: RosPass -> [RosSchema] -> [RosSchema] -> RosQueryExpr
>           -> Either String RosQueryExpr
> applyPass p tl al (RosQueryUnion q1 q2) =
>   RosQueryUnion <$> p tl al q1 <*> p tl al q2
> applyPass p tl al (RosQueryAgg q sl aggf target scm) =
>   Right (RosQueryAgg q sl aggf target scm)   -- handleGroupBy is the last call, no need go deeper 
> applyPass p tl al (RosQuery sl fr wh gr d scm) =
>   let qPrev = (RosQuery sl fr wh gr d scm)
>   in let qNew = RosQuery
>                 <$> (checkListErr $ map convVE sl)
>                 <*> newFr
>                 <*> newPred
>                 <*> Right gr
>                 <*> Right d
>                 <*> Right scm
>   in case qNew of
>     Left _ -> qNew
>     Right qNew' -> if qPrev == qNew'
>                      then p tl al qPrev   -- end of recursion
>                      else applyPass p tl al qNew' 
>   where convVE (RosVQE q) = RosVQE <$> applyPass p tl al q
>         convVE ve = Right ve
>         convTR (RosTR te n) = RosTR <$> convTE te <*> Right n
>         convTR (RosTRXProd t1 t2) = RosTRXProd <$> convTR t1 <*> convTR t2
>         convTE (RosUnion t1 t2) = RosUnion <$> convTE t1 <*> convTE t2
>         convTE (RosTRQuery tq) = RosTRQuery <$> applyPass p tl al tq
>         convTE te = Right te
>         newFr = case fr of
>                   Nothing -> Right Nothing
>                   Just fl -> Just <$> (checkListErr $ map convTR fl)
>         convPred (RosAnd p1 p2) = RosAnd <$> convPred p1 <*> convPred p2
>         convPred (RosOr p1 p2) = RosOr <$> convPred p1 <*> convPred p2
>         convPred (RosNot pr) = RosNot <$> convPred pr
>         convPred (RosExists q) = RosExists <$> applyPass p tl al q
>         convPred (RosVeq v1 v2) = RosVeq <$> convVE v1 <*> convVE v2
>         convPred (RosVgt v1 v2) = RosVgt <$> convVE v1 <*> convVE v2
>         convPred (RosVlt v1 v2) = RosVlt <$> convVE v1 <*> convVE v2
>         convPred pred = Right pred  -- do nothing for other predicate
>         newPred = case wh of
>                     Nothing -> Right Nothing
>                     Just pred -> Just <$> (convPred pred)
>         

do all the passes here.

> toRosQuery :: [RosSchema] -> [RosSchema] -> QueryExpr
>            -> String -> Either String RosQueryExpr
> toRosQuery tl al q s = 
>   do ros1 <- cosToRos tl al q s
>      ros2 <- applyPass handleAgg tl al ros1
>      ros3 <- applyPass handleQueryAsValue tl al ros2
>      ros4 <- applyPass handleGroupBy tl al ros3
>      return ros4

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

> instance Sexp RosValueExpr where
>   toSexp (RosNumLit i) = show i
>   toSexp (RosDIden s1 s2) = "\"" ++ s1 ++ "." ++ s2 ++ "\""
>   toSexp (RosBinOp v1 op v2) =  addParen 
>     $ unwords ["VAL-BINOP", toSexp v1, op, toSexp v2]
>   toSexp (RosAggVQE af q) = addParen $ uw ["AGGR-SUBQ", af, toSexpSchemaless q]    -- need to unwrap relation to value, currently only support aggregate without groupby
 
convert Predicate to sexp

> instance Sexp RosPredicate where
>   toSexp RosTRUE = "(TRUE)"
>   toSexp RosFALSE = "(FALSE)"
>   toSexp (RosNaryOp p al) = addParen $
>     uw (["NARY-OP", p] ++ (map (\a-> "\"" ++ a ++ "\"") al))
>   toSexp (RosAnd p1 p2) = addParen $ uw ["AND", toSexp p1, toSexp p2]
>   toSexp (RosOr p1 p2) = addParen $ uw ["OR", toSexp p1, toSexp p2]
>   toSexp (RosNot p) = addParen $ uw ["NOT", toSexp p]
>   toSexp (RosVeq v1 v2) = addParen $ uw ["BINOP", toSexp v1, "=", toSexp v2]
>   toSexp (RosVgt v1 v2) = addParen $ uw ["BINOP", toSexp v1, ">", toSexp v2]
>   toSexp (RosVlt v1 v2) = addParen $ uw ["BINOP", toSexp v1, "<", toSexp v2]
>   toSexp (RosExists q) = addParen $ uw ["EXISTS", toSexp q]

convert RosTableRef to sexp

> instance Sexp RosTableExpr where
>   toSexp (RosTRBase tn) = tn
>   toSexp (RosTRQuery q) = toSexp q
>   toSexp (RosUnion t1 t2) = addParen $ uw ["TABLE-UNION-ALL", toSexp t1, toSexp t2]

> instance Sexp RosTableRef where
>   toSexp (RosTR t a) =
>     case t of
>       RosTRQuery q -> toSexp t
>       _ -> addParen $ uw ["NAMED",
>                           "(RENAME",
>                           toSexp t,
>                           (addEscStr a) ++ ")"]
>   toSexp (RosTRXProd q1 q2) = addParen $ uw ["JOIN", toSexp q1, toSexp q2]

convert RosQueryExpr to sexp

-- TODO: handle from nothing in rosette ("UNIT")

Since query with only aggregation (no group by) and group by query requires their own syntactic rewrite, we need to first handle these two cases.

> instance Sexp RosQueryExpr where
>   toSexp q = addParen $ uw ["AS", spj, sch]
>     where spj = toSexpSchemaless q
>           sch' = case q of
>                    RosQueryUnion q1 q2 -> rosSchema q1
>                    RosQueryAgg _ _ _ _ scm -> scm
>                    _ -> rosSchema q
>           sch = addSParen $ uw [addEscStr (fst sch'), al]
>           al = addParen $ uw ("list":(addEscStr <$> snd sch'))

convert RosQueryExpr to s-expression string without adding schema. 

> toSexpSchemaless :: RosQueryExpr -> String
> toSexpSchemaless (RosQueryAgg q gb f tar _) =
>   addParen $ uw ["SELECT-GROUP", toSexp q, gb', f, toSexp tar]
>   where gb'  = addParen $ uw ("list" : map toSexp gb)
> toSexpSchemaless (RosQueryUnion q1 q2) =
>   addParen $ uw ["UNION-ALL", toSexpSchemaless q1, toSexpSchemaless q2]
> toSexpSchemaless (RosQuery sl fl p _ dis _) = 
>   addParen $ uw [sel, sl', "\n  FROM", fl', "\n  WHERE", p']
>   where sl' = addParen $ uw ("VALS": map toSexp sl)
>         fl' = case fl of Nothing -> "UNIT"
>                          Just fr -> toSexp $ head fr -- assuming converted from list to singleton
>         p' =  case p of Nothing -> addParen $ "TRUE"
>                         Just wh -> toSexp wh
>         sel = if dis then "SELECT-DISTINCT" else "SELECT"

generate rosette code.

> genRos :: [CosetteStmt] -> Either String String
> genRos sts = genRos' [] [] [] [] [] sts

the first pass of the statements.

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
>   do sl' <- tableScms tsl sl              -- put tableNames in schemas
>      qe1 <- findQ q1 ql                    
>      qe2 <- findQ q2 ql                   -- find query expressions 
>      qe1' <- elimStar sl' qe1
>      qe2' <- elimStar sl' qe2   -- get rid of stars in queries
>      rsq1 <- toRosQuery sl' [] qe1' q1
>      rsq2 <- toRosQuery sl' [] qe2' q2
>      rs1 <- Right (toSexpSchemaless rsq1)
>      rs2 <- Right (toSexpSchemaless rsq2)
>      preds <- predDecs pl sl
>      tbs <- tableDecs sl'
>      return ((joinWithBr headers) ++ tbs ++ preds ++ (genQ q1 rs1) ++ (genQ q2 rs2) ++ (genSolve sl' q1 q2))
>   where
>     findQ q' ql' = case lookup q' ql' of
>                      Just qe -> Right qe
>                      Nothing -> Left ("Cannot find " ++ q' ++ ".")

generate declarations of symbolic predicate (generic predicate)

> predDecs :: [(String, [String])] -> [RosSchema] -> Either String String
> predDecs pl sl =
>   do pl' <- checkListErr $ map f pl
>      return (joinWithBr pl')
>   where
>     f p = do scms <- checkListErr $ map (findScm sl) (snd p)
>              scms' <- Right (map rosAttrs scms)
>              al <- Right (foldl (++) [] scms') 
>              return ("(define-symbolic " ++ (fst p) ++ " (~> " ++
>                     (uw $ map (\a -> "integer?") al) ++ " boolean?))\n")

generate declarations of symbolic tables.
Table-Schema map, schema list
The first argument must be a list of schemas representing TABLEs, with
schema name replaced by table names.

> tableDecs :: [RosSchema] -> Either String String
> tableDecs sl = Right (joinWithBr tl)
>   where tl = map f sl
>         f t =
>           let n = rosSName t in
>             let scm = rosAttrs t in
>               "(define " ++ n ++ "-info (table-info \"" ++ n 
>               ++ "\" (list " ++ (uw $ map (addQuote . fst) scm) ++ ")))\n"
>         addQuote x = "\"" ++ x ++ "\""
>         


Number of rows of symbolic relations, to be replaced by incremental solving

> numOfRows :: Integer
> numOfRows = 1

> headers :: [String]
> headers = ["#lang rosette \n",
>            "(require \"../cosette.rkt\" \"../util.rkt\" \"../table.rkt\"",
>            "         \"../sql.rkt\" \"../evaluator.rkt\" \"../equal.rkt\") \n",
>            "(provide ros-instance)\n",
>            "(current-bitwidth #f)\n"]

> genQ :: String -> String -> String
> genQ qn q = "(define (" ++ qn ++ " tables) \n  " ++ q ++ ")\n\n"

The first argument must be a list of schemas representing TABLEs, with
schema name replaced by table names.

> genSolve :: [RosSchema] -> String -> String -> String
> genSolve tl q1 q2 = "\n(define ros-instance (list " ++ q1 ++ " " ++ q2 ++ " (list "
>                     ++ (uw $ map (\a -> (rosSName a) ++ "-info") tl)
>                     ++ "))) \n"


