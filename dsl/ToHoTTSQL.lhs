{-# LANGUAGE OverloadedStrings #-}

= Convert Cosette AST to rosette program

> module ToHoTTSQL where

> import CosetteParser
> import Text.Parsec.Error as PE
> import Data.List (unwords, intercalate, filter)
> import Data.Set (toList, fromList)
> import Data.Char (toUpper)
> import FunctionsAndTypesForParsing
> import Utilities
> import qualified Data.Map as Map

== HoTTSQL Abstract Syntax

schema

> data HSSchema =  MakeHSSchema {hsSName :: String             -- name of the schema
>                               ,hsAttrs :: [(String, String)] -- name, typename
>                              } deriving (Eq, Show)

environment

> data HSEnv = MakeHSEnv {tables :: [(String, String)]    -- table name, schema name
>                        ,schemas :: [HSSchema]           -- schemas
>                        } deriving (Eq, Show)

> emptyEnv :: HSEnv
> emptyEnv = MakeHSEnv [] []

context

> data HSContext = HSNode HSContext HSContext
>                | HSAbsScm String HSSchema           -- abstract schema
>                | HSScm String HSContext HSContext    -- concrete schema
>                | HSLeaf String String                -- single attribute: name, type
>                | HSEmpty
>                  deriving (Eq, Show)

> renameCtx :: HSContext -> String -> HSContext
> renameCtx (HSNode c1 c2) n = HSScm n c1 c2
> renameCtx (HSAbsScm a s) n = HSAbsScm n s
> renameCtx (HSScm a c1 c2) n = HSScm n c1 c2
> renameCtx others n = others

value expression

> data HSValueExpr = HSDIden String String                   -- eg: r.a  
>                  | HSBinOp HSValueExpr String HSValueExpr  -- eg: r.a + r.b
>                  | HSConstant String                       -- constant
>                  | HSAggVQE String HSQueryExpr             -- aggFun Query
>                  | HSAgg String HSValueExpr                -- eg: count(*)
>                  | HSVStar                                 -- only in count(*)
>                    deriving (Eq, Show)

predicate

> data HSPredicate = HSTrue
>                  | HSFalse
>                  | HSPredVar String [String]
>                  | HSAnd HSPredicate HSPredicate
>                  | HSOr HSPredicate HSPredicate
>                  | HSNot HSPredicate
>                  | HSExists HSQueryExpr
>                  | HSEq HSValueExpr HSValueExpr
>                  | HSGt HSValueExpr HSValueExpr
>                  | HSLt HSValueExpr HSValueExpr
>                    deriving (Eq, Show)

select item

> data HSSelectItem = HSStar
>                   | HSDStar String
>                   | HSProj HSValueExpr
>                     deriving (Eq, Show)

table reference

> data HSTableRef = HSTRBase String
>                 | HSTRQuery HSQueryExpr
>                 | HSUnitTable                      -- Unit table
>                 | HSProduct HSTableRef HSTableRef
>                 | HSTableUnion HSTableRef HSTableRef
>                   deriving (Eq, Show)

HoTTSQL query

> data HSQueryExpr = HSSelect
>                  {hsSelectList :: [HSSelectItem]
>                  ,hsFrom :: HSTableRef
>                  ,hsWhere :: HSPredicate
>                  ,hsGroup :: [HSValueExpr]
>                  ,hsDistinct :: Bool}
>                  | HSUnionAll HSQueryExpr HSQueryExpr
>                  deriving (Eq, Show)


== supported binary operators (op, Coq translation)

> binOps :: [(String, String)]
> binOps = [("+", "binaryExpr add"),
>           ("-", "binaryExpr minus")]

== convert Cosette to HoTTSQL

look up schema by table name

> lkUpSchema :: HSEnv -> String -> Either String HSSchema
> lkUpSchema env q = do sn <- lkUp (tables env) (\t q1 -> fst t == q1) q
>                       lkUp (schemas env) (\t q1 -> hsSName t == q1) $ snd sn

look up context by name

> lkUpCtx :: HSContext -> String -> Either String HSContext
> lkUpCtx ctx n = Left $ "cannot find " ++ n

get output context from FROM

> getCtx :: HSEnv -> HSContext -> Maybe [TableRef] -> Either String HSContext
> getCtx env ctx Nothing = Right HSEmpty
> getCtx env ctx (Just fl) = f fl
>   where f [a] = fromTR a
>         f (h:t) = HSNode <$> fromTR h <*> f t
>         f [] = Right HSEmpty
>         fromTR (TR te a) = renameCtx <$> getScm te <*> Right a
>         getScm (TRBase tn) = HSAbsScm <$> Right "" <*> lkUpSchema env tn
>         getScm (TRQuery q) = getOutCtx env ctx "" q
>         getScm (TRUnion t1 t2) = getScm t1

look up a schema (which is a context) in FROM clause by alias

> lkUpScmInFr :: HSEnv -> HSContext -> Maybe [TableRef] -> String
>                  -> Either String HSContext
> lkUpScmInFr env ctx fr a = do ctx' <- getCtx env ctx fr
>                               ret <- lkUpCtx ctx' a
>                               return ret

get output schema (which is a context) of a query
env, out context, query name, query expr.

> getOutCtx :: HSEnv -> HSContext -> String ->  QueryExpr -> Either String HSContext
> getOutCtx env ctx qn q =
>   case q of
>     Select s fr w g d ->
>       do ctx' <- getCtx env ctx fr
>          ret <- convSl ctx' s
>          return ret
>     UnionAll q1 q2 -> getOutCtx env ctx qn q1
>   where f ctx' Star =  Right ctx'
>         f ctx' (DStar r) = lkUpCtx ctx' r
>         f ctx' (Proj e al) = do ty <- getType env (HSNode ctx ctx') e
>                                 return (HSLeaf al ty)
>         convSl ctx' [a] = f ctx' a
>         convSl ctx' (h:t) = HSNode <$> f ctx' h <*> convSl ctx' t
>         convSl ctx' [] = Right HSEmpty

get type of a value expression

TODO: now always return int, type inference to be added.

> getType :: HSEnv -> HSContext -> ValueExpr -> Either String String
> getType env ctx v = Right "int"

convert from clause, it does the following things:
1. convert the list of table to nested joins
2. get rid of table alias

> convertFromItem :: HSEnv -> HSContext -> TableRef -> Either String HSTableRef
> convertFromItem env ctx tr = cte env ctx (getTe tr)
>   where cte env ctx (TRBase tn) = Right $ HSTRBase tn
>         cte env ctx (TRUnion t1 t2) = HSTableUnion <$> cte env ctx t1 <*> cte env ctx t2
>         cte env ctx (TRQuery q) = HSTRQuery <$> toHSQuery env ctx q

> convertFrom :: HSEnv -> HSContext -> Maybe [TableRef] -> Either String HSTableRef
> convertFrom env ctx Nothing = Right HSUnitTable
> convertFrom env ctx (Just []) = Right HSUnitTable
> convertFrom env ctx (Just [x]) = convertFromItem env ctx x
> convertFrom env ctx (Just [x1, x2]) = HSProduct <$> convertFromItem env ctx x1
>                                                 <*> convertFromItem env ctx x2
> convertFrom env ctx (Just (h:t)) = HSProduct <$> convertFromItem env ctx h
>                                              <*> (convertFrom env ctx (Just t))

convert alias to path, and get its schema 
it returns (path, schema) or nothing

> nameToPath' :: HSContext -> String -> Either String ([String], HSContext)
> nameToPath' HSEmpty s = Left $ "cannot find alias " ++ s
> nameToPath' (HSAbsScm al sch) s =
>   if al == s then Right ([], (HSAbsScm al sch)) else Left $ "cannot find alias " ++ s
> nameToPath' (HSScm al lt rt) s =
>   if al == s then Right ([], (HSScm al lt rt)) else nameToPath' (HSNode lt rt) s 
> nameToPath' (HSNode lt rt) s =
>   case nameToPath' rt s of Left _ -> do t <- nameToPath' lt s
>                                         return ("left":(fst t), snd t)
>                            Right t -> Right ("right":(fst t), snd t)
> nameToPath' (HSLeaf _ _) s = Left $ "cannot find alias " ++ s

only return path.

> nameToPath :: HSContext -> String -> Either String String
> nameToPath ctx s = (\x -> intercalate "⋅" (fst x)) <$> nameToPath' ctx s

convert Cosette value expression to HoTTSQL expression

> convertVE :: HSEnv -> HSContext -> ValueExpr -> Either String HSValueExpr
> convertVE env ctx (NumLit i) = Right $ HSConstant ("integer_" ++ (show i))
> convertVE env ctx (DIden tr attr) =
>   do (p, s) <- nameToPath' ctx tr
>      r <- Right (intercalate "⋅" p)
>      arr <- attrToPath s attr
>      a <- Right (intercalate "⋅" arr)
>      return (HSDIden r a)
>   where
>      attrToPath (HSNode lf rt) a =
>        case attrToPath rt a of
>          Left err -> case attrToPath lf a of
>                        Left e -> Left e
>                        Right p -> Right ("left":p)
>          Right p -> Right ("right":p)
>      attrToPath (HSAbsScm rn hs) a =
>        if any (\x-> fst x == a) (hsAttrs hs)
>        then Right [hsSName hs ++ "_" ++ a]
>        else Left $ "cannot find attribute " ++ a
>      attrToPath (HSScm rn lf rt) a = attrToPath (HSNode lf rt) a
>      attrToPath (HSLeaf at ty) a =
>        if a == at then Right []
>        else Left $ "cannot find attribute " ++ a                                     
> convertVE env ctx (BinOp v1 op v2) = HSBinOp <$> convertVE env ctx v1
>                                          <*> Right op
>                                          <*> convertVE env ctx v2
> convertVE env ctx (Constant c) = Right (HSConstant c)
> convertVE env ctx (VQE (Select sl fr wh gb di)) =
>   case sl of
>     [Proj (Agg f v) a] -> if (gb == Nothing)
>                           then let q = (Select [newSI f v a] fr wh gb di) in
>                                  HSAggVQE f <$> toHSQuery env ctx q
>                           else Left err
>     _ -> Left err
>   where err = "Currently only support aggregate without group by as value expression"
>         newSI f v a = case v of
>                         AV v' -> Proj v' a
>                         AStar -> Star
> convertVE env ctx (VQE others) = Left "Currently only support aggregate without group by as value expression"
> convertVE env ctx (Agg f ae) = case ae of
>                                  AV v -> HSAgg f <$> convertVE env ctx v
>                                  AStar -> Right $ HSAgg f HSVStar                                  

convert Cosette predicate to HoTTSQL predicate

> convertPred :: HSEnv -> HSContext -> Predicate -> Either String HSPredicate
> convertPred env ctx TRUE = Right HSTrue
> convertPred env ctx FALSE = Right HSFalse
> convertPred env ctx (PredVar b s) = HSPredVar <$> Right b
>                                     <*> checkListErr (nameToPath ctx <$> s)
> convertPred env ctx (And b1 b2) = HSAnd <$> convertPred env ctx b1
>                                         <*> convertPred env ctx b2
> convertPred env ctx (Or b1 b2) = HSOr <$> convertPred env ctx b1
>                                       <*> convertPred env ctx b2
> convertPred env ctx (Not b) = HSNot <$> convertPred env ctx b
> convertPred env ctx (Exists q) = HSExists <$> toHSQuery env ctx q
> convertPred env ctx (Veq v1 v2) = HSEq <$> convertVE env ctx v1
>                                        <*> convertVE env ctx v2
> convertPred env ctx (Vgt v1 v2) = HSGt <$> convertVE env ctx v1
>                                        <*> convertVE env ctx v2
> convertPred env ctx (Vlt v1 v2) = HSLt <$> convertVE env ctx v1
>                                        <*> convertVE env ctx v2

convert Select when group by is empty

> convertSelect :: HSEnv -> HSContext -> [SelectItem] -> Either String [HSSelectItem]
> convertSelect env ctx l = checkListErr (f <$> l)
>   where f Star = Right HSStar
>         f (DStar x) = HSDStar <$> nameToPath ctx x
>         f (Proj v _) = HSProj <$> convertVE env ctx v

convert where

> convertWhere :: HSEnv -> HSContext -> Maybe Predicate -> Either String HSPredicate
> convertWhere env ctx Nothing = Right HSTrue
> convertWhere env ctx (Just p) = convertPred env ctx p

> convertGroup :: HSContext -> Maybe [ValueExpr] -> Either String [HSValueExpr]
> convertGroup ctx Nothing = Right []
> convertGroup ctx (Just g) = checkListErr $ (convertVE emptyEnv ctx <$> g)


get number literals from Cosette AST.

> getNumberLiterals :: QueryExpr -> [Integer]
> getNumberLiterals (UnionAll q1 q2) =
>   getNumberLiterals q1 ++ getNumberLiterals q2
> getNumberLiterals (Select sl fr wh _ _) =
>   (foldl (++) [] $ map getNumSI sl) ++ getNumFr fr ++ getNumWh wh   
>   where getNumSI (Proj v _) = getNumVE v
>         getNumSI others = []
>         getNumVE (NumLit i) = [i]
>         getNumVE (BinOp v1 o v2) = getNumVE v1 ++ getNumVE v2
>         getNumVE (VQE q) = getNumberLiterals q
>         getNumVE others = []
>         getNumFr Nothing = []
>         getNumFr (Just trs) = (foldl (++) [] $ map getNumTR trs)
>         getNumTR (TR te _) = getNumTE te
>         getNumTE (TRQuery q) = getNumberLiterals q
>         getNumTE (TRUnion t1 t2) = getNumTE t1 ++ getNumTE t2
>         getNumTE others = []
>         getNumWh Nothing = []
>         getNumWh (Just p) = getNumPred p
>         getNumPred (Exists q) = getNumberLiterals q
>         getNumPred (Veq v1 v2) = getNumVE v1 ++ getNumVE v2
>         getNumPred (Vgt v1 v2) = getNumVE v1 ++ getNumVE v2
>         getNumPred (Vlt v1 v2) = getNumVE v1 ++ getNumVE v2
>         getNumPred (And p1 p2) = getNumPred p1 ++ getNumPred p2
>         getNumPred (Or p1 p2) = getNumPred p1 ++ getNumPred p2
>         getNumPred (Not p) = getNumPred p
>         getNumPred others = []

> intToConst :: Integer -> String
> intToConst i = "integer_" ++ (show i)

(recursively) replace star with an attribute

> elimStar :: HSEnv -> HSContext -> QueryExpr
>          -> Either String QueryExpr
> elimStar env ctx (UnionAll q1 q2) =
>   UnionAll <$> elimStar env ctx q1 <*> elimStar env ctx q2
> elimStar env ctx (Select sl fr wh gr di) =
>   do ctx' <- getCtx env ctx fr
>      (r, c) <- findRel ctx'                                         -- find a leaf's paths
>      a <- findLeaf c 
>      sl' <- checkListErr $ map (convSI (DIden r a) (HSNode ctx ctx')) sl
>      fr' <- convFr env ctx fr
>      wh' <- convWh env (HSNode ctx ctx') wh
>      return (Select sl' fr' wh' gr di) 
>   where findRel (HSNode t1 t2) = case (findRel t1, findRel t2) of
>                                    (Left e1, Left e2) -> Left e1
>                                    (Left e, Right a) -> Right a
>                                    (Right a1, Right a2) -> Right a2
>                                    (Right a, Left e) -> Right a
>         findRel (HSAbsScm a s) = Right (a, (HSAbsScm a s))
>         findRel (HSScm a t1 t2) = Right (a, (HSScm a t1 t2))
>         findRel other = Left "Error in elimSatr (ToHoTTSQL.lhs)."
>         findLeaf (HSNode t1 t2) = case (findLeaf t1, findLeaf t2) of
>                                     (Left e1, Left e2) -> Left e1
>                                     (Left err, Right a) -> Right a
>                                     (Right a1, Right a2) -> Right a2
>                                     (Right a, Left err) -> Right a
>         findLeaf (HSAbsScm a s) = Right ((fst . last) $ hsAttrs s)
>         findLeaf (HSScm sn t1 t2) =  findLeaf (HSNode t1 t2)
>         findLeaf (HSLeaf at ty) = Right at
>         findLeaf HSEmpty = Left "cannot find a leaf."
>         convSI v ctx (Proj (Agg f AStar) aname) =
>           Right $ Proj (Agg f (AV v)) aname
>         convSI v ctx (Proj (VQE q) aname) =
>           Proj <$> (VQE <$> elimStar env ctx q) <*> Right aname 
>         convSI v ctx other = Right $ other
>         convFr env ctx Nothing = Right Nothing
>         convFr env ctx (Just fl) = Just <$> (checkListErr $ map (convTR env ctx) fl)
>         convTR env ctx (TR te s) = TR <$> convTE env ctx te <*> Right s
>         convTE env ctx (TRQuery q) = TRQuery <$> elimStar env ctx q
>         convTE env ctx (TRUnion t1 t2) =
>           TRUnion <$> convTE env ctx t1 <*> convTE env ctx t2
>         convTE env ctx base = Right base
>         convWh env ctx Nothing = Right Nothing
>         convWh env ctx (Just p) = Just <$> convPred env ctx p
>         convPred env ctx (And p1 p2) = And <$> convPred env ctx p1 <*> convPred env ctx p2
>         convPred env ctx (Or p1 p2) = Or <$> convPred env ctx p1 <*> convPred env ctx p2
>         convPred env ctx (Not p1) = Not <$> convPred env ctx p1
>         convPred env ctx (Exists q) = Exists <$> elimStar env ctx q
>         convPred env ctx (Veq v1 v2) = Veq <$> convVE env ctx v1 <*> convVE env ctx v2
>         convPred env ctx (Vgt v1 v2) = Vgt <$> convVE env ctx v1 <*> convVE env ctx v2
>         convPred env ctx (Vlt v1 v2) = Vlt <$> convVE env ctx v1 <*> convVE env ctx v2
>         convPred env ctx others = Right others
>         convVE env ctx (VQE q) = VQE <$> elimStar env ctx q
>         convVE env ctx (BinOp v1 op v2) =
>           BinOp <$> convVE env ctx v1 <*> Right op <*> convVE env ctx v2
>         convVE env ctx others = Right others

convert Cosette AST to HoTTSQL AST

> toHSQuery :: HSEnv -> HSContext -> QueryExpr -> Either String HSQueryExpr
> toHSQuery env ctx q = case q of
>                         Select sl fr wh Nothing ds ->
>                           do ctx' <- getCtx env ctx fr
>                              ft' <- convertFrom env ctx fr
>                              sl' <- convertSelect env (HSNode ctx ctx') sl
>                              wh' <- convertWhere env (HSNode ctx ctx') wh
>                              gr' <- Right []
>                              return (HSSelect sl' ft' wh' gr' ds)
>                         Select sl fr wh gr ds ->
>                           case last sl of
>                             Proj (Agg f v) _ ->         -- last proj is a aggregate
>                               do ctx' <- getCtx env ctx fr
>                                  fr' <- convertFrom env ctx fr
>                                  sl' <- case checkListErr $ map noOnAgg initFields of
>                                    Left e -> Left e
>                                    Right _ -> convertSelect env (HSNode ctx ctx') sl
>                                  wh' <- convertWhere env (HSNode ctx ctx') wh
>                                  gr' <- convertGroup (HSNode ctx ctx') gr
>                                  return (HSSelect sl' fr' wh' gr' ds)
>                             _ -> case checkListErr $ map noOnAgg sl of 
>                                    Left e -> Left e
>                                    Right _ -> toHSQuery env ctx (Select sl fr wh Nothing True)
>                           where err = "only support single group by with single aggregation at the end of SELECT list"
>                                 noOnAgg (Proj (Agg _ _) _) = Left err
>                                 noOnAgg other = Right other
>                                 lastField = last sl
>                                 initFields = init sl
>                         UnionAll q1 q2 ->
>                              HSUnionAll <$>
>                              toHSQuery env ctx q1 <*> (toHSQuery env ctx q2)

> cosToHS :: HSEnv -> HSContext -> QueryExpr -> Either String HSQueryExpr
> cosToHS env ctx q = do q1 <- elimStar env ctx q
>                        q2 <- toHSQuery env ctx q1
>                        return q2

convert HoTTSQL AST to string (Coq program)

> class Coqable a where
>   toCoq :: a -> String

delimit strings with space

> uw :: [String] -> String
> uw = unwords

dedup list (this does not preserve the order)

> dedup :: Ord a => [a] -> [a]
> dedup = toList . fromList

add a prefix to schema name to avoid naming confliction.

> prefixScm :: String -> String
> prefixScm s = "scm_" ++ s

add a prefix to relation name to avoid naming confliction.

> prefixRel :: String -> String
> prefixRel r = "rel_" ++ r

add a prefix to predicate name to avoid naming confliction.

> prefixPred :: String -> String
> prefixPred p = "pred_" ++ p

> instance Coqable HSValueExpr where
>   toCoq (HSDIden t a) = addParen $ uw ["variable", addParen $ t ++ "⋅" ++ a]
>   toCoq (HSBinOp v1 op v2) = addParen $ uw [op', toCoq v1, toCoq v2]
>     where op' = case lookup op binOps of
>                   Just o -> o
>                   Nothing -> "ERROR: do not support " ++ " op."             
>   toCoq (HSConstant c) = addParen $ uw ["constantExpr", c]
>   toCoq (HSAggVQE f q) = addParen $ uw ["aggregate", f, toCoq q]

convert valueExpr to projection strings.

> veToProj :: HSValueExpr -> String
> veToProj (HSDIden t a) = addParen $ t ++ "⋅" ++ a
> veToProj v = addParen $ uw ["e2p", toCoq v]

> instance Coqable HSPredicate where
>   toCoq HSTrue = "true"
>   toCoq HSFalse = "false"
>   toCoq (HSPredVar v sl) = addParen $ uw ["castPred (combine left",
>                                          (f sl) ++ ")", prefixPred v]
>     where f [x] = addParen $ x
>           f (t:h) = addParen $ uw ["combine", addParen t, f h]
>           f [] = "ERROR"
>   toCoq (HSAnd b1 b2) = addParen $ uw ["and", toCoq b1, toCoq b2]
>   toCoq (HSOr b1 b2) = addParen $ uw ["or", toCoq b1, toCoq b2]
>   toCoq (HSNot b) = addParen $ uw ["negate", toCoq b]
>   toCoq (HSExists q) = addParen $ uw ["EXISTS", toCoq q]
>   toCoq (HSEq v1 v2) = addParen $ uw ["equal", toCoq v1, toCoq v2]
>   toCoq (HSGt v1 v2) =
>     addParen $ uw ["castPred (combine", veToProj v1, veToProj v2, ") gt"]
>   toCoq (HSLt v1 v2) =
>     addParen $ uw ["castPred (combine", veToProj v2, veToProj v1, ") gt"]


> instance Coqable HSTableRef where
>   toCoq (HSTRBase x) = addParen $ uw ["table", prefixRel x]
>   toCoq (HSTRQuery q) = addParen $ toCoq q
>   toCoq HSUnitTable = "unit"
>   toCoq (HSProduct t1 t2) = addParen $ uw ["product", toCoq t1, toCoq t2]
>   toCoq (HSTableUnion t1 t2) = addParen $ uw [toCoq t1, "UNION ALL", toCoq t2]

> instance Coqable HSSelectItem where
>   toCoq HSStar = "*"
>   toCoq (HSDStar x) = addParen $ (x ++ "⋅star")
>   toCoq (HSProj v) = veToProj v

> instance Coqable HSQueryExpr where
>   toCoq (HSUnionAll q1 q2) = (addParen $ toCoq q1) ++ " UNION ALL " ++
>                              (addParen $ toCoq q2)
>   toCoq (HSSelect sl fr wh [] di) =             -- if there is no group by
>     p ++ (addParen $ uw [ genSel sl, "FROM1", toCoq fr, w])
>     where genSel [HSStar] = "SELECT *"
>           genSel sl = "SELECT1 " ++ (f sl)
>           f [x] = toCoq x
>           f (h:t) = addParen $ uw ["combine", toCoq h, f t]
>           p = if di then "DISTINCT " else ""
>           w = if (wh == HSTrue)
>               then ""
>               else "WHERE " ++ (toCoq wh)
>   toCoq (HSSelect sl fr wh gr di) =            -- if group by is not empty
>     p ++ (addParen $ uw ["SELECT ", f sl, "FROM1 ", toCoq fr, w, "GROUP BY ", f' gr])
>     where p = if di then "DISTINCT " else "" 
>           -- always valid here, replace * in COUNT(*) with right
>           -- the pattern matching is intended to be imcomplete,
>           -- last field can only AGG
>           f [HSProj (HSAgg af HSVStar)] = (map toUpper af) ++ (addParen $ "right") 
>           f [HSProj (HSAgg af ve)] =  (map toUpper af) ++ (addParen $ toCoq ve) 
>           f (h:t) = addParen $ uw ["combine'", "PLAIN" ++ (addParen $ uw ["variable", toCoq h]), f t]
>           w = if (wh == HSTrue)
>               then ""
>               else "WHERE " ++ (toCoq wh)
>           f' [x] = veToProj x
>           f' (h:t) = addParen $ uw ["combine", veToProj h, f' t]

from Cosette statements to Coq program (or Error message)

> genCoq :: [CosetteStmt] -> Either String String
> genCoq sts = genCoq' [] [] [] [] [] sts

The actual working horse:
Table-Schema map, constant list, predicate list, schema list, query list,
statement list

> genCoq' :: [(String, String)] -> [(String, String)]-> [(String, [String])] -> [HSSchema] -> [(String, QueryExpr)] -> [CosetteStmt] -> Either String String
> genCoq' tsl cl pl sl ql (h:t) =
>   case h of
>     Schema sn sl' -> genCoq' tsl cl pl (MakeHSSchema sn sl':sl) ql t
>     Table tn sn -> genCoq' ((tn, sn):tsl) cl pl sl ql t  
>     Pred pn sn -> genCoq' tsl cl ((pn, sn):pl) sl ql t
>     Const cn tn -> genCoq' tsl ((cn, tn):cl) pl sl ql t
>     Query qn q -> genCoq' tsl cl pl sl ((qn, q): ql) t
>     Verify q1 q2 -> genTheorem tsl cl pl sl ql q1 q2
> genCoq' tsl cl pl sl ql _ = Left "Cannot find verify statement."

assemble the theorem definition.

> genTheorem :: [(String, String)] -> [(String, String)]-> [(String, [String])] -> [HSSchema] -> [(String, QueryExpr)] -> String -> String -> Either String String
> genTheorem tsl cl pl sl ql q1 q2 =
>   do qe1 <- findQ q1 ql
>      qe2 <- findQ q2 ql
>      nl1 <- Right $ getNumberLiterals qe1
>      nl2 <- Right $ getNumberLiterals qe2
>      env <- Right $ MakeHSEnv tsl sl
>      hsq1 <- cosToHS env HSEmpty qe1
>      hsq2 <- cosToHS env HSEmpty qe2
>      qs1 <- Right (toCoq hsq1)
>      qs2 <- Right (toCoq hsq2)
>      vs <- Right (verifyDecs qs1 qs2)
>      return ((joinWithBr headers) ++ (constDecs (nl1++nl2)) ++ openDef ++ decs ++ vs ++ endDef ++ (genProof tactics) ++ ending)
>   where
>     findQ q' ql' = case lookup q' ql' of
>                      Just qe -> Right qe
>                      Nothing -> Left ("Cannot find " ++ q' ++ ".")
>     snames = unwords $ map (prefixScm . hsSName) sl
>     tables = unwords $ map (\t -> "(" ++ (prefixRel (fst t)) ++ ": relation "
>                                    ++ (prefixScm (snd t)) ++ ")") tsl
>     scms = "( Γ " ++ snames ++ ": Schema) "
>     tbls = tables ++ " "
>     attrs = unwords $ map attrDecs sl
>     preds = unwords $ map predDecs pl
>     decs = addRefine $ "forall " ++ scms ++ tbls ++ attrs ++ preds ++ ", _"
>     constDecs consts = (joinWithBr $ map (\a -> "  Variable " ++ (intToConst a) ++ ": constant int.") (dedup consts)) ++ "\n" 

extract data types that are needed. e.g. schema s(a:t1, b:t2, c:t1, ??) -> [t1, t2] 

> getDataTypes :: [HSSchema] -> [String]
> getDataTypes sl = filter (\a -> a /= "type") (dedup sl')
>   where sl' = foldr (\l s -> s ++ (snd <$> hsAttrs l)) [] sl

generate verify declaration string

> verifyDecs :: String -> String -> String
> verifyDecs q1 q2 = addRefine $ "⟦ Γ ⊢ " ++ q1 ++ " : _ ⟧ =  ⟦ Γ ⊢ " ++ q2 ++ " : _ ⟧" 

generate attribute (column) declarations from schemas, TODO: everything is int for now.

> attrDecs :: HSSchema -> String
> attrDecs s = unwords $
>   map genAttr attrs
>   where sn = hsSName s
>         attrs = hsAttrs s
>         genAttr t = if (fst t) == "unknowns"
>                     then ""
>                     else "(" ++ sn ++ "_" ++ (fst t) ++ " : Column int " ++ (prefixScm sn) ++ ")"

generate predicate declarations

> predDecs :: (String, [String]) -> String
> predDecs t = "(" ++ (prefixPred (fst t)) ++ " : Pred (Γ++" ++ "" ++
>               scms ++ "))"
>   where scms = foldr (\a b -> if b == "" then prefixScm a
>                               else (prefixScm a) ++ "++" ++ (prefixScm b))
>                       "" (snd t)

> headers :: [String]
> headers = ["Require Import HoTT.",
>            "Require Import UnivalenceAxiom.",
>            "Require Import HoTTEx.",
>            "Require Import Denotation.",
>            "Require Import UnivalentSemantics.",
>            "Require Import AutoTactics.",
>            "Require Import CQTactics. \n",
>            "Open Scope type. \n",
>            "Module Optimization (T : Types) (S : Schemas T) (R : Relations T S)  (A : Aggregators T S).",
>            "  Import T S R A.",
>            "  Module SQL_TSRA := SQL T S R A.",
>            "  Import SQL_TSRA.",
>            "  Module AutoTac := AutoTactics T S R A.",
>            "  Import AutoTac.",
>            "  Module CQTac := CQTactics T S R A.",
>            "  Import CQTac. \n",
>            "  Parameter int: type.",
>            "  Parameter add: binary int int int.",
>            "  Parameter minus: binary int int int. \n",
>            "  Notation combine' := combineGroupByProj.\n",
>            "  Parameter count : forall {T}, aggregator T int.",
>            "  Notation \"'COUNT' ( e )\" := (aggregatorGroupByProj count e). \n",
>            "  Parameter gt: Pred (node (leaf int) (leaf int)). \n"]

> openDef :: String
> openDef = "  Definition Rule: Type. \n"

> addRefine :: String -> String
> addRefine s = "    refine (" ++ s ++ "). \n"

> endDef :: String
> endDef = "  Defined. \n"

generate proof given a tactics

> genProof :: [String] -> String
> genProof tac = "  Arguments Rule /. \n \n  Lemma ruleStand: Rule. \n" ++ "    start;\n" ++ (f tac) ++ "  Qed. \n "
>   where f x = "    first [" ++ (intercalate "| " x) ++ "]. \n"

> tactics :: [String]
> tactics = ["sum_heuristic1",
>            "prod_heuristic1",
>            "deductive_proof'",
>            "conjunctiveQueryProof'",
>            "hott_ring'"]

> ending :: String
> ending = "\nEnd Optimization. \n"

