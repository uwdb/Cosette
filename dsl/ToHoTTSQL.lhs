{-# LANGUAGE OverloadedStrings #-}

= Convert Cosette AST to rosette program

> module ToHoTTSQL where

> import CosetteParser
> import Text.Parsec.Error as PE
> import Data.List (unwords, intercalate)
> import FunctionsAndTypesForParsing
> import qualified Data.Map as Map

== HoTTSQL Abstract Syntax

schema

> data HSSchema =  MakeHSSchema {hsSName :: String             -- name of the schema
>                             ,hsAttrs :: [(String, String)] -- name, typename
>                             } deriving (Eq, Show)

environment

> data HSEnv = MakeHSEnv {tables :: [(String, String)]  -- table name, schema name
>                        ,schemas :: [HSSchema]         -- schemas
>                        } deriving (Eq, Show)

context

> data HSContext = HSNode HSContext HSContext
>                | HSLeaf String HSSchema         -- alias schema
>                | HSEmpty
>                  deriving (Eq, Show)

value expression

> data HSValueExpr = HSDIden String String                   -- eg: r.a  
>                  | HSBinOp HSValueExpr String HSValueExpr  -- eg: r.a + r.b
>                  | HSConstant String                       -- constant variable
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


== convert Cosette to HoTTSQL

a utility function

> lkUp :: [a] -> (a -> String -> Bool) -> String -> Either String a
> lkUp [] _ q = Left $ "cannot find " ++ q ++ " in list."
> lkUp (h:t) f q = if f h q then Right h else lkUp t f q

look up schema by table name

> lkUpSchema :: HSEnv -> String -> Either String HSSchema
> lkUpSchema env q = do sn <- lkUp (tables env) (\t q1 -> fst t == q1) q
>                       lkUp (schemas env) (\t q1 -> hsSName t == q1) $ snd sn

get output schema

> getFromSchema :: HSEnv -> HSContext -> Maybe [TableRef] -> Either String [(String, String)]
> getFromSchema env ctx Nothing = Right []
> getFromSchema env ctx (Just []) = Right []
> getFromSchema env ctx (Just (h:t)) =  (++) <$> getScm env (getTe h) <*> getFromSchema env ctx (Just t)
>   where getScm env (TRBase tn) = hsAttrs <$> lkUpSchema env tn
>         getScm env (TRQuery q) = getOutput env ctx q
>         getScm env (TRUnion t1 t2) = getScm env t1

look up a schema in FROM clause by alias

> lkUpSchemaInFrom :: HSEnv -> HSContext -> Maybe [TableRef] -> String -> Either String [(String, String)]
> lkUpSchemaInFrom env ctx Nothing a = Left $ "cannot find " ++ a
> lkUpSchemaInFrom env ctx (Just []) a = Left $ "cannot find " ++ a
> lkUPSchemaInFrom env ctx (Just (h:t)) a =
>   if scm h == a
>   then lkUpSchemaInTe (getTe h)
>   else lkUpSchemaInFrom env ctx (Just t) a
>   where scm (TR _ al) = al
>         lkUpSchemaInTe (TRBase tn) = hsAttrs <$> lkUpSchema env tn
>         lkUpSchemaInTe (TRQuery q) = getOutput env ctx q
>         lkUpSchemaInTe (TRUnion t1 _) = lkUpSchemaInTe t1

get output schema of a query

> getOutput :: HSEnv -> HSContext -> QueryExpr -> Either String [(String, String)]
> getOutput env ctx q = f (qSelectList q)
>   where f [Star] = getFromSchema env ctx (qFrom q)
>         f (h:t) = case h of DStar al -> (++) <$> (lkUpSchemaInFrom env ctx (qFrom q) al)
>                                              <*> f t
>                             Proj e al -> do ctx' <- getCtx env ctx (qFrom q)
>                                             ty <- getType env (HSNode ctx ctx') e
>                                             rest <- f t
>                                             return ((al,ty):rest) 
>                             _ -> Left "error."
>         f [] = Right []

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

generate context from FROM clause

> getCtxNode :: HSEnv -> HSContext -> TableRef -> Either String HSContext
> getCtxNode env ctx (TR tr al) = gcn tr
>   where gcn (TRBase tn) = HSLeaf al <$> lkUpSchema env tn
>         gcn (TRQuery q) = do at <- getOutput env ctx q
>                              return (HSLeaf al (MakeHSSchema al at))
>         gcn (TRUnion t1 t2) = gcn t1

> getCtx :: HSEnv -> HSContext -> Maybe [TableRef] -> Either String HSContext
> getCtx env ctx Nothing = Right HSEmpty
> getCtx env ctx (Just []) = Right HSEmpty
> getCtx env ctx (Just [x]) = getCtxNode env ctx x
> getCtx env ctx (Just (h:t)) = HSNode <$> getCtxNode env ctx h
>                                      <*> getCtx env ctx (Just t)

convert alias to path, and get its schema 
it returns (path, schema) or nothing

> nameToPath' :: HSContext -> String -> Maybe ([String], HSSchema)
> nameToPath' HSEmpty _ = Nothing
> nameToPath' (HSNode lt rt) s =
>   case nameToPath' rt s of Nothing -> do t <- nameToPath' lt s
>                                          return ("left":(fst t), snd t)
>                            Just t -> Just ("right":(fst t), snd t) 
> nameToPath' (HSLeaf al sch) s = if al == s then Just ([], sch) else Nothing

wrap it in Either

> nameToPath :: HSContext -> String -> Either String (String, HSSchema)
> nameToPath ctx s = case nameToPath' ctx s of
>                      Nothing -> Left ("cannot find alias " ++ s)
>                      Just x -> Right (intercalate "⋅" (fst x), snd x)

convert Cosette value expression to HoTTSQL expression

> fstInList :: (Eq a) => [(a, b)] -> a -> Bool
> fstInList [] a = False
> fstInList (h:t) a = if fst h == a then True else fstInList t a

> convertVE :: HSContext -> ValueExpr -> Either String HSValueExpr
> convertVE ctx (NumLit i) = Left "do not support concrete number now."
> convertVE ctx (DIden tr attr) = do t <- nameToPath ctx tr
>                                    if fstInList (hsAttrs (snd t)) attr
>                                    then return (HSDIden (fst t) attr)
>                                    else Left ("attribute " ++ attr ++ " is not valid")
> convertVE ctx (BinOp v1 op v2) = HSBinOp <$> convertVE ctx v1
>                                          <*> Right op
>                                          <*> convertVE ctx v2
> convertVE ctx (Constant c) = Right (HSConstant c)

convert Cosette predicate to HoTTSQL predicate

> convertPred :: HSEnv -> HSContext -> Predicate -> Either String HSPredicate
> convertPred env ctx TRUE = Right HSTrue
> convertPred env ctx FALSE = Right HSFalse
> convertPred env ctx (PredVar b s) = HSPredVar <$> Right b
>                                     <*> checkListErr (f <$> s)
>   where f a = fst <$> nameToPath ctx a
> convertPred env ctx (And b1 b2) = HSAnd <$> convertPred env ctx b1
>                                         <*> convertPred env ctx b2
> convertPred env ctx (Or b1 b2) = HSOr <$> convertPred env ctx b1
>                                       <*> convertPred env ctx b2
> convertPred env ctx (Not b) = HSNot <$> convertPred env ctx b
> convertPred env ctx (Exists q) = HSExists <$> toHSQuery env ctx q
> convertPred env ctx (Veq v1 v2) = HSEq <$> convertVE ctx v1
>                                        <*> convertVE ctx v2
> convertPred env ctx (Vgt v1 v2) = HSGt <$> convertVE ctx v1
>                                        <*> convertVE ctx v2
> convertPred env ctx (Vlt v1 v2) = HSLt <$> convertVE ctx v1
>                                        <*> convertVE ctx v2

convert Select

> convertSelect :: HSContext -> [SelectItem] -> Either String [HSSelectItem]
> convertSelect ctx l = checkListErr (f <$> l)
>   where f Star = Right HSStar
>         f (DStar x) = HSDStar <$> (fst <$> nameToPath ctx x)
>         f (Proj v _) = HSProj <$> convertVE ctx v

convert where

> convertWhere :: HSEnv -> HSContext -> Maybe Predicate -> Either String HSPredicate
> convertWhere env ctx Nothing = Right HSTrue
> convertWhere env ctx (Just p) = convertPred env ctx p

> convertGroup :: HSContext -> Maybe [ValueExpr] -> Either String [HSValueExpr]
> convertGroup ctx Nothing = Right []
> convertGroup ctx (Just g) = checkListErr $ (convertVE ctx <$> g)

convert Cosette AST to HoTTSQL AST 

> toHSQuery :: HSEnv -> HSContext -> QueryExpr -> Either String HSQueryExpr
> toHSQuery env ctx q = case q of
>                         Select sl fr wh gr ds ->
>                           do ctx' <- getCtx env ctx fr
>                              ft' <- convertFrom env ctx fr
>                              sl' <- convertSelect (HSNode ctx ctx') sl
>                              wh' <- convertWhere env (HSNode ctx ctx') wh
>                              gr' <- convertGroup (HSNode ctx ctx') gr
>                              return (HSSelect sl' ft' wh' gr' ds)
>                         UnionAll q1 q2 ->
>                              HSUnionAll <$>
>                              toHSQuery env ctx q1 <*>(toHSQuery env ctx q2)

convert HoTTSQL AST to string (Coq program)

> class Coqable a where
>   toCoq :: a -> String

delimit strings with space

> uw :: [String] -> String
> uw = unwords

> instance Coqable HSValueExpr where
>   toCoq (HSDIden t a) = addParen $ uw ["variable", addParen $ t ++ "⋅" ++ a]
>   toCoq (HSBinOp v1 op v2) = addParen $ uw [op, toCoq v1, toCoq v2]
>   toCoq (HSConstant c) = addParen $ uw ["constantExpr", c]

> instance Coqable HSPredicate where
>   toCoq HSTrue = "true"
>   toCoq HSFalse = "false"
>   toCoq (HSPredVar v sl) = addParen $ uw ["castPred (combine left",
>                                          (f sl) ++ ")", v]
>     where f [x] = addParen $ x
>           f (t:h) = addParen $ uw ["combine", addParen $ t, f h]
>           f [] = "ERROR"
>   toCoq (HSAnd b1 b2) = addParen $ uw ["and", toCoq b1, toCoq b2]
>   toCoq (HSOr b1 b2) = addParen $ uw ["or", toCoq b1, toCoq b2]
>   toCoq (HSNot b) = addParen $ uw ["negate", toCoq b]
>   toCoq (HSExists q) = addParen $ uw ["EXISTS", toCoq q]
>   toCoq (HSEq v1 v2) = addParen $ uw ["equal", toCoq v1, toCoq v2]
>   toCoq (HSGt v1 v2) = addParen $ uw ["gt", toCoq v1, toCoq v2]
>   toCoq (HSLt v1 v2) = addParen $ uw ["lt", toCoq v2, toCoq v2]

> instance Coqable HSTableRef where
>   toCoq (HSTRBase x) = addParen $ uw ["table", x]
>   toCoq (HSTRQuery q) = addParen $ toCoq q
>   toCoq HSUnitTable = "unit"
>   toCoq (HSProduct t1 t2) = addParen $ uw ["product", toCoq t1, toCoq t2]
>   toCoq (HSTableUnion t1 t2) = addParen $ uw [toCoq t1, "UNION ALL", toCoq t2]

> instance Coqable HSSelectItem where
>   toCoq HSStar = "*"
>   toCoq (HSDStar x) = x ++ "⋅*"
>   toCoq (HSProj v) = toCoq v

> instance Coqable HSQueryExpr where
>   toCoq (HSUnionAll q1 q2) = (addParen $ toCoq q1) ++ " UNION ALL " ++
>                              (addParen $ toCoq q2)
>   toCoq q = p ++ (addParen $ uw ["SELECT", f $ hsSelectList q,
>                                  "FROM1", toCoq $ hsFrom q,
>                                  "WHERE", toCoq $ hsWhere q])
>     where f [x] = toCoq x
>           f (h:t) = addParen $ uw ["combine", toCoq h, f t]
>           p = if (hsDistinct q)
>               then "DISTINCT "
>               else ""


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
>   let env = MakeHSEnv tsl sl in
>     do qe1 <- findQ q1 ql
>        qe2 <- findQ q2 ql
>        hsq1 <- toHSQuery env HSEmpty qe1 
>        hsq2 <- toHSQuery env HSEmpty qe2
>        qs1 <- Right (toCoq hsq1)
>        qs2 <- Right (toCoq hsq2)
>        vs <- Right (verifyDecs qs1 qs2)
>        return ((joinWithBr headers) ++ openDef ++ decs ++ vs ++ endDef ++ (genProof $ joinWithBr tactics) ++ ending)
>   where
>     findQ q' ql' = case lookup q' ql' of
>                      Just qe -> Right qe
>                      Nothing -> Left ("Cannot find " ++ q' ++ ".")
>     snames = unwords $ map hsSName sl
>     tables = unwords $ map (\t -> "(" ++ (fst t) ++ " : relation " ++ (snd t) ++ ")") tsl
>     scms = "( Γ " ++ snames ++ " : Schema) "
>     tbls = tables ++ " "
>     attrs = unwords $ map attrDecs sl
>     preds = unwords $ map predDecs pl
>     decs = addRefine $ "forall " ++ scms ++ tbls ++ attrs ++ preds ++ ", _"

generate verify declaration string

> verifyDecs :: String -> String -> String
> verifyDecs q1 q2 = addRefine $ "⟦ Γ ⊢ " ++ q1 ++ " : _ ⟧ =  ⟦ Γ ⊢ " ++ q2 ++ " : _ ⟧" 

generate attribute (column) declarations from schemas

> attrDecs :: HSSchema -> String
> attrDecs s = unwords $
>   map genAttr attrs
>   where sn = hsSName s
>         attrs = hsAttrs s
>         genAttr t = if (fst t) == "unkowns"
>                     then ""
>                     else "(" ++ (fst t) ++ " : Column " ++ (snd t) ++ " " ++ sn ++ ")"

generate predicate declarations

> predDecs :: (String, [String]) -> String
> predDecs t = "(" ++ (fst t) ++ " : Pred (Γ++" ++ "" ++ scms ++ "))"
>   where scms = foldr (\a b -> if b == "" then a else a ++ "++" ++ b) "" (snd t)

> joinWithBr :: [String] -> String
> joinWithBr = foldr (\a b -> if a == "" then b else a ++ " \n" ++ b) "" 

> headers :: [String]
> headers = ["Require Import HoTT.",
>            "Require Import UnivalenceAxiom.",
>            "Require Import HoTTEx.",
>            "Require Import Denotation.",
>            "Require Import UnivalentSemantics.",
>            "Require Import AutoTactics. \n",
>            "Open Scope type. \n",
>            "Module Optimization (T : Types) (S : Schemas T) (R : Relations T S)  (A : Aggregators T S).",
>            "  Import T S R A.",
>            "  Module SQL_TSRA := SQL T S R A.",
>            "  Import SQL_TSRA.",
>            "  Module AutoTac := AutoTactics T S R A.",
>            "  Import AutoTac. \n "]

> openDef :: String
> openDef = "  Definition Rule: Type. \n"

> addRefine :: String -> String
> addRefine s = "    refine (" ++ s ++ "). \n"

> endDef :: String
> endDef = "  Defined. \n"

generate proof given a tactics

> genProof :: String -> String
> genProof tac = "Arguments Rule /. \n \n  Lemma ruleStand: Rule. \n  " ++ tac ++ "  Qed. \n "

> tactics :: [String]
> tactics = ["try hott_ring."]

> ending :: String
> ending = "\nEnd Optimization. \n"

