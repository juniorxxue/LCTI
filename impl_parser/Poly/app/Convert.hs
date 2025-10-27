module Convert where

import qualified Syntax as S
import qualified AST as P

import Data.List (elemIndex)

-- environment : choose : forall a. a -> a, id : forall a. a -> a, a, b
-- (choose id) @a @b ===> (1 0) @1 @0

-- Helper function to find the index of a type variable in the environment
-- Only counts type variables (EUvar entries)
findTypeVarIndex :: String -> P.NamedEnv -> Maybe Int
findTypeVarIndex _ P.EEmpty = Nothing
findTypeVarIndex name (P.EUvar x env)
  | name == x = Just 0
  | otherwise = fmap (+1) (findTypeVarIndex name env)
findTypeVarIndex name (P.ETrm _ _ env) = findTypeVarIndex name env
findTypeVarIndex name (P.EEvar _ env) = findTypeVarIndex name env
findTypeVarIndex name (P.ESvar _ _ env) = findTypeVarIndex name env

-- Helper function to find the index of a term variable in the environment
-- Only counts term variables (ETrm entries)
findTermVarIndex :: String -> P.NamedEnv -> Maybe Int
findTermVarIndex _ P.EEmpty = Nothing
findTermVarIndex name (P.ETrm x _ env)
  | name == x = Just 0
  | otherwise = fmap (+1) (findTermVarIndex name env)
findTermVarIndex name (P.EUvar _ env) = findTermVarIndex name env
findTermVarIndex name (P.EEvar _ env) = findTermVarIndex name env
findTermVarIndex name (P.ESvar _ _ env) = findTermVarIndex name env

-- Convert a named type to a de Bruijn indexed type
convertNamedTyp :: P.NamedEnv -> P.NamedTyp -> S.Typ
convertNamedTyp env P.TInt = S.TInt
convertNamedTyp env P.TBool = S.TBool
convertNamedTyp env (P.TVar name) = 
  case findTypeVarIndex name env of
    Just i -> S.TVar i
    Nothing -> error $ "Unbound type variable: " ++ name
convertNamedTyp env (P.TArr t1 t2) = 
  S.TArr (convertNamedTyp env t1) (convertNamedTyp env t2)
convertNamedTyp env (P.TForall name t) = 
  S.TForall (convertNamedTyp (P.EUvar name env) t)
convertNamedTyp env (P.TUncurry ts t) = 
  S.TUncurry (map (convertNamedTyp env) ts) (convertNamedTyp env t)
convertNamedTyp env (P.TList t) = 
  S.TList (convertNamedTyp env t)
convertNamedTyp env (P.TProd t1 t2) = 
  S.TProd (convertNamedTyp env t1) (convertNamedTyp env t2)
convertNamedTyp env (P.TST t1 t2) = 
  S.TST (convertNamedTyp env t1) (convertNamedTyp env t2)

-- Convert a named term to a de Bruijn indexed term
convertNamedTerm :: P.NamedEnv -> P.NamedTerm -> S.Trm
convertNamedTerm env (P.LitInt n) = S.LitInt n
convertNamedTerm env (P.LitBool b) = S.LitBool b
convertNamedTerm env (P.Var name) = 
  case findTermVarIndex name env of
    Just i -> S.Var i
    Nothing -> error $ "Unbound variable: " ++ name
convertNamedTerm env (P.Abs name body) = 
  S.Abs (convertNamedTerm (P.ETrm name (P.TVar "_dummy") env) body)
convertNamedTerm env (P.AbsAnn name ty body) = 
  S.AbsAnn (convertNamedTyp env ty) (convertNamedTerm (P.ETrm name ty env) body)
convertNamedTerm env (P.AbsUncurry names body) = 
  let n = length names
      env' = foldr (\name acc -> P.ETrm name (P.TVar "_dummy") acc) env (reverse names)
  in S.AbsUncurry n (convertNamedTerm env' body)
convertNamedTerm env (P.AbsUncurryAnn bindings body) = 
  let (names, types) = unzip bindings
      convertedTypes = map (convertNamedTyp env) types
      env' = foldr (\(name, ty) acc -> P.ETrm name ty acc) env (reverse bindings)
  in S.AbsUncurryAnn convertedTypes (convertNamedTerm env' body)
convertNamedTerm env (P.App e1 e2) = 
  S.App (convertNamedTerm env e1) (convertNamedTerm env e2)
convertNamedTerm env (P.AppUncurry e es) = 
  S.AppUncurry (convertNamedTerm env e) (map (convertNamedTerm env) es)
convertNamedTerm env (P.Ann e ty) = 
  S.Ann (convertNamedTerm env e) (convertNamedTyp env ty)
convertNamedTerm env (P.TAbs name body) = 
  S.TAbs (convertNamedTerm (P.EUvar name env) body)
convertNamedTerm env (P.TApp e ty) = 
  S.TApp (convertNamedTerm env e) (convertNamedTyp env ty)
convertNamedTerm env P.Nil = S.Nil
convertNamedTerm env P.Cons = S.Cons
convertNamedTerm env (P.Pair e1 e2) = 
  S.Pair (convertNamedTerm env e1) (convertNamedTerm env e2)
convertNamedTerm env (P.Fst e) = 
  S.Fst (convertNamedTerm env e)
convertNamedTerm env (P.Snd e) = 
  S.Snd (convertNamedTerm env e)

convertNamedEnv :: P.NamedEnv -> S.Env
convertNamedEnv P.EEmpty = S.EEmpty
convertNamedEnv (P.ETrm name ty env) = 
  S.ETrm (convertNamedTyp env ty) (convertNamedEnv env)
convertNamedEnv (P.EUvar name env) = 
  S.EUvar (convertNamedEnv env)
convertNamedEnv (P.EEvar name env) = 
  S.EEvar (convertNamedEnv env)
convertNamedEnv (P.ESvar name ty env) = 
  S.ESvar (convertNamedTyp env ty) (convertNamedEnv env)  