module Convert where

import qualified Syntax as S
import qualified Parser as P
import Data.List (elemIndex)

convertNamedTyp :: P.NamedTyp -> S.Typ

convertNamedTerm :: P.NamedTerm -> S.Trm

-- Helpers for type conversion with a type-variable environment
convertNamedTyp = convertTyp []

convertTyp :: [String] -> P.NamedTyp -> S.Typ
convertTyp _ P.TInt = S.TInt
convertTyp _ P.TBool = S.TBool
convertTyp tyEnv (P.TVar a) =
  case elemIndex a tyEnv of
    Just ix -> S.TVar ix
    Nothing -> error ("Unbound type variable: " ++ a)
convertTyp tyEnv (P.TArr t1 t2) = S.TArr (convertTyp tyEnv t1) (convertTyp tyEnv t2)
convertTyp tyEnv (P.TForall a t) = S.TForall (convertTyp (a : tyEnv) t)
convertTyp tyEnv (P.TUncurry ts t) = S.TUncurry (map (convertTyp tyEnv) ts) (convertTyp tyEnv t)
convertTyp tyEnv (P.TList t) = S.TList (convertTyp tyEnv t)
convertTyp tyEnv (P.TProd t1 t2) = S.TProd (convertTyp tyEnv t1) (convertTyp tyEnv t2)
convertTyp tyEnv (P.TST t1 t2) = S.TST (convertTyp tyEnv t1) (convertTyp tyEnv t2)

-- Helpers for term conversion with term and type environments
convertNamedTerm = fst . convertTermT [] []

-- Type env here carries innermost-first binders, optionally named
type TyEnv = [Maybe String]

convertTermT :: [String] -> TyEnv -> P.NamedTerm -> (S.Trm, TyEnv)
convertTermT _ tyEnv (P.LitInt i) = (S.LitInt i, tyEnv)
convertTermT _ tyEnv (P.LitBool b) = (S.LitBool b, tyEnv)
convertTermT trmEnv tyEnv (P.Var x) =
  ( case elemIndex x trmEnv of
      Just ix -> S.Var ix
      Nothing -> error ("Unbound term variable: " ++ x)
  , tyEnv)
convertTermT trmEnv tyEnv (P.Abs x e) =
  let (e', tyEnv') = convertTermT (x : trmEnv) tyEnv e in (S.Abs e', tyEnv')
convertTermT trmEnv tyEnv (P.AbsAnn ty e) =
  let (ty', tyEnv1) = convertTypWith tyEnv ty
      (e', tyEnv2) = convertTermT (anon : trmEnv) tyEnv1 e
  in (S.AbsAnn ty' e', tyEnv2)
  where
    anon = ","
convertTermT trmEnv tyEnv (P.AbsUncurry names e) =
  let ns = splitCommas names
      n = length ns
      trmEnv' = reverse ns ++ trmEnv
      (e', tyEnv') = convertTermT trmEnv' tyEnv e
  in (S.AbsUncurry n e', tyEnv')
convertTermT trmEnv tyEnv (P.AbsUncurryAnn tys e) =
  let (tys', tyEnv1) = convertTyListWith tyEnv tys
      trmEnv' = replicate (length tys) "," ++ trmEnv
      (e', tyEnv2) = convertTermT trmEnv' tyEnv1 e
  in (S.AbsUncurryAnn tys' e', tyEnv2)
convertTermT trmEnv tyEnv (P.App e1 e2) =
  let (e1', tyEnv1) = convertTermT trmEnv tyEnv e1
      (e2', tyEnv2) = convertTermT trmEnv tyEnv1 e2
  in (S.App e1' e2', tyEnv2)
convertTermT trmEnv tyEnv (P.AppUncurry e es) =
  let (e', tyEnv1) = convertTermT trmEnv tyEnv e
      (es', tyEnv2) = convertTerms trmEnv tyEnv1 es
  in (S.AppUncurry e' es', tyEnv2)
convertTermT trmEnv tyEnv (P.Ann e ty) =
  let (e', tyEnv1) = convertTermT trmEnv tyEnv e
      (ty', tyEnv2) = convertTypWith tyEnv1 ty
  in (S.Ann e' ty', tyEnv2)
convertTermT trmEnv tyEnv (P.TAbs e) =
  let (e', tyEnvBody) = convertTermT trmEnv (Nothing : tyEnv) e
  in case tyEnvBody of
       (_:rest) -> (S.TAbs e', rest)
       [] -> (S.TAbs e', [])
convertTermT trmEnv tyEnv (P.TApp e ty) =
  let (e', tyEnv1) = convertTermT trmEnv tyEnv e
      (ty', tyEnv2) = convertTypWith tyEnv1 ty
  in (S.TApp e' ty', tyEnv2)
convertTermT _ tyEnv P.Nil = (S.Nil, tyEnv)
convertTermT _ tyEnv P.Cons = (S.Cons, tyEnv)
convertTermT trmEnv tyEnv (P.Pair e1 e2) =
  let (e1', tyEnv1) = convertTermT trmEnv tyEnv e1
      (e2', tyEnv2) = convertTermT trmEnv tyEnv1 e2
  in (S.Pair e1' e2', tyEnv2)
convertTermT trmEnv tyEnv (P.Fst e) =
  let (e', tyEnv') = convertTermT trmEnv tyEnv e in (S.Fst e', tyEnv')
convertTermT trmEnv tyEnv (P.Snd e) =
  let (e', tyEnv') = convertTermT trmEnv tyEnv e in (S.Snd e', tyEnv')

convertTerms :: [String] -> TyEnv -> [P.NamedTerm] -> ([S.Trm], TyEnv)
convertTerms _ tyEnv [] = ([], tyEnv)
convertTerms trmEnv tyEnv (t:ts) =
  let (t', tyEnv1) = convertTermT trmEnv tyEnv t
      (ts', tyEnv2) = convertTerms trmEnv tyEnv1 ts
  in (t' : ts', tyEnv2)

convertTyListWith :: TyEnv -> [P.NamedTyp] -> ([S.Typ], TyEnv)
convertTyListWith tyEnv [] = ([], tyEnv)
convertTyListWith tyEnv (t:ts) =
  let (t', tyEnv1) = convertTypWith tyEnv t
      (ts', tyEnv2) = convertTyListWith tyEnv1 ts
  in (t' : ts', tyEnv2)

convertTypWith :: TyEnv -> P.NamedTyp -> (S.Typ, TyEnv)
convertTypWith tyEnv P.TInt = (S.TInt, tyEnv)
convertTypWith tyEnv P.TBool = (S.TBool, tyEnv)
convertTypWith tyEnv (P.TVar a) =
  case findIndexName a tyEnv of
    Just ix -> (S.TVar ix, tyEnv)
    Nothing -> case assignToOutermost a tyEnv of
                 Just (ix, tyEnv') -> (S.TVar ix, tyEnv')
                 Nothing -> error ("Unbound type variable: " ++ a)
convertTypWith tyEnv (P.TArr t1 t2) =
  let (t1', tyEnv1) = convertTypWith tyEnv t1
      (t2', tyEnv2) = convertTypWith tyEnv1 t2
  in (S.TArr t1' t2', tyEnv2)
convertTypWith tyEnv (P.TForall a t) =
  let (t', tyEnv') = convertTypWith (Just a : tyEnv) t
  in (S.TForall t', tyEnv')
convertTypWith tyEnv (P.TUncurry ts t) =
  let (ts', tyEnv1) = convertTyListWith tyEnv ts
      (t', tyEnv2) = convertTypWith tyEnv1 t
  in (S.TUncurry ts' t', tyEnv2)
convertTypWith tyEnv (P.TList t) =
  let (t', tyEnv') = convertTypWith tyEnv t in (S.TList t', tyEnv')
convertTypWith tyEnv (P.TProd t1 t2) =
  let (t1', tyEnv1) = convertTypWith tyEnv t1
      (t2', tyEnv2) = convertTypWith tyEnv1 t2
  in (S.TProd t1' t2', tyEnv2)
convertTypWith tyEnv (P.TST t1 t2) =
  let (t1', tyEnv1) = convertTypWith tyEnv t1
      (t2', tyEnv2) = convertTypWith tyEnv1 t2
  in (S.TST t1' t2', tyEnv2)

findIndexName :: String -> TyEnv -> Maybe Int
findIndexName name = go 0
  where
    go _ [] = Nothing
    go i (m:ms) = case m of
      Just n | n == name -> Just i
      _ -> go (i + 1) ms

assignToOutermost :: String -> TyEnv -> Maybe (Int, TyEnv)
assignToOutermost name tyEnv =
  case lastNothingIndex tyEnv of
    Nothing -> Nothing
    Just ix -> Just (ix, setAt ix (Just name) tyEnv)

lastNothingIndex :: TyEnv -> Maybe Int
lastNothingIndex = go 0 Nothing
  where
    go _ acc [] = acc
    go i acc (m:ms) =
      let acc' = case m of
                   Nothing -> Just i
                   _ -> acc
      in go (i + 1) acc' ms

setAt :: Int -> a -> [a] -> [a]
setAt _ _ [] = []
setAt 0 y (_:xs) = y : xs
setAt n y (x:xs) = x : setAt (n - 1) y xs

-- utility: split a comma-separated list with no spaces
splitCommas :: String -> [String]
splitCommas s = go s []
  where
    go [] acc = finish acc
    go (c:cs) acc
      | c == ',' = finish acc ++ go cs []
      | otherwise = go cs (acc ++ [c])
    finish acc = case acc of
      [] -> []
      _  -> [acc]

parseAndConvertTyp :: String -> S.Typ
parseAndConvertTyp s = case P.parseNamedTyp s of
  Left err -> error (show err)
  Right typ -> convertNamedTyp typ

parseAndConvertTerm :: String -> S.Trm
parseAndConvertTerm s = case P.parseNamedTerm s of
  Left err -> error (show err)
  Right term -> convertNamedTerm term