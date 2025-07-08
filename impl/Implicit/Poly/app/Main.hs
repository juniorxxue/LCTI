{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant multi-way if" #-}
{-# HLINT ignore "Use if" #-}
module Main where

import Control.Monad (forM_)
import Control.Monad.Writer
import DeBruijn
import Debug.Trace
import Log
import Syntax
import System.IO (hFlush, stdout)

lookupEnv :: Int -> Env -> WriterT Log Maybe Typ
lookupEnv 0 (ETrm ty _) = do
  tell ["[Lookup] " ++ show ty ++ " in Γ"]
  return ty
lookupEnv k (ETrm _ env) = lookupEnv (k - 1) env
lookupEnv k (EUvar env) = shiftTyp0 <$> lookupEnv k env
lookupEnv k (EEvar env) = shiftTyp0 <$> lookupEnv k env
lookupEnv k (ESvar _ env) = shiftTyp0 <$> lookupEnv k env
lookupEnv _ _ = lift Nothing

findSol :: Env -> Int -> WriterT Log Maybe Typ
findSol a b | trace ("findSol " ++ show a ++ " |- " ++ show b) False = undefined
findSol EEmpty _ = lift Nothing
findSol (ESvar ty _) 0 = return $ shiftTyp0 ty
findSol (ESvar _ senv) k | k > 0 = do
  ty' <- findSol senv (k - 1)
  return $ shiftTyp0 ty'
findSol (EUvar senv) k | k > 0 = do
  ty' <- findSol senv (k - 1)
  return $ shiftTyp0 ty'
findSol (EEvar senv) k | k > 0 = do
  ty' <- findSol senv (k - 1)
  return $ shiftTyp0 ty'
findSol _ _ = lift Nothing

inst :: Env -> Int -> Typ -> Maybe Env
inst env k a | trace ("inst " ++ show env ++ " " ++ show k ++ " " ++ show a) False = undefined
inst (EEvar senv) 0 tyA = Just $ ESvar (unshiftTyp0 tyA) senv
inst (EEvar senv) k tyA | k > 0 = do
  env' <- inst senv (k - 1) (unshiftTyp0 tyA)
  return (EEvar env')
inst (EUvar senv) k tyA | k > 0 = do
  env' <- inst senv (k - 1) (unshiftTyp0 tyA)
  return (EUvar env')
inst (ESvar ty senv) k tyA | k > 0 = do
  env' <- inst senv (k - 1) (unshiftTyp0 tyA)
  return (ESvar ty env')
inst _ _ _ = Nothing

ssubP :: (Env, Env) -> Typ -> Typ -> WriterT Log Maybe Env
ssubP (a1, a2) b c | trace ("ssub " ++ show a1 ++ ";" ++ show a2 ++ " |- " ++ show b ++ " <:+ " ++ show c) False = undefined
ssubP (env, senv) TInt TInt = do
  tell ["[S-Int] " ++ logSSubFull (env, senv) TInt TInt senv]
  return senv
ssubP (env, senv) TBool TBool = do
  tell ["[S-Bool] " ++ logSSubFull (env, senv) TBool TBool senv]
  return senv
ssubP (env, senv) (TVar a) (TVar b) | isUvar (envConcat env senv) a && a == b = do
  tell ["[S-Refl] " ++ logSSubFull (env, senv) (TVar a) (TVar b) senv]
  return senv
ssubP (env, senv) (TVar a) tyA | isEvar senv a = case inst senv a tyA of
  Just newenv -> do
    tell ["[S-Ex-L] " ++ logSSubFull (env, senv) (TVar a) tyA newenv]
    return newenv
  Nothing -> lift Nothing
ssubP (env, senv) (TVar a) tyA = do
  tyB <- findSol senv a
  if tyA == tyB
    then do
      tell ["[S-Sol-L] " ++ logSSubFull (env, senv) (TVar a) tyA senv]
      return senv
    else lift Nothing
ssubP (env, senv) (TArr tyA tyB) (TArr tyC tyD) = do
  (senv1, _log1) <- peek $ ssubN (env, senv) tyC tyA
  (senv2, _log2) <- peek $ ssubP (env, senv1) tyB tyD
  tell ["[S-Arr] " ++ logSSubFull (env, senv) (TArr tyA tyB) (TArr tyC tyD) senv2]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return senv2
ssubP (env, senv) (TForall tyA) (TForall tyB) = do
  (EUvar senv', _log) <- peek $ ssubP (env, EUvar senv) tyA tyB
  tell ["[S-Forall] " ++ logSSubFull (env, senv) (TForall tyA) (TForall tyB) senv']
  tell $ indentAll _log
  return senv'
ssubP (env, senv) (TList tyA) (TList tyB) = do
  (senv', _log) <- peek $ ssubP (env, senv) tyA tyB
  tell ["[S-List] " ++ logSSubFull (env, senv) (TList tyA) (TList tyB) senv']
  tell $ indentAll _log
  return senv'
ssubP (env, senv) (TProd tyA tyB) (TProd tyC tyD) = do
  (senv1, _log1) <- peek $ ssubP (env, senv) tyA tyC
  (senv2, _log2) <- peek $ ssubP (env, senv1) tyB tyD
  tell ["[S-Prod] " ++ logSSubFull (env, senv) (TProd tyA tyB) (TProd tyC tyD) senv2]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return senv2
ssubP (env, senv) (TST tyA tyB) (TST tyC tyD) = do
  (senv1, _log1) <- peek $ ssubP (env, senv) tyA tyC
  (senv2, _log2) <- peek $ ssubN (env, senv1) tyC tyA
  (senv3, _log3) <- peek $ ssubP (env, senv2) tyB tyD
  tell ["[S-ST] " ++ logSSubFull (env, senv) (TST tyA tyB) (TST tyC tyD) senv2]
  tell $ indentAll _log1
  tell $ indentAll _log2
  tell $ indentAll _log3
  return senv3
ssubP _ _ _ = lift Nothing

ssubN :: (Env, Env) -> Typ -> Typ -> WriterT Log Maybe Env
ssubN (a1, a2) b c | trace ("ssub " ++ show a1 ++ ";" ++ show a2 ++ " |- " ++ show b ++ " <:- " ++ show c) False = undefined
ssubN (env, senv) TInt TInt = do
  tell ["[S-Int] " ++ logSSubFull (env, senv) TInt TInt senv]
  return senv
ssubN (env, senv) TBool TBool = do
  tell ["[S-Bool] " ++ logSSubFull (env, senv) TBool TBool senv]
  return senv
ssubN (env, senv) (TVar a) (TVar b) | isUvar (envConcat env senv) a && a == b = do
  tell ["[S-Refl] " ++ logSSubFull (env, senv) (TVar a) (TVar b) senv]
  return senv
ssubN (env, senv) tyA (TVar a) | isEvar senv a = case inst senv a tyA of
  Just newenv -> do
    tell ["[S-Ex-R] " ++ logSSubFull (env, senv) (TVar a) tyA newenv]
    return newenv
  Nothing -> lift Nothing
ssubN (env, senv) tyA (TVar a) = do
  tyB <- findSol senv a
  if tyA == tyB
    then do
      tell ["[S-Sol-R] " ++ logSSubFull (env, senv) tyA (TVar a) senv]
      return senv
    else lift Nothing
ssubN (env, senv) (TArr tyA tyB) (TArr tyC tyD) = do
  (senv1, _log1) <- peek $ ssubP (env, senv) tyC tyA
  (senv2, _log2) <- peek $ ssubN (env, senv1) tyB tyD
  tell ["[S-Arr] " ++ logSSubFull (env, senv) (TArr tyA tyB) (TArr tyC tyD) senv2]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return senv2
ssubN (env, senv) (TForall tyA) (TForall tyB) = do
  (EUvar senv', _log) <- peek $ ssubN (env, EUvar senv) tyA tyB
  tell ["[S-Forall] " ++ logSSubFull (env, senv) (TForall tyA) (TForall tyB) senv']
  tell $ indentAll _log
  return senv'
ssubN (env, senv) (TList tyA) (TList tyB) = do
  (senv', _log) <- peek $ ssubN (env, senv) tyA tyB
  tell ["[S-List] " ++ logSSubFull (env, senv) (TList tyA) (TList tyB) senv']
  tell $ indentAll _log
  return senv'
ssubN (env, senv) (TProd tyA tyB) (TProd tyC tyD) = do
  (senv1, _log1) <- peek $ ssubN (env, senv) tyA tyC
  (senv2, _log2) <- peek $ ssubN (env, senv1) tyB tyD
  tell ["[S-Prod] " ++ logSSubFull (env, senv) (TProd tyA tyB) (TProd tyC tyD) senv2]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return senv2
ssubN (env, senv) (TST tyA tyB) (TST tyC tyD) = do
  (senv1, _log1) <- peek $ ssubN (env, senv) tyA tyC
  (senv2, _log2) <- peek $ ssubP (env, senv1) tyC tyA
  (senv3, _log3) <- peek $ ssubN (env, senv2) tyB tyD
  tell ["[S-ST] " ++ logSSubFull (env, senv) (TST tyA tyB) (TST tyC tyD) senv3]
  tell $ indentAll _log1
  tell $ indentAll _log2
  tell $ indentAll _log3
  return senv3
ssubN _ _ _ = lift Nothing

ground :: Env -> Typ -> WriterT Log Maybe Typ
ground a b | trace ("ground " ++ show a ++ " |- " ++ show b) False = undefined
ground _ TInt = return TInt
ground _ TBool = return TBool
ground env (TVar k) | isUvar env k = return (TVar k)
ground env (TVar k) = findSol env k
ground env (TArr tyA tyB) = do
  tyA' <- ground env tyA
  tyB' <- ground env tyB
  return $ TArr tyA' tyB'
ground env (TForall tyA) = do
  tyA' <- ground (EUvar env) tyA
  return $ TForall tyA'
ground env (TList tyA) = do
  tyA' <- ground env tyA
  return $ TList tyA'
ground env (TProd tyA tyB) = do
  tyA' <- ground env tyA
  tyB' <- ground env tyB
  return $ TProd tyA' tyB'
ground env (TST tyA tyB) = do
  tyA' <- ground env tyA
  tyB' <- ground env tyB
  return $ TST tyA' tyB'

sub :: (Env, Env) -> Typ -> Context -> WriterT Log Maybe (Env, Typ)
sub (a1, a2) b c | trace ("sub " ++ show a1 ++ ";" ++ show a2 ++ " |- " ++ show b ++ " <: " ++ show c) False = undefined
sub (env, senv) tyA CEmpty | closed (envConcat env senv) tyA = do
  grdA <- ground (envConcat env senv) tyA
  tell ["[S-Empty] " ++ logSubFull (env, senv) tyA CEmpty senv grdA]
  return (senv, grdA)
sub (env, senv) tyA (CFullType tyB) = do
  (senv', _log1) <- peek $ ssubP (env, senv) tyA tyB
  tell ["[S-Type] " ++ logSubFull (env, senv) tyA (CFullType tyB) senv' tyB]
  tell $ indentAll _log1
  return (senv', tyB)
sub (env, senv) (TArr tyA tyB) (CTerm e h) | closed (envConcat env senv) tyA = do
  grdA <- ground (envConcat env senv) tyA
  (tyC, _log1) <- peek $ infer (envConcat env senv) (CFullType grdA) e
  ((senv', tyD), _log2) <- peek $ sub (env, senv) tyB h
  tell ["[S-Term-Close] " ++ logSubFull (env, senv) (TArr tyA tyB) (CTerm e h) senv' (TArr tyC tyD)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return (senv', TArr tyC tyD)
sub (env, senv) (TArr tyA tyB) (CTerm e h) | open (envConcat env senv) tyA = do
  (tyC, _log1) <- peek $ infer (envConcat env senv) CEmpty e
  (senv1, _log2) <- peek $ ssubN (env, senv) tyC tyA
  ((senv2, tyD), _log3) <- peek $ sub (env, senv1) tyB h
  tell ["[S-Term-Open] " ++ logSubFull (env, senv) (TArr tyA tyB) (CTerm e h) senv2 (TArr tyC tyD)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  tell $ indentAll _log3
  return (senv2, TArr tyC tyD)
sub (env, senv) (TForall tyA) (CTerm e h) = do
  ((ESvar _ senv', tyB), _log1) <- peek $ sub (env, EEvar senv) tyA (shiftTyContext0 (CTerm e h))
  tell ["[S-Forall-L] " ++ logSubFull (env, senv) (TForall tyA) (CTerm e h) senv' (unshiftTyp0 tyB)]
  tell $ indentAll _log1
  return (senv', unshiftTyp0 tyB)
sub (env, senv) (TForall tyA) (CTApp tyB h) = do
  ((senv', tyC), _log1) <- peek $ sub (env, ESvar tyB senv) tyA (shiftTyContext0 h)
  senv'' <- case senv' of
    ESvar _ senv'' -> return senv''
    EEvar senv'' -> return senv''
    _ -> lift Nothing
  tell ["[S-Forall-TApp] " ++ logSubFull (env, senv) (TForall tyA) (CTApp tyB h) senv'' (TForall tyC)]
  tell $ indentAll _log1
  return (senv'', TForall tyC)
sub (env, senv) (TVar k) (CTerm e h) | isSvar (envConcat env senv) k = do
  tyA <- findSol (envConcat env senv) k
  ((senv', tyBC), _log) <- peek $ sub (env, senv) tyA (CTerm e h)
  tell ["[S-Svar-Term] " ++ logSubFull (env, senv) (TVar k) (CTerm e h) senv' tyBC]
  tell $ indentAll _log
  return (senv', tyBC)
sub (env, senv) (TVar k) (CTApp tyT h) | isSvar (envConcat env senv) k = do
  tyA <- findSol (envConcat env senv) k
  ((senv', tyBC), _log) <- peek $ sub (env, senv) tyA (CTApp tyT h)
  tell ["[S-Svar-TApp] " ++ logSubFull (env, senv) (TVar k) (CTApp tyT h) senv' tyBC]
  tell $ indentAll _log
  return (senv', tyBC)
sub (env, senv) (TVar k) (CTerm e h) | isUvar (envConcat env senv) k = do
  (tyA, _log) <- peek $ infers (envConcat env senv) (CTerm e h)
  case inst senv k tyA of
    Just newenv -> do
      tell ["[S-Infers] " ++ logSubFull (env, senv) (TVar k) (CTerm e h) newenv tyA]
      tell $ indentAll _log
      return (newenv, tyA)
    Nothing -> lift Nothing
sub _ _ _ = lift Nothing

-- TODO: change the name of the rules
infers :: Env -> Context -> WriterT Log Maybe Typ
infers env (CFullType tyA) = do
  tell ["[CI-Type] " ++ logInfersFull env (CFullType tyA) tyA]
  return tyA
infers env (CTerm tm h) = do
  (tyA, _log1) <- peek $ infer env CEmpty tm
  (tyB, _log2) <- peek $ infers env h
  tell ["[CI-Term] " ++ logInfersFull env (CTerm tm h) (TArr tyA tyB)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return $ TArr tyA tyB
infers _ _ = lift Nothing

-- sub (EEmpty, (ESvar TInt EEmpty)) (TArr (TVar 0) (TVar 0)) (CTerm (Lit 42) CEmpty)

infer :: Env -> Context -> Trm -> WriterT Log Maybe Typ
infer a b c | trace ("infer " ++ show a ++ " |- " ++ show b ++ " => " ++ show c) False = undefined
infer env CEmpty (LitInt n) = do
  tell ["[Ty-Int] " ++ logInferFull env CEmpty (LitInt n) TInt]
  return TInt
infer env CEmpty (LitBool b) = do
  tell ["[Ty-Bool] " ++ logInferFull env CEmpty (LitBool b) TBool]
  return TBool
infer env CEmpty (Var i) = do
  (tyA, _log) <- peek $ lookupEnv i env
  tell ["[Ty-Var] " ++ logInferFull env CEmpty (Var i) tyA]
  tell $ indentAll _log
  return tyA
infer env CEmpty (Ann tm tyA) = do
  (_, _log) <- peek $ infer env (CFullType tyA) tm
  tell ["[Ty-Ann] " ++ logInferFull env CEmpty (Ann tm tyA) tyA]
  tell $ indentAll _log
  return tyA
infer env h (App tm1 tm2) = do
  (TArr _ ty12, _log) <- peek $ infer env (CTerm tm2 h) tm1
  tell ["[Ty-App] " ++ logInferFull env h (App tm1 tm2) ty12]
  tell $ indentAll _log
  return ty12
infer env (CFullType (TArr tyA tyB)) (Abs tm) = do
  (tyC, _log) <- peek $ infer (ETrm tyA env) (CFullType tyB) tm
  tell ["[Ty-Abs1] " ++ logInferFull env (CFullType (TArr tyA tyB)) (Abs tm) (TArr tyA tyC)]
  tell $ indentAll _log
  return $ TArr tyA tyC
infer env (CTerm tm2 h) (Abs tm) = do
  (tyA, _log1) <- peek $ infer env CEmpty tm2
  (tyB, _log2) <- peek $ infer (ETrm tyA env) (shiftContext0 h) tm
  tell ["[Ty-Abs2] " ++ logInferFull env (CTerm tm2 h) (Abs tm) (TArr tyA tyB)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return $ TArr tyA tyB
infer env (CTerm tm2 h) (AbsAnn tyA tm) = do
  (_, _log1) <- peek $ infer env (CFullType tyA) tm2
  (tyB, _log2) <- peek $ infer (ETrm tyA env) (shiftContext0 h) tm
  tell ["[Ty-AbsAnn] " ++ logInferFull env (CTerm tm2 h) (AbsAnn tyA tm) (TArr tyA tyB)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return $ TArr tyA tyB
infer env (CFullType (TArr tyA tyB)) (AbsAnn tyA' tm) | tyA == tyA' = do
  (_, _log) <- peek $ infer (ETrm tyA env) (CFullType tyB) tm
  tell ["[Ty-AbsAnn-Chk] " ++ logInferFull env (CFullType (TArr tyA tyB)) (AbsAnn tyA' tm) (TArr tyA tyB)]
  tell $ indentAll _log
  return $ TArr tyA tyB
infer env CEmpty (AbsAnn tyA tm) = do
  (tyB, _log) <- peek $ infer (ETrm tyA env) CEmpty tm
  tell ["[Ty-AbsAnn] " ++ logInferFull env CEmpty (AbsAnn tyA tm) tyB]
  tell $ indentAll _log
  return $ TArr tyA tyB
infer env (CFullType (TForall tyA)) (TAbs tm) = do
  (_, _log) <- peek $ infer (EUvar env) (CFullType tyA) tm
  tell ["[Ty-TAbs-Chk] " ++ logInferFull env (CFullType (TForall tyA)) (TAbs tm) (TForall tyA)]
  tell $ indentAll _log
  return $ TForall tyA
infer env h g | genericConsumer g && nonEmptyContext h = do
  (tyA, _log1) <- peek $ infer env CEmpty g
  ((EEmpty, tyB), _log2) <- peek $ sub (env, EEmpty) tyA h
  tell ["[Ty-Sub] " ++ logInferFull env h g tyB]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return tyB
infer env CEmpty (TAbs tm) = do
  (tyA, _log) <- peek $ infer (EUvar env) CEmpty tm
  tell ["[Ty-TAbs] " ++ logInferFull env CEmpty (TAbs tm) (TForall tyA)]
  tell $ indentAll _log
  return $ TForall tyA
infer env h (TApp tm tyA) = do
  (TForall tyB, _log) <- peek $ infer env (CTApp tyA h) tm
  tell ["[Ty-TApp] " ++ logInferFull env h (TApp tm tyA) (substTyp0 tyA tyB)]
  tell $ indentAll _log
  return (substTyp0 tyA tyB)
infer env (CFullType (TList tyA)) Nil = do
  tell ["[Ty-Nil-Chk] " ++ logInferFull env (CFullType (TList tyA)) Nil (TList tyA)]
  return (TList tyA)
infer env CEmpty Nil = do
  let tyNil = TForall (TList (TVar 0))
  tell ["[Ty-Nil] " ++ logInferFull env CEmpty Nil tyNil]
  return tyNil
infer env CEmpty Cons = do
  let tyCons = TForall (TArr (TVar 0) (TArr (TList (TVar 0)) (TList (TVar 0))))
  tell ["[Ty-Cons] " ++ logInferFull env CEmpty Cons tyCons]
  return tyCons
infer env CEmpty Pair = do
  let tyPair = TForall $ TForall $ TArr (TVar 1) $ TArr (TVar 0) $ TProd (TVar 1) (TVar 0)
  tell ["[Ty-Pair] " ++ logInferFull env CEmpty Pair tyPair]
  return tyPair
infer env CEmpty ST = do
  let tyST = TForall $ TForall $ TArr (TVar 1) $ TArr (TVar 0) $ TST (TVar 1) (TVar 0)
  tell ["[Ty-ST] " ++ logInferFull env CEmpty ST tyST]
  return tyST
infer _ _ _ = lift Nothing

main :: IO ()
main = do
  -- print idTyp
  let
      -- id : forall a. a -> a
      idTyp = TForall (TArr (TVar 0) (TVar 0))
      -- id = /\a. \x. x : a -> a
      idTrm = TAbs (Ann (Abs (Var 0)) (TArr (TVar 0) (TVar 0)))
      -- choose : forall a. a -> a -> a
      chooseTyp = TForall $ TArr (TVar 0) $ TArr (TVar 0) (TVar 0)
      -- auto : (forall a. a -> a) -> (forall a. a -> a)
      autoTyp = idTyp `TArr` idTyp
      -- auto' : forall a. (forall b. b -> b) -> a -> a
      auto'Typ = TForall $ TArr idTyp $ TArr (TVar 0) (TVar 0)
      -- poly : (forall a. a -> a) -> Int × Bool
      polyTyp = idTyp `TArr` TProd TInt TBool
      -- head : forall a. [a] -> a
      headTyp = TForall $ TArr (TList (TVar 0)) (TVar 0)
      -- tail : forall a. [a] -> [a]
      tailTyp = TForall $ TArr (TList (TVar 0)) (TList (TVar 0))
      -- length : forall a. [a] -> Int
      lengthTyp = TForall $ TArr (TList (TVar 0)) TInt
      -- single : forall a. a -> [a]
      singleTyp = TForall $ TArr (TVar 0) (TList (TVar 0))
      -- append : forall a. [a] -> [a] -> [a]
      appendTyp = TForall $ TArr (TList (TVar 0)) $ TArr (TList (TVar 0)) (TList (TVar 0))
      -- inc : Int -> Int
      incTyp = TArr TInt TInt
      -- map : forall a b. (a -> b) -> [a] -> [b]
      mapTyp = TForall $ TForall $ TArr (TArr (TVar 1) (TVar 0)) $ TArr (TList (TVar 1)) (TList (TVar 0))
      -- app : forall a b. (a -> b) -> a -> b
      appTyp = TForall $ TForall $ TArr (TArr (TVar 1) (TVar 0)) $ TArr (TVar 1) (TVar 0)
      -- revapp : forall a b. a -> (a -> b) -> b
      revappTyp = TForall $ TForall $ TArr (TVar 1) $ TArr (TArr (TVar 1) (TVar 0)) (TVar 0)
      -- runST : forall a. (forall b. ST b a) -> a
      runSTTyp = TForall $ TArr (TForall $ TST (TVar 0) (TVar 1)) (TVar 0)
      -- argST : forall a. ST a Int
      argSTTyp = TForall $ TST (TVar 0) TInt

      -- A1: \x. \y. y  Ann~>  /\a. /\b. (\x. \y. y) : a -> b -> b
      exA1 = infer EEmpty CEmpty (Abs (Abs (Var 0)))
      exA1Ann = infer EEmpty CEmpty $ TAbs $ TAbs $ Ann (Abs (Abs (Var 0))) (TArr (TVar 1) (TArr (TVar 0) (TVar 0)))
      -- with AbsAnn: /\a. /\b. \x : a. \y : b. y
      exA1Ann' = infer EEmpty CEmpty $ TAbs $ TAbs $ AbsAnn (TVar 1) $ AbsAnn (TVar 0) $ Var 0
      -- A2: choose id
      exA2 = infer (ETrm idTyp (ETrm chooseTyp EEmpty)) CEmpty $ Var 1 `App` Var 0
      -- A3: choose Nil ids Ann~> choose (Nil : [forall a. a -> a]) ids
      exA3 = infer (ETrm (TList idTyp) (ETrm chooseTyp EEmpty)) CEmpty $ Var 1 `App` Nil `App` Var 0
      exA3Ann = infer (ETrm (TList idTyp) (ETrm chooseTyp EEmpty)) CEmpty $ Var 1 `App` (Nil `Ann` TList idTyp) `App` Var 0
      -- A4: \x. x x Ann~> (\x. x x) : (forall a. a -> a) -> (forall a. a -> a)
      -- with AbsAnn: \x : (forall a. a -> a). x x
      exA4 = infer EEmpty CEmpty $ Abs (App (Var 0) (Var 0))
      exA4Ann = infer EEmpty CEmpty $ Abs (App (Var 0) (Var 0)) `Ann` autoTyp
      exA4Ann' = infer EEmpty CEmpty $ AbsAnn idTyp (App (Var 0) (Var 0))
      -- A5: id auto
      exA5 = infer (ETrm idTyp (ETrm autoTyp EEmpty)) CEmpty $ Var 0 `App` Var 1
      -- A6: id auto'
      exA6 = infer (ETrm idTyp (ETrm auto'Typ EEmpty)) CEmpty $ Var 0 `App` Var 1
      -- choose id : (forall a. a -> a) -> forall a. a -> a
      -- auto : (forall a. a -> a) -> (forall a. a -> a)
      -- A7: choose id auto Ann~> choose (id @ (forall a. a -> a)) auto
      exA7 = infer (ETrm chooseTyp (ETrm idTyp (ETrm autoTyp EEmpty))) CEmpty $ Var 0 `App` Var 1 `App` Var 2
      exA7Ann = infer (ETrm chooseTyp (ETrm idTyp (ETrm autoTyp EEmpty))) CEmpty $ Var 0 `App` (Var 1 `TApp` idTyp) `App` Var 2
      -- choose id : (forall a. a -> a) -> forall a. a -> a
      -- auto' : forall a. (forall b. b -> b) -> a -> a
      -- A8: choose id auto' Ann~> choose (/\a. \f. id f @a : (forall b. b -> b) -> a -> a) auto' / choose (/\a. \f. \x. id f x : (forall b. b -> b) -> a -> a) auto'
      exA8 = infer (ETrm chooseTyp (ETrm idTyp (ETrm auto'Typ EEmpty))) CEmpty $ Var 0 `App` Var 1 `App` Var 2
      -- exA8Ann = infer (ETrm chooseTyp (ETrm idTyp (ETrm auto'Typ EEmpty))) CEmpty $ Var 0 `App` (Var 1 `TApp` TForall (TArr (TArr (TVar 0) (TVar 0)) (TArr (TVar 0) (TVar 0)))) `App` (TAbs (Abs (Var 3 `App` (Ann (TApp (Var 0) (TVar 0)) (TArr (TVar 0) (TVar 0)))) `Ann` (TArr (TArr (TVar 0) (TVar 0)) (TArr (TVar 0) (TVar 0)))))
      exA8Ann = infer (ETrm chooseTyp (ETrm idTyp (ETrm auto'Typ EEmpty))) CEmpty $ Var 0 `App` TAbs (Abs (Var 2 `App` (Var 0 `TApp` TVar 0)) `Ann` TArr idTyp (TArr (TVar 0) (TVar 0))) `App` Var 2
      exA8Ann' = infer (ETrm chooseTyp (ETrm idTyp (ETrm auto'Typ EEmpty))) CEmpty $ Var 0 `App` TAbs (Abs (Abs (Var 3 `App` Var 1 `App` Var 0)) `Ann` TArr idTyp (TArr (TVar 0) (TVar 0))) `App` Var 2
      -- with AbsAnn: choose (/\a. \f : forall b. b -> b. id f @a) auto'
      exA8Ann'' = infer (ETrm chooseTyp (ETrm idTyp (ETrm auto'Typ EEmpty))) CEmpty $ Var 0 `App` TAbs (AbsAnn idTyp (Var 2 `App` (Var 0 `TApp` TVar 0)) `Ann` TArr idTyp (TArr (TVar 0) (TVar 0))) `App` Var 2
      -- A9: f (choose id) ids
      -- where f : forall a. (a -> a) -> [a] -> a
      fTyp = TForall $ TArr (TArr (TVar 0) (TVar 0)) $ TArr (TList (TVar 0)) (TVar 0)
      exA9 = infer (ETrm fTyp (ETrm chooseTyp (ETrm idTyp (ETrm (TList idTyp) EEmpty)))) CEmpty $ Var 0 `App` (Var 1 `App` Var 2) `App` Var 3
      -- A10: poly id
      exA10 = infer (ETrm polyTyp (ETrm idTyp EEmpty)) CEmpty $ Var 0 `App` Var 1
      -- A11: poly (\x. x) Ann~> poly (/\a. \x. x : a -> a)
      exA11 = infer (ETrm polyTyp EEmpty) CEmpty $ Var 0 `App` Abs (Var 0)
      exA11Ann = infer (ETrm polyTyp EEmpty) CEmpty $ Var 0 `App` TAbs (Abs (Var 0))
      -- A12: id poly (\x. x) Ann~> id poly (/\a. \x. x)
      exA12 = infer (ETrm idTyp (ETrm polyTyp EEmpty)) CEmpty $ Var 0 `App` Var 1 `App` Abs (Var 0)
      exA12Ann = infer (ETrm idTyp (ETrm polyTyp EEmpty)) CEmpty $ Var 0 `App` Var 1 `App` TAbs (Abs (Var 0))
      -- B1: \f. (f 1, f True) Ann~> \f. (f 1, f True) : (forall a. a -> a) -> Int × Bool
      exB1 = infer EEmpty CEmpty $ Abs (Pair `App` (Var 0 `App` LitInt 1) `App` (Var 0 `App` LitBool True))
      exB1Ann = infer EEmpty CEmpty $ Abs (Pair `App` (Var 0 `App` LitInt 1) `App` (Var 0 `App` LitBool True)) `Ann` (idTyp `TArr` TProd TInt TBool)
      -- with AbsAnn: \f : forall a. a -> a. (f 1, f True)
      exB1Ann' = infer EEmpty CEmpty $ AbsAnn idTyp (Pair `App` (Var 0 `App` LitInt 1) `App` (Var 0 `App` LitBool True))
      -- B2: \xs. poly (head xs) Ann~> \xs. poly (head xs) : [forall a. a -> a] -> Int × Bool
      exB2 = infer (ETrm polyTyp (ETrm headTyp EEmpty)) CEmpty $ Abs (Var 1 `App` (Var 2 `App` Var 0))
      exB2Ann = infer (ETrm polyTyp (ETrm headTyp EEmpty)) CEmpty $ Abs (Var 1 `App` (Var 2 `App` Var 0)) `Ann` (TList idTyp `TArr` TProd TInt TBool)
      -- with AbsAnn: \xs : [forall a. a -> a]. poly (head xs)
      exB2Ann' = infer (ETrm polyTyp (ETrm headTyp EEmpty)) CEmpty $ AbsAnn (TList idTyp) (Var 1 `App` (Var 2 `App` Var 0))
      -- C1: length ids
      exC1 = infer (ETrm lengthTyp (ETrm (TList idTyp) EEmpty)) CEmpty $ Var 0 `App` Var 1
      -- C2: tail ids
      exC2 = infer (ETrm tailTyp (ETrm (TList idTyp) EEmpty)) CEmpty $ Var 0 `App` Var 1
      -- C3: head ids
      exC3 = infer (ETrm headTyp (ETrm (TList idTyp) EEmpty)) CEmpty $ Var 0 `App` Var 1
      -- C4: single id
      exC4 = infer (ETrm singleTyp (ETrm idTyp EEmpty)) CEmpty $ Var 0 `App` Var 1
      -- C5: cons id ids
      exC5 = infer (ETrm idTyp (ETrm (TList idTyp) EEmpty)) CEmpty $ Cons `App` Var 0 `App` Var 1
      -- C6: cons (\x. x) ids Ann~> cons (/\a. \x. x : a -> a) ids
      exC6 = infer (ETrm (TList idTyp) EEmpty) CEmpty $ Cons `App` Abs (Var 0) `App` Var 0
      exC6Ann = infer (ETrm (TList idTyp) EEmpty) CEmpty $ Cons `App` idTrm `App` Var 0
      -- with AbsAnn: cons (/\a. \x : a. x) ids
      exC6Ann' = infer (ETrm (TList idTyp) EEmpty) CEmpty $ Cons `App` TAbs (AbsAnn (TVar 0) (Var 0)) `App` Var 0
      -- C7: append (single inc) (single id) Ann~> append (single inc) (single (id @ Int))
      exC7 = infer (ETrm appendTyp (ETrm singleTyp (ETrm incTyp (ETrm idTyp EEmpty)))) CEmpty $ Var 0 `App` (Var 1 `App` Var 2) `App` (Var 1 `App` Var 3)
      exC7Ann = infer (ETrm appendTyp (ETrm singleTyp (ETrm incTyp (ETrm idTyp EEmpty)))) CEmpty $ Var 0 `App` (Var 1 `App` Var 2) `App` (Var 1 `App` (Var 3 `TApp` TInt))
      -- C8: append (single id) ids
      exC8 = infer (ETrm appendTyp (ETrm singleTyp (ETrm idTyp (ETrm (TList idTyp) EEmpty)))) CEmpty $ Var 0 `App` (Var 1 `App` Var 2) `App` Var 3
      -- C9: map poly (single id)
      exC9 = infer (ETrm mapTyp (ETrm polyTyp (ETrm singleTyp (ETrm idTyp EEmpty)))) CEmpty $ Var 0 `App` Var 1 `App` (Var 2 `App` Var 3)
      -- C10: map head (single ids) Ann~> map (head @ (forall a. a -> a)) (single ids)
      exC10 = infer (ETrm mapTyp (ETrm headTyp (ETrm singleTyp (ETrm (TList idTyp) EEmpty)))) CEmpty $ Var 0 `App` Var 1 `App` (Var 2 `App` Var 3)
      exC10Ann = infer (ETrm mapTyp (ETrm headTyp (ETrm singleTyp (ETrm (TList idTyp) EEmpty)))) CEmpty $ Var 0 `App` (Var 1 `TApp` idTyp) `App` (Var 2 `App` Var 3)
      -- D1: app poly id
      exD1 = infer (ETrm appTyp (ETrm polyTyp (ETrm idTyp EEmpty))) CEmpty $ Var 0 `App` Var 1 `App` Var 2
      -- D2: revapp id poly
      exD2 = infer (ETrm revappTyp (ETrm idTyp (ETrm polyTyp EEmpty))) CEmpty $ Var 0 `App` Var 1 `App` Var 2
      -- D3: runST argST
      exD3 = infer (ETrm runSTTyp (ETrm argSTTyp EEmpty)) CEmpty $ Var 0 `App` Var 1
      -- D4: app runST argST Ann~> app (\x. runST (/\a. x @a) : (forall a. ST a Int) -> Int) argST
      exD4 = infer (ETrm appTyp (ETrm runSTTyp (ETrm argSTTyp EEmpty))) CEmpty $ Var 0 `App` Var 1 `App` Var 2
      exD4Ann = infer (ETrm appTyp (ETrm runSTTyp (ETrm argSTTyp EEmpty))) CEmpty $ Var 0 `App` (Abs (Var 2 `App` TAbs (Var 0 `TApp` TVar 0)) `Ann` TArr argSTTyp TInt) `App` Var 2
      -- with AbsAnn: app (\x : forall a. ST a Int. runST (/\a. x @a)) argST
      exD4Ann' = infer (ETrm appTyp (ETrm runSTTyp (ETrm argSTTyp EEmpty))) CEmpty $ Var 0 `App` AbsAnn argSTTyp (Var 2 `App` TAbs (Var 0 `TApp` TVar 0)) `App` Var 2
      exD4Ann'' = infer (ETrm appTyp (ETrm runSTTyp (ETrm argSTTyp EEmpty))) CEmpty $ Var 0 `App` (Var 1 `TApp` TInt) `App` Var 2
      -- D5: revapp argST runST Ann~> revapp argST (runST @Int) / revapp argST (\x. runST (/\a. x @a) : (forall a. ST a Int) -> Int)
      exD5 = infer (ETrm revappTyp (ETrm argSTTyp (ETrm runSTTyp EEmpty))) CEmpty $ Var 0 `App` Var 1 `App` Var 2
      exD5Ann = infer (ETrm revappTyp (ETrm argSTTyp (ETrm runSTTyp EEmpty))) CEmpty $ Var 0 `App` Var 1 `App` (Var 2 `TApp` TInt)
      exD5Ann' = infer (ETrm revappTyp (ETrm argSTTyp (ETrm runSTTyp EEmpty))) CEmpty $ Var 0 `App` Var 1 `App` (Abs (Var 3 `App` TAbs (Var 0 `TApp` TVar 0)) `Ann` TArr argSTTyp TInt)
      -- h : Int -> (forall a. a -> a)
      hTyp = TArr TInt idTyp
      -- k : forall a. a -> [a] -> a
      kTyp = TForall $ TArr (TVar 0) $ TArr (TList (TVar 0)) (TVar 0)
      -- lst : [forall a. Int -> a -> a]
      lstTyp = TList $ TForall $ TArr TInt $ TArr (TVar 0) (TVar 0)
      -- r : (forall a. a -> forall b. b -> b) -> Int
      rTyp = TArr (TForall (TArr (TVar 0) idTyp)) TInt
      -- E1: k h lst
      exE1 = infer (ETrm kTyp (ETrm hTyp (ETrm lstTyp EEmpty))) CEmpty $ Var 0 `App` Var 1 `App` Var 2
      -- exE1' = infer (ETrm chooseTyp (ETrm hTyp (ETrm (TForall $ TArr TInt $ TArr (TVar 0) (TVar 0)) EEmpty))) CEmpty $ Var 0 `App` Var 1 `App` Abs (Var 2 `App` Var 0)
      -- E2: k (\x. h x) lst Ann~> k (/\a. \x. h x @ a : Int -> a -> a) lst
      exE2 = infer (ETrm kTyp (ETrm hTyp (ETrm lstTyp EEmpty))) CEmpty $ Var 0 `App` Abs (Var 2 `App` Var 0) `App` Var 2
      exE2Ann = infer (ETrm kTyp (ETrm hTyp (ETrm lstTyp EEmpty))) CEmpty $ Var 0 `App` TAbs (Abs ((Var 2 `App` Var 0)) `Ann` TArr TInt (TArr (TVar 0) (TVar 0))) `App` Var 2
      -- with AbsAnn: k (/\a. \x : Int. h x @ a) lst
      exE2Ann' = infer (ETrm kTyp (ETrm hTyp (ETrm lstTyp EEmpty))) CEmpty $ Var 0 `App` TAbs (AbsAnn TInt (Var 2 `App` Var 0 `TApp` TVar 0)) `App` Var 2
      -- E3: r (\x. \y. y) Ann~> r (/\ a. (\x. /\ b. \y. y) : a -> forall b. b -> b)
      exE3 = infer (ETrm rTyp EEmpty) CEmpty $ Var 0 `App` Abs (Abs (Var 0))
      exE3Ann = infer (ETrm rTyp EEmpty) CEmpty $ Var 0 `App` TAbs (Abs (TAbs (Abs (Var 0))) `Ann` TArr (TVar 0) idTyp)
      -- with AbsAnn: r (/\a. \x : a. /\b. \y : b. y)
      exE3Ann' = infer (ETrm rTyp EEmpty) CEmpty $ Var 0 `App` TAbs (AbsAnn (TVar 0) (TAbs (AbsAnn (TVar 0) (Var 0))))
      
      -- FreezeML paper additions
      -- F5: auto id
      exF5 = infer (ETrm autoTyp (ETrm idTyp EEmpty)) CEmpty $ Var 0 `App` Var 1
      -- F6: cons (head ids) ids
      exF6 = infer (ETrm headTyp (ETrm (TList idTyp) EEmpty)) CEmpty $ Cons `App` (Var 0 `App` Var 1) `App` Var 1
      -- F7: head ids 3
      exF7 = infer (ETrm headTyp (ETrm (TList idTyp) EEmpty)) CEmpty $ Var 0 `App` Var 1 `App` LitInt 3
      -- F8: choose (head ids)
      exF8 = infer (ETrm chooseTyp (ETrm headTyp (ETrm (TList idTyp) EEmpty))) CEmpty $ Var 0 `App` (Var 1 `App` Var 2)

      -- Spine-local type inference
      exPair = infer EEmpty CEmpty $ (Pair `App` Abs (Var 0) `App` LitInt 1) `Ann` ((TInt `TArr` TInt) `TProd` TInt)
      exPairAnn = infer EEmpty CEmpty $ (Pair `App` (Abs (Var 0) `Ann` TArr TInt TInt) `App` LitInt 1) `Ann` ((TInt `TArr` TInt) `TProd` TInt)

  forM_
    [ exA1,
      exA1Ann,
      exA1Ann',
      exA2,
      exA3,
      exA3Ann,
      exA4,
      exA4Ann,
      exA4Ann',
      exA5,
      exA6,
      exA7,
      exA7Ann,
      exA8,
      exA8Ann,
      exA8Ann',
      exA8Ann'',
      exA9,
      exA10,
      exA11,
      exA11Ann,
      exA12,
      exA12Ann,
      exB1,
      exB1Ann,
      exB1Ann',
      exB2,
      exB2Ann,
      exB2Ann',
      exC1,
      exC2,
      exC3,
      exC4,
      exC5,
      exC6,
      exC6Ann,
      exC6Ann',
      exC7,
      exC7Ann,
      exC8,
      exC9,
      exC10,
      exC10Ann,
      exD1,
      exD2,
      exD3,
      exD4,
      exD4Ann,
      exD4Ann',
      exD4Ann',
      exD5,
      exD5Ann,
      exD5Ann',
      exE1,
      exE2,
      exE2Ann,
      exE2Ann',
      exE3,
      exE3Ann,
      exE3Ann',
      exF5,
      exF6,
      exF7,
      exF8,
      exPair,
      exPairAnn
    ]
    $ \ex -> case runWriterT ex of
      Just (tyA, logs) -> do
        putStrLn $ "inferred type: " ++ show tyA
        mapM_ putStrLn logs
        hFlush stdout
      Nothing -> print "Nothing"
