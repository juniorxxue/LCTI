{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant multi-way if" #-}
{-# HLINT ignore "Use if" #-}
module Main where

import Control.Monad (forM_, when, foldM)
import Control.Monad.Writer
import DeBruijn
import Log
import Syntax
import System.Environment (getArgs)
import Examples (examples, Example(..), getExample, getExamplesInGroup)
import Debug.Trace

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
-- findSol a b | trace ("findSol " ++ show a ++ " |- " ++ show b) False = undefined
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
ssubP (env, senv) (TUncurry tsA tyA) (TUncurry tsC tyD) | length tsA == length tsC = do
  let foldFunc (senv', logs) (tyA', tyC') = do
        (senv'', log') <- peek $ ssubN (env, senv') tyC' tyA'
        return (senv'', logs ++ log')
  (result, _) <- peek $ foldM foldFunc (senv, []) (zip tsA tsC)
  let (senv1, argLogs) = result
  (senv2, retLog) <- peek $ ssubP (env, senv1) tyA tyD
  tell ["[S-Uncurry] " ++ logSSubFull (env, senv) (TUncurry tsA tyA) (TUncurry tsC tyD) senv2]
  tell $ indentAll argLogs
  tell $ indentAll retLog
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
ssubN (env, senv) (TUncurry tsA tyB) (TUncurry tsC tyD) | length tsA == length tsC = do
  let foldFunc (senv', logs) (tyA', tyC') = do
        (senv'', log') <- peek $ ssubP (env, senv') tyC' tyA'
        return (senv'', logs ++ log')
  (result, _) <- peek $ foldM foldFunc (senv, []) (zip tsA tsC)
  let (senv1, argLogs) = result
  (senv2, retLog) <- peek $ ssubN (env, senv1) tyB tyD
  tell ["[S-Uncurry] " ++ logSSubFull (env, senv) (TUncurry tsA tyB) (TUncurry tsC tyD) senv2]
  tell $ indentAll argLogs
  tell $ indentAll retLog
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
ground env (TUncurry ts tyA) = do
  ts' <- mapM (ground env) ts
  tyA' <- ground env tyA
  return $ TUncurry ts' tyA'
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

dispatch :: (Env, Env) -> [Typ] -> [Trm] -> WriterT Log Maybe (Env, [Typ])
dispatch (a1, a2) b c | trace ("dispatch " ++ show a1 ++ ";" ++ show a2 ++ " |- " ++ show b ++ " ⇉ " ++ show c) False = undefined
dispatch (env, senv) [tyA] [e] | open (envConcat env senv) tyA = do
  (tyA', _log) <- peek $ infer (envConcat env senv) CEmpty e
  (senv', _log') <- peek $ ssubN (env, senv) tyA' tyA
  tell ["[S-Dispatch-Open] " ++ logDispatch (env, senv) [tyA] [e] [tyA'] senv']
  tell $ indentAll _log
  tell $ indentAll _log'
  return (senv', [tyA'])
dispatch (env, senv) [tyA] [e] | closed (envConcat env senv) tyA = do
  grdA <- ground (envConcat env senv) tyA
  (_, _log) <- peek $ infer (envConcat env senv) (CFullType grdA) e
  tell ["[S-Dispatch-Closed] " ++ logDispatch (env, senv) [tyA] [e] [tyA] senv]
  tell $ indentAll _log
  return (senv, [tyA])
dispatch (env, senv) (tyA:tyAs) (e:es) | open (envConcat env senv) tyA = do
  (tyA', _log) <- peek $ infer (envConcat env senv) CEmpty e
  (senv', _log') <- peek $ ssubN (env, senv) tyA' tyA
  ((senv'', tyAs'), _log'') <- peek $ dispatch (env, senv') tyAs es
  tell ["[S-Dispatch-Cons-Open] " ++ logDispatch (env, senv) (tyA:tyAs) (e:es) (tyA':tyAs') senv'']
  tell $ indentAll _log
  tell $ indentAll _log'
  tell $ indentAll _log''
  return (senv'', tyA':tyAs')
dispatch (env, senv) (tyA:tyAs) (e:es) | closed (envConcat env senv) tyA = do
  grdA <- ground (envConcat env senv) tyA
  (_, _log) <- peek $ infer (envConcat env senv) (CFullType grdA) e
  ((senv', tyAs'), _log') <- peek $ dispatch (env, senv) tyAs es
  tell ["[S-Dispatch-Cons-Closed] " ++ logDispatch (env, senv) (tyA:tyAs) (e:es) (tyA:tyAs') senv']
  tell $ indentAll _log
  tell $ indentAll _log'
  return (senv', tyA:tyAs')
dispatch _ _ _ = lift Nothing

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
  tell ["[S-Term-Closed] " ++ logSubFull (env, senv) (TArr tyA tyB) (CTerm e h) senv' (TArr tyC tyD)]
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
sub (env, senv) (TUncurry tyAs tyB) (CUncurry es h) = do
  ((senv', tyAs'), _log1) <- peek $ dispatch (env, senv) tyAs es
  ((senv'', tyB'), _log2) <- peek $ sub (env, senv') tyB h
  tell ["[S-Arr-UC] " ++ logSubFull (env, senv) (TUncurry tyAs tyB) (CUncurry es h) senv'' (TUncurry tyAs' tyB')]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return (senv'', TUncurry tyAs' tyB')
sub (env, senv) (TForall tyA) (CTerm e h) = do
  ((ESvar _ senv', tyB), _log1) <- peek $ sub (env, EEvar senv) tyA (shiftTyContext0 (CTerm e h))
  tell ["[S-Forall-L] " ++ logSubFull (env, senv) (TForall tyA) (CTerm e h) senv' (unshiftTyp0 tyB)]
  tell $ indentAll _log1
  return (senv', unshiftTyp0 tyB)
sub (env, senv) (TForall tyA) (CUncurry es h) = do
  ((ESvar _ senv', tyB), _log1) <- peek $ sub (env, EEvar senv) tyA (shiftTyContext0 (CUncurry es h))
  tell ["[S-Forall-L-UC] " ++ logSubFull (env, senv) (TForall tyA) (CUncurry es h) senv' (unshiftTyp0 tyB)]
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
sub (env, senv) (TVar k) (CUncurry es h) | isSvar (envConcat env senv) k = do
  tyA <- findSol (envConcat env senv) k
  ((senv', tyBC), _log) <- peek $ sub (env, senv) tyA (CUncurry es h)
  tell ["[S-Svar-UC] " ++ logSubFull (env, senv) (TVar k) (CUncurry es h) senv' tyBC]
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
  (TArr _ ty, _log) <- peek $ infer env (CTerm tm2 h) tm1
  tell ["[Ty-App] " ++ logInferFull env h (App tm1 tm2) ty]
  tell $ indentAll _log
  return ty
infer env h (AppUncurry tm1 tm2s) = do
  (TUncurry _ ty, _log) <- peek $ infer env (CUncurry tm2s h) tm1
  tell ["[Ty-App-UC] " ++ logInferFull env h (AppUncurry tm1 tm2s) ty]
  tell $ indentAll _log
  return ty
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
infer env (CFullType (TUncurry ts tyB)) (AbsUncurry n tm) | n == length ts = do
  (tyC, _log) <- peek $ infer (foldr ETrm env ts) (CFullType tyB) tm
  tell ["[Ty-Abs-UC1] " ++ logInferFull env (CFullType (TUncurry ts tyB)) (AbsUncurry n tm) (TUncurry ts tyC)]
  tell $ indentAll _log
  return $ TUncurry ts tyC
infer env (CUncurry tm2s h) (AbsUncurry n tm) | n == length tm2s = do
  (tyAs, _log1) <- peek $ mapM (infer env CEmpty) tm2s
  (tyB, _log2) <- peek $ infer (foldr ETrm env tyAs) (iterate shiftContext0 h !! n) tm
  tell ["[Ty-Abs-UC2] " ++ logInferFull env (CUncurry tm2s h) (AbsUncurry n tm) (TUncurry tyAs tyB)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return $ TUncurry tyAs tyB
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
  args <- getArgs
  let showDrv = "--drv" `elem` args
      showHelp = "--help" `elem` args || "-h" `elem` args
  
  if showHelp
    then do
      putStrLn "Usage: cabal run Poly -- [OPTIONS] [EXAMPLE_NAME]"
      putStrLn ""
      putStrLn "Options:"
      putStrLn "  --help, -h        Show this help message"
      putStrLn "  --drv, -d         Show detailed derivation steps"
      putStrLn ""
      putStrLn "Examples:"
      putStrLn "  cabal run Poly                    # Run all examples (default)"
      putStrLn "  cabal run Poly -- A1              # Run specific example"
      putStrLn "  cabal run Poly -- A1 A2 A3        # Run multiple examples"
      putStrLn "  cabal run Poly -- --drv A1        # Run with derivation"
    else do
      -- Filter out flags to get example names
      let requestedExamples = filter (not . isFlag) args
          isFlag arg = arg `elem` ["--drv", "--help", "-h"]
      if null requestedExamples
        then runAllExamples showDrv
        else runSpecificExamples showDrv requestedExamples

runAllExamples :: Bool -> IO ()
runAllExamples showDrv = do
  forM_ examples $ \example -> do
    runSingleExample example showDrv

runSpecificExamples :: Bool -> [String] -> IO ()
runSpecificExamples showDrv names = do
  forM_ names $ \name -> do
    let groupExamples = getExamplesInGroup name
    if not (null groupExamples)
      then do
        putStrLn $ "Running examples: " ++ name
        forM_ groupExamples $ \example -> do
          runSingleExample example showDrv
      else do
        case getExample name of
          Just example -> runSingleExample example showDrv
          Nothing -> do
            putStrLn $ "Error: Example or group '" ++ name ++ "' not found."
            putStrLn "Use --help to see usage information."

runSingleExample :: Example -> Bool -> IO ()
runSingleExample example showDrv = do
  putStrLn $ replicate 80 '-'
  putStrLn $ exampleName example ++ ": " ++ exampleDescription example
  case runWriterT (infer (exampleEnv example) CEmpty (exampleTerm example)) of
    Just (tyA, logs) -> do
      putStrLn $ "[✓] Typing result: " ++ show tyA
      when showDrv $ do
        putStrLn ""
        mapM_ putStrLn logs
    Nothing -> do
      putStrLn "[x] Typing failed"
