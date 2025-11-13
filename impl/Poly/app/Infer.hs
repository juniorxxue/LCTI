{-# LANGUAGE FlexibleContexts #-}
module Infer where

import Control.Monad (foldM, guard, unless)
import Control.Monad.Writer
import Log
import Syntax
import Unbound.Generics.LocallyNameless
import Control.Applicative (Alternative, (<|>), empty)
import Debug.Trace
import Control.Monad.Error.Class (MonadError, throwError)

ensure :: MonadError String m => Bool -> String -> m ()
ensure cond msg = unless cond (throwError msg)

findSol :: (MonadError String m) => Env -> TyName -> m Ty
findSol env a = do
  case lookupTyVar env a of
    Just (Svar ty) -> return ty
    _ -> throwError "findSol: lookupTyVar failed"    

ssub :: (MonadWriter Log m, MonadFail m, Fresh m, MonadError String m) => (Env, Env) -> Ty -> Polar -> Ty -> m Env
-- ssub (env, senv) b p c | trace ("ssub " ++ ";" ++ show senv ++ " |- " ++ show b ++ " " ++ show p ++ " " ++ show c) False = undefined
ssub (env, senv) TInt p TInt = do
  tell ["[S-Int] " ++ logSSubFull (env, senv) TInt p TInt senv]
  return senv
ssub (env, senv) TBool p TBool = do
  tell ["[S-Bool] " ++ logSSubFull (env, senv) TBool p TBool senv]
  return senv
ssub (env, senv) (TVar a) p (TVar b) | isUvar (envConcat env senv) a && a == b = do
  tell ["[S-Refl] " ++ logSSubFull (env, senv) (TVar a) p (TVar b) senv]
  return senv
ssub (env, senv) (TVar a) Pos tyA = do
  case lookupTyVar env a of
    Just Evar -> do 
      case inst senv a tyA of
        Just newenv -> do
          tell ["[S-MVar-L] " ++ logSSubFull (env, senv) (TVar a) Pos tyA newenv]
          return newenv
        Nothing -> throwError $ "ssub: inst failed" ++ show a ++ " " ++ show tyA
    Just (Svar tyB) -> do
      ensure (tyA `aeq` tyB) "ssub: tyA /= tyB"
      tell ["[S-SVar-L] " ++ logSSubFull (env, senv) (TVar a) Pos tyA senv]
      return senv
    _ -> throwError $ "ssub: lookupTyVar failed" ++ show senv ++ " " ++ show tyA  
ssub (env, senv) tyA Neg (TVar a) = do
  case lookupTyVar env a of
    Just Evar -> do
      case inst senv a tyA of
        Just newenv -> do
          tell ["[S-MVar-R] " ++ logSSubFull (env, senv) (TVar a) Neg tyA newenv]
          return newenv
        Nothing -> throwError $ "ssub: inst failed" ++ show a ++ " " ++ show tyA
    Just (Svar tyB) -> do
      ensure (tyA `aeq` tyB) "ssub: tyA /= tyB"
      tell ["[S-SVar-R] " ++ logSSubFull (env, senv) (TVar a) Neg tyA senv]
      return senv
    _ -> throwError $ "ssub: lookupTyVar failed" ++ show senv ++ " " ++ show tyA  
ssub (env, senv) (TArr tyA tyB) p (TArr tyC tyD) = do
  (senv1, _log1) <- peek $ ssub (env, senv) tyC (flipPolar p) tyA
  (senv2, _log2) <- peek $ ssub (env, senv1) tyB p tyD
  tell ["[S-Arr] " ++ logSSubFull (env, senv) (TArr tyA tyB) p (TArr tyC tyD) senv2]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return senv2
ssub (env, senv) (TUncurry tsA tyA) p (TUncurry tsC tyD) | length tsA == length tsC = do
  let foldFunc (senv', logs) (tyA', tyC') = do
        (senv'', log') <- peek $ ssub (env, senv') tyC' (flipPolar p) tyA'
        return (senv'', logs ++ log')
  (result, _) <- peek $ foldM foldFunc (senv, []) (zip tsA tsC)
  let (senv1, argLogs) = result
  (senv2, retLog) <- peek $ ssub (env, senv1) tyA p tyD
  tell ["[S-Uncurry] " ++ logSSubFull (env, senv) (TUncurry tsA tyA) p(TUncurry tsC tyD) senv2]
  tell $ indentAll argLogs
  tell $ indentAll retLog
  return senv2
ssub (env, senv) (TForall bdA) p (TForall bdB) = do
  mAB <- unbind2 bdA bdB
  (a, tyA, _, tyB) <- maybe (throwError "ssub: unbind2 failed") pure mAB
  (EUvar _ senv', _log) <- peek $ ssub (env, EUvar a senv) tyA p tyB
  tell ["[S-Forall] " ++ logSSubFull (env, senv) (TForall bdA) p (TForall bdB) senv']
  tell $ indentAll _log
  return senv'
ssub (env, senv) (TList tyA) p (TList tyB) = do
  (senv', _log) <- peek $ ssub (env, senv) tyA p tyB
  tell ["[S-List] " ++ logSSubFull (env, senv) (TList tyA) p (TList tyB) senv']
  return senv'
ssub (env, senv) (TProd tyA tyB) p (TProd tyC tyD) = do
  (senv1, _log1) <- peek $ ssub (env, senv) tyA p tyC
  (senv2, _log2) <- peek $ ssub (env, senv1) tyB p tyD
  tell ["[S-Prod] " ++ logSSubFull (env, senv) (TProd tyA tyB) p (TProd tyC tyD) senv2]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return senv2
ssub (env, senv) (TST tyA tyB) p (TST tyC tyD) = do
  (senv1, _log1) <- peek $ ssub (env, senv) tyA p tyC
  (senv2, _log2) <- peek $ ssub (env, senv1) tyB p tyD
  (senv3, _log3) <- peek $ ssub (env, senv2) tyC p tyA
  tell ["[S-ST] " ++ logSSubFull (env, senv) (TST tyA tyB) p (TST tyC tyD) senv3]
  tell $ indentAll _log1
  tell $ indentAll _log2
  tell $ indentAll _log3
  return senv3
ssub _ _ _ _ = fail "ssub: unexpected case"

ground :: (MonadWriter Log m, Fresh m, MonadFail m, MonadError String m) => Env -> Ty -> m Ty
-- ground a b | trace ("ground " ++ show a ++ " |- " ++ show b) False = undefined
ground _ TInt = return TInt
ground _ TBool = return TBool
ground env (TVar k) | isUvar env k = return (TVar k)
ground env (TVar k) = findSol env k
ground env (TArr tyA tyB) = liftA2 TArr (ground env tyA) (ground env tyB)
ground env (TForall bdA) = do
  (a, tyA) <- unbind bdA
  tyA' <- ground (EUvar a env) tyA
  return $ TForall (bind a tyA')
ground env (TUncurry ts tyA) = do
  ts' <- mapM (ground env) ts
  tyA' <- ground env tyA
  return $ TUncurry ts' tyA'
ground env (TList tyA) = do
  tyA' <- ground env tyA
  return $ TList tyA'
ground env (TProd tyA tyB) = liftA2 TProd (ground env tyA) (ground env tyB)
ground env (TST tyA tyB) = liftA2 TST (ground env tyA) (ground env tyB)

inferUncurry :: (MonadWriter Log m, Fresh m, Alternative m, MonadFail m, MonadError String m) => (Env, Env) -> Ty -> Tm -> m (Env, Ty)
inferUncurry (env, senv) tyA e = do
  isOpen (envConcat env senv) tyA
  (tyA', _log) <- peek $ infer (envConcat env senv) CEmpty e
  (senv', _log') <- peek $ ssub (env, senv) tyA' Pos tyA
  tell ["[UC-Infer] " ++ logInferUncurry (env, senv) tyA e tyA' senv']
  tell $ indentAll _log
  tell $ indentAll _log'
  return (senv', tyA')
  <|> do
  closed (envConcat env senv) tyA
  grdA <- ground (envConcat env senv) tyA
  (_, _log) <- peek $ infer (envConcat env senv) (CFullType grdA) e
  tell ["[UC-Check] " ++ logInferUncurry (env, senv) tyA e tyA senv]
  tell $ indentAll _log
  return (senv, tyA)

sub :: (MonadWriter Log m, Fresh m, Alternative m, MonadFail m, MonadError String m) => (Env, Env) -> Ty -> Context -> m (Env, Ty)
sub (a1, a2) b c | trace ("sub " ++ ";" ++ show a2 ++ " |- " ++ show b ++ " <: " ++ show c) False = undefined
sub (env, senv) tyA CEmpty = do  
  closed (envConcat env senv) tyA
  grdA <- ground (envConcat env senv) tyA
  tell ["[S-Empty] " ++ logSubFull (env, senv) tyA CEmpty senv grdA]
  return (senv, grdA)
sub (env, senv) tyA (CFullType tyB) = do
  (senv', _log1) <- peek $ ssub (env, senv) tyA Pos tyB
  tell ["[S-Type] " ++ logSubFull (env, senv) tyA (CFullType tyB) senv' tyB]
  tell $ indentAll _log1
  return (senv', tyB)
sub (env, senv) (TArr tyA tyB) (CTerm e h) = 
  do
  closed (envConcat env senv) tyA
  grdA <- ground (envConcat env senv) tyA
  (tyC, _log1) <- peek $ infer (envConcat env senv) (CFullType grdA) e
  ((senv', tyD), _log2) <- peek $ sub (env, senv) tyB h
  tell ["[S-Term-Closed] " ++ logSubFull (env, senv) (TArr tyA tyB) (CTerm e h) senv' (TArr tyC tyD)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return (senv', TArr tyC tyD)
  <|> 
  do
  isOpen (envConcat env senv) tyA 
  (tyC, _log1) <- peek $ infer (envConcat env senv) CEmpty e
  (senv1, _log2) <- peek $ ssub (env, senv) tyC Neg tyA
  ((senv2, tyD), _log3) <- peek $ sub (env, senv1) tyB h
  tell ["[S-Term-Open] " ++ logSubFull (env, senv) (TArr tyA tyB) (CTerm e h) senv2 (TArr tyC tyD)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  tell $ indentAll _log3
  return (senv2, TArr tyC tyD)
sub (env, senv) (TUncurry tyAs tyB) (CUncurry es h) = do
  let foldFunc ((senv', tyAs'), logs) (tyA', e') = do
        ((senv'', tyA''), log') <- peek $ inferUncurry (env, senv') tyA' e'
        return ((senv'', tyAs' ++ [tyA'']), logs ++ log')
  ((senv', tyAs'), _log1) <- foldM foldFunc ((senv, []), []) (zip tyAs es)
  ((senv'', tyB'), _log2) <- peek $ sub (env, senv') tyB h
  tell ["[S-Arr-UC] " ++ logSubFull (env, senv) (TUncurry tyAs tyB) (CUncurry es h) senv'' (TUncurry tyAs' tyB')]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return (senv'', TUncurry tyAs' tyB')
sub (env, senv) (TForall bdA) (CTerm e h) = do
  (a, tyA) <- unbind bdA
  ((ESvar _ _ senv', tyB), _log1) <- peek $ sub (env, EEvar a senv) tyA (CTerm e h)
  tell ["[S-Forall-L] " ++ logSubFull (env, senv) (TForall bdA) (CTerm e h) senv' tyB]
  tell $ indentAll _log1
  return (senv', tyB)
sub (env, senv) (TForall bdA) (CUncurry es h) = do
  (a, tyA) <- unbind bdA
  ((ESvar _ _ senv', tyB), _log1) <- peek $ sub (env, EEvar a senv) tyA (CUncurry es h)
  tell ["[S-Forall-L-UC] " ++ logSubFull (env, senv) (TForall bdA) (CUncurry es h) senv' tyB]
  tell $ indentAll _log1
  return (senv', tyB)
sub (env, senv) (TVar k) h | isSvar (envConcat env senv) k = do
  tyA <- findSol (envConcat env senv) k
  ((senv', tyB), _log) <- peek $ sub (env, senv) tyA h
  tell ["[S-Svar] " ++ logSubFull (env, senv) (TVar k) h senv' tyB]
  tell $ indentAll _log
  return (senv', tyB)
sub (env, senv) (TVar k) (CTerm e h) | isUvar (envConcat env senv) k = do
  (tyA, _log) <- peek $ infers (envConcat env senv) (CTerm e h)
  case inst senv k tyA of
    Just newenv -> do
      tell ["[S-Infers] " ++ logSubFull (env, senv) (TVar k) (CTerm e h) newenv tyA]
      tell $ indentAll _log
      return (newenv, tyA)
    Nothing -> fail "sub: inst failed"
sub (env, senv) (TProd tyA tyB) (CFst h) = do
  ((senv', tyA'), _log) <- peek $ sub (env, senv) tyA h
  tell ["[S-Prod-Fst] " ++ logSubFull (env, senv) (TProd tyA tyB) (CFst h) senv' tyA']
  tell $ indentAll _log
  return (senv', TProd tyA' tyB)
sub (env, senv) (TProd tyA tyB) (CSnd h) = do
  ((senv', tyB'), _log) <- peek $ sub (env, senv) tyB h
  tell ["[S-Prod-Snd] " ++ logSubFull (env, senv) (TProd tyA tyB) (CSnd h) senv' tyB']
  tell $ indentAll _log
  return (senv', TProd tyA tyB')
sub _ _ _ = fail "sub: unexpected case"

infers :: (MonadWriter Log m, Fresh m, Alternative m, MonadFail m, MonadError String m) => Env -> Context -> m Ty
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
infers _ _ = fail "infers: unexpected case"

infer :: (MonadWriter Log m, Fresh m, Alternative m, MonadFail m, MonadError String m) => Env -> Context -> Tm -> m Ty
infer a b c | trace ("infer " ++ " |- " ++ show b ++ " => " ++ show c) False = undefined
infer env CEmpty (LitInt n) = do
  tell ["[Ty-Int] " ++ logInferFull env CEmpty (LitInt n) TInt]
  return TInt
infer env CEmpty (LitBool b) = do
  tell ["[Ty-Bool] " ++ logInferFull env CEmpty (LitBool b) TBool]
  return TBool
infer env CEmpty (Var i) = do
  case lookupTmVar env i of
    Just tyA -> do
      tell ["[Ty-Var] " ++ logInferFull env CEmpty (Var i) tyA]    
      return tyA
    Nothing -> empty
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
infer env (CFullType (TArr tyA tyB)) (Abs bdTm) = do
  (x, tm) <- unbind bdTm
  (tyC, _log) <- peek $ infer (ETrm x tyA env) (CFullType tyB) tm
  tell ["[Ty-Abs1] " ++ logInferFull env (CFullType (TArr tyA tyB)) (Abs bdTm) (TArr tyA tyC)]
  tell $ indentAll _log
  return $ TArr tyA tyC
infer env (CTerm tm2 h) (Abs bdTm) = do
  (x, tm) <- unbind bdTm
  (tyA, _log1) <- peek $ infer env CEmpty tm2
  (tyB, _log2) <- peek $ infer (ETrm x tyA env) h tm
  tell ["[Ty-Abs2] " ++ logInferFull env (CTerm tm2 h) (Abs bdTm) (TArr tyA tyB)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return $ TArr tyA tyB
infer env (CFullType (TArr tyA tyB)) (AbsAnn bdTm) = do
  ((x, Embed tyA'), tm) <- unbind bdTm
  guard (tyA `aeq` tyA')
  (_, _log) <- peek $ infer (ETrm x tyA env) (CFullType tyB) tm
  tell ["[Ty-AbsAnn1] " ++ logInferFull env (CFullType (TArr tyA tyB)) (AbsAnn bdTm) (TArr tyA tyB)]
  tell $ indentAll _log
  return $ TArr tyA tyB
infer env (CTerm tm2 h) (AbsAnn bdTm) = do
  ((x, Embed tyA), tm) <- unbind bdTm
  (_, _log1) <- peek $ infer env (CFullType tyA) tm2
  (tyB, _log2) <- peek $ infer (ETrm x tyA env) h tm
  tell ["[Ty-AbsAnn2] " ++ logInferFull env (CTerm tm2 h) (AbsAnn bdTm) (TArr tyA tyB)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return $ TArr tyA tyB
infer env CEmpty (AbsAnn bdTm) = do
  ((x, Embed tyA), tm) <- unbind bdTm  
  (tyB, _log) <- peek $ infer (ETrm x tyA env) CEmpty tm
  tell ["[Ty-AbsAnn3] " ++ logInferFull env CEmpty (AbsAnn bdTm) tyB]
  tell $ indentAll _log
  return $ TArr tyA tyB
infer env (CFullType (TUncurry tyAs tyB)) (AbsUncurryAnn bdTm) = do
  (xs_tyAs, tm) <- unbind bdTm
  let xs = [ x_A | (x_A, _) <- xs_tyAs]
      tyAs' = [ ty_A | (_, Embed ty_A) <- xs_tyAs]  
  guard $ all (uncurry aeq) (zip tyAs tyAs')
  (_, _log) <- peek $ infer (foldl (\env' (x, tyA) -> ETrm x tyA env') env (zip xs tyAs')) (CFullType tyB) tm
  tell ["[Ty-AbsAnn-UC1] " ++ logInferFull env (CFullType (TUncurry tyAs tyB)) (AbsUncurryAnn bdTm) (TUncurry tyAs tyB)]
  tell $ indentAll _log
  return $ TUncurry tyAs tyB
infer env (CUncurry tm2s h) (AbsUncurryAnn bdTm) = do  
  (xs_tyAs, tm) <- unbind bdTm
  let xs = [ x_A | (x_A, _) <- xs_tyAs]
      tyAs = [ ty_A | (_, Embed ty_A) <- xs_tyAs]
  (_, _log1) <- peek $ mapM (\(tyA, tm2) -> infer env (CFullType tyA) tm2) (zip tyAs tm2s)
  (tyB, _log2) <- peek $ infer (foldl (\env' (x, tyA) -> ETrm x tyA env') env (zip xs tyAs)) h tm
  tell ["[Ty-AbsAnn-UC2] " ++ logInferFull env (CUncurry tm2s h) (AbsUncurryAnn bdTm) (TUncurry tyAs tyB)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return $ TUncurry tyAs tyB
infer env CEmpty (AbsUncurryAnn bdTm) = do
  (xs_tyAs, tm) <- unbind bdTm
  let xs = [ x_A | (x_A, _) <- xs_tyAs]
      tyAs = [ ty_A | (_, Embed ty_A) <- xs_tyAs]
  (tyB, _log) <- peek $ infer (foldl (\env' (x, tyA) -> ETrm x tyA env') env (zip xs tyAs)) CEmpty tm
  tell ["[Ty-AbsAnn-UC3] " ++ logInferFull env CEmpty (AbsUncurryAnn bdTm) tyB]
  tell $ indentAll _log
  return $ TUncurry tyAs tyB
infer env (CFullType (TUncurry ts tyB)) (AbsUncurry bdTm) = do
  (xs, tm) <- unbind bdTm
  (tyC, _log) <- peek $ infer (foldl (\env' (x, tyA) -> ETrm x tyA env') env (zip xs ts)) (CFullType tyB) tm
  tell ["[Ty-Abs-UC1] " ++ logInferFull env (CFullType (TUncurry ts tyB)) (AbsUncurry bdTm) (TUncurry ts tyC)]
  tell $ indentAll _log
  return $ TUncurry ts tyC
infer env (CUncurry tm2s h) (AbsUncurry bd) = do
  (xs, tm) <- unbind bd
  (tyAs, _log1) <- peek $ mapM (infer env CEmpty) tm2s
  (tyB, _log2) <- peek $ infer (foldl (\env' (x, tyA) -> ETrm x tyA env') env (zip xs tyAs)) h tm
  tell ["[Ty-Abs-UC2] " ++ logInferFull env (CUncurry tm2s h) (AbsUncurry bd) (TUncurry tyAs tyB)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return $ TUncurry tyAs tyB
infer env (CFullType (TForall bdTy)) (TAbs bdTm) = do
  Just (a, tyA, _, tm) <- unbind2 bdTy bdTm
  (_, _log) <- peek $ infer (EUvar a env) (CFullType tyA) tm
  tell ["[Ty-TAbs-Chk] " ++ logInferFull env (CFullType (TForall bdTy)) (TAbs bdTm) (TForall bdTy)]
  tell $ indentAll _log
  return $ TForall bdTy
infer env CEmpty (Pair tm1 tm2) = do
  (tyA, _log1) <- peek $ infer env CEmpty tm1
  (tyB, _log2) <- peek $ infer env CEmpty tm2
  tell ["[Ty-Pair1] " ++ logInferFull env CEmpty (Pair tm1 tm2) (TProd tyA tyB)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return $ TProd tyA tyB
infer env (CFullType (TProd tyA tyB)) (Pair tm1 tm2) = do
  (tyA', _log1) <- peek $ infer env (CFullType tyA) tm1
  (tyB', _log2) <- peek $ infer env (CFullType tyB) tm2
  tell ["[Ty-Pair2] " ++ logInferFull env (CFullType (TProd tyA tyB)) (Pair tm1 tm2) (TProd tyA' tyB')]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return $ TProd tyA' tyB'
infer env h (Fst tm) = do
  (ty, _log1) <- peek $ infer env (CFst h) tm
  case ty of
    TProd tyA _ -> do
      tell ["[Ty-Fst] " ++ logInferFull env h (Fst tm) tyA]
      tell $ indentAll _log1
      return tyA
    _ -> fail "infer: unexpected case"
infer env h (Snd tm) = do
  (ty, _log1) <- peek $ infer env (CSnd h) tm
  case ty of
    TProd _ tyB -> do
      tell ["[Ty-Snd] " ++ logInferFull env h (Snd tm) tyB]
      tell $ indentAll _log1
      return tyB
    _ -> fail "infer: unexpected case"
infer env (CFst h) (Pair tm1 tm2) = do
  (tyA, _log1) <- peek $ infer env h tm1
  (tyB, _log2) <- peek $ infer env CEmpty tm2
  tell ["[Ty-Pair-Fst] " ++ logInferFull env (CFst h) (Pair tm1 tm2) (TProd tyA tyB)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return $ TProd tyA tyB
infer env (CSnd h) (Pair tm1 tm2) = do
  (tyA, _log1) <- peek $ infer env CEmpty tm1
  (tyB, _log2) <- peek $ infer env h tm2
  tell ["[Ty-Pair-Snd] " ++ logInferFull env (CSnd h) (Pair tm1 tm2) (TProd tyA tyB)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return $ TProd tyA tyB
infer env h g | genericConsumer g && nonEmptyContext h = do
  (tyA, _log1) <- peek $ infer env CEmpty g
  ((EEmpty, tyB), _log2) <- peek $ sub (env, EEmpty) tyA h
  tell ["[Ty-Sub] " ++ logInferFull env h g tyB]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return tyB
infer env CEmpty (TAbs bdTm) = do
  (a, tm) <- unbind bdTm
  (tyA, _log) <- peek $ infer (EUvar a env) CEmpty tm
  tell ["[Ty-TAbs] " ++ logInferFull env CEmpty (TAbs bdTm) (TForall (bind a tyA))]
  tell $ indentAll _log
  return $ TForall (bind a tyA)
infer env h (TApp tm tyA) = do
  (TForall bdTy, _log1) <- peek $ infer env CEmpty tm
  (a, tyB) <- unbind bdTy
  ((EEmpty, tyC), _log2) <- peek $ sub (env, EEmpty) (subst a tyB tyA) h
  tell ["[Ty-TApp] " ++ logInferFull env h (TApp tm tyA) tyC]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return tyC
infer env (CFullType (TList tyA)) Nil = do
  tell ["[Ty-Nil-Chk] " ++ logInferFull env (CFullType (TList tyA)) Nil (TList tyA)]
  return (TList tyA)
infer env CEmpty Nil = do  
  let tyNil = TForall (bind (s2n "a") (TList (TVar (s2n "a"))))
  tell ["[Ty-Nil] " ++ logInferFull env CEmpty Nil tyNil]
  return tyNil
infer _ _ _ = throwError "infer: unexpected case"