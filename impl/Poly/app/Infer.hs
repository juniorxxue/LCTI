{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
module Infer where

import Control.Monad (foldM, guard, unless)
import Derivation
import Log (logSSubFull, logSubFull, logInferFull, logInfersFull, logInferUncurry, formatError)
import Syntax
import Unbound.Generics.LocallyNameless
import Control.Applicative (Alternative, (<|>))
import Control.Monad.Error.Class (MonadError, throwError)

-------------------------------------------------------------------------------
-- Type Aliases
-------------------------------------------------------------------------------

-- | The inference monad constraint (no Writer needed!)
type InferC m = (Fresh m, Alternative m, MonadFail m, MonadError String m)

-------------------------------------------------------------------------------
-- Helpers
-------------------------------------------------------------------------------

ensure :: MonadError String m => Bool -> String -> m ()
ensure cond msg = unless cond (throwError msg)

findSol :: MonadError String m => Env -> TyName -> m Ty
findSol env a = case lookupTyVar env a of
  Just (Svar ty) -> return ty
  _ -> throwError $ formatError "findSol: lookupTyVar failed"
         [("Function", "findSol"), ("Type variable", show a)]

-------------------------------------------------------------------------------
-- Polarized Subtyping (ssub)
-------------------------------------------------------------------------------

ssub :: InferC m => (Env, Env) -> Ty -> Polar -> Ty -> m (Derived Env)

-- [S-Int]
ssub (env, senv) TInt p TInt =
  axiomM "[S-Int]" (logSSubFull (env, senv) TInt p TInt senv) senv

-- [S-Bool]
ssub (env, senv) TBool p TBool =
  axiomM "[S-Bool]" (logSSubFull (env, senv) TBool p TBool senv) senv

-- [S-Refl]
ssub (env, senv) (TVar a) p (TVar b) | isUvar (envConcat env senv) a && a == b =
  axiomM "[S-Refl]" (logSSubFull (env, senv) (TVar a) p (TVar b) senv) senv

-- [S-MVar-L] / [S-SVar-L]
ssub (env, senv) (TVar a) Pos tyA = do
  case lookupTyVar (envConcat env senv) a of
    Just Evar ->
      case inst senv a tyA of
        Just newenv ->
          axiomM "[S-MVar-L]" (logSSubFull (env, senv) (TVar a) Pos tyA newenv) newenv
        Nothing -> throwError $ formatError "ssub: inst failed"
                   [("Function", "ssub [S-MVar-L]"), ("Polarity", "Pos")
                   ,("Type variable", show a), ("Type", show tyA)
                   ,("Solution environment", show senv)]
    Just (Svar tyB) -> do
      ensure (tyA `aeq` tyB) $ formatError "ssub: type mismatch (tyA /= tyB)"
              [("Function", "ssub [S-SVar-L]"), ("Polarity", "Pos")
              ,("Type variable", show a), ("Expected type", show tyB)
              ,("Actual type", show tyA), ("Solution environment", show senv)]
      axiomM "[S-SVar-L]" (logSSubFull (env, senv) (TVar a) Pos tyA senv) senv
    _ -> throwError $ formatError "ssub: lookupTyVar failed"
           [("Function", "ssub [S-MVar-L/S-SVar-L]"), ("Polarity", "Pos")
           ,("Type variable", show a), ("Type", show tyA)
           ,("Solution environment", show senv)]

-- [S-MVar-R] / [S-SVar-R]
ssub (env, senv) tyA Neg (TVar a) = do
  case lookupTyVar (envConcat env senv) a of
    Just Evar ->
      case inst senv a tyA of
        Just newenv ->
          axiomM "[S-MVar-R]" (logSSubFull (env, senv) tyA Neg (TVar a) newenv) newenv
        Nothing -> throwError $ formatError "ssub: inst failed"
                   [("Function", "ssub [S-MVar-R]"), ("Polarity", "Neg")
                   ,("Type variable", show a), ("Type", show tyA)
                   ,("Solution environment", show senv)]
    Just (Svar tyB) -> do
      ensure (tyA `aeq` tyB) $ formatError "ssub: type mismatch (tyA /= tyB)"
              [("Function", "ssub [S-SVar-R]"), ("Polarity", "Neg")
              ,("Type variable", show a), ("Expected type", show tyB)
              ,("Actual type", show tyA), ("Solution environment", show senv)]
      axiomM "[S-SVar-R]" (logSSubFull (env, senv) tyA Neg (TVar a) senv) senv
    _ -> throwError $ formatError "ssub: lookupTyVar failed"
           [("Function", "ssub [S-MVar-R/S-SVar-R]"), ("Polarity", "Neg")
           ,("Type variable", show a), ("Type", show tyA)
           ,("Solution environment", show senv)]

-- [S-Arr]
ssub (env, senv) (TArr tyA tyB) p (TArr tyC tyD) =
  deriveWith "[S-Arr]" (logSSubFull (env, senv) (TArr tyA tyB) p (TArr tyC tyD)) $ do
    senv1 <- premise $ ssub (env, senv) tyC (flipPolar p) tyA
    premise $ ssub (env, senv1) tyB p tyD

-- [S-Uncurry]
ssub (env, senv) (TUncurry tsA tyA) p (TUncurry tsC tyD) | length tsA == length tsC =
  deriveWith "[S-Uncurry]" (logSSubFull (env, senv) (TUncurry tsA tyA) p (TUncurry tsC tyD)) $ do
    senv1 <- liftD $ foldM foldArg senv (zip tsA tsC)
    premise $ ssub (env, senv1) tyA p tyD
  where
    foldArg senv' (tyA', tyC') = do
      Derived senv'' _ <- ssub (env, senv') tyC' (flipPolar p) tyA'
      return senv''

-- [S-Forall]
ssub (env, senv) (TForall bdA) p (TForall bdB) = do
  mAB <- unbind2 bdA bdB
  (a, tyA, _, tyB) <- maybe (throwError $ formatError "ssub: unbind2 failed"
                             [("Function", "ssub [S-Forall]"), ("Polarity", show p)
                             ,("Left type", show (TForall bdA))
                             ,("Right type", show (TForall bdB))]) pure mAB
  deriveWith "[S-Forall]" (logSSubFull (env, senv) (TForall bdA) p (TForall bdB)) $ do
    EUvar _ senv' <- premise $ ssub (env, EUvar a senv) tyA p tyB
    return senv'

-- [S-List]
ssub (env, senv) (TList tyA) p (TList tyB) =
  deriveWith "[S-List]" (logSSubFull (env, senv) (TList tyA) p (TList tyB)) $ do
    premise $ ssub (env, senv) tyA p tyB

-- [S-Prod]
ssub (env, senv) (TProd tyA tyB) p (TProd tyC tyD) =
  deriveWith "[S-Prod]" (logSSubFull (env, senv) (TProd tyA tyB) p (TProd tyC tyD)) $ do
    senv1 <- premise $ ssub (env, senv) tyA p tyC
    premise $ ssub (env, senv1) tyB p tyD

-- [S-ST]
ssub (env, senv) (TST tyA tyB) p (TST tyC tyD) =
  deriveWith "[S-ST]" (logSSubFull (env, senv) (TST tyA tyB) p (TST tyC tyD)) $ do
    senv1 <- premise $ ssub (env, senv) tyA p tyC
    senv2 <- premise $ ssub (env, senv1) tyB p tyD
    premise $ ssub (env, senv2) tyC p tyA

-- Fallback
ssub (_, senv) ty1 p ty2 = throwError $ formatError "ssub: unexpected case"
  [("Function", "ssub"), ("Left type", show ty1), ("Polarity", show p)
  ,("Right type", show ty2), ("Solution environment", show senv)]

-------------------------------------------------------------------------------
-- Ground
-------------------------------------------------------------------------------

ground :: (Fresh m, MonadFail m, MonadError String m) => Env -> Ty -> m Ty
ground _ TInt = return TInt
ground _ TBool = return TBool
ground env (TVar k) | isUvar env k = return (TVar k)
ground env (TVar k) = findSol env k
ground env (TArr tyA tyB) = TArr <$> ground env tyA <*> ground env tyB
ground env (TForall bdA) = do
  (a, tyA) <- unbind bdA
  tyA' <- ground (EUvar a env) tyA
  return $ TForall (bind a tyA')
ground env (TUncurry ts tyA) = do
  ts' <- mapM (ground env) ts
  tyA' <- ground env tyA
  return $ TUncurry ts' tyA'
ground env (TList tyA) = TList <$> ground env tyA
ground env (TProd tyA tyB) = TProd <$> ground env tyA <*> ground env tyB
ground env (TST tyA tyB) = TST <$> ground env tyA <*> ground env tyB

-------------------------------------------------------------------------------
-- Uncurry Inference
-------------------------------------------------------------------------------

inferUncurry :: InferC m => (Env, Env) -> Ty -> Tm -> m (Derived (Env, Ty))
inferUncurry (env, senv) tyA e =
  -- Try open first
  (do isOpen (envConcat env senv) tyA
      deriveWith "[UC-Infer]" (\(senv', tyA') -> logInferUncurry (env, senv) tyA e tyA' senv') $ do
        tyA' <- premise $ infer (envConcat env senv) CEmpty e
        senv' <- premise $ ssub (env, senv) tyA' Neg tyA
        return (senv', tyA'))
  <|>
  -- Fallback to closed
  (do closed (envConcat env senv) tyA
      grdA <- ground (envConcat env senv) tyA
      deriveWith "[UC-Check]" (const $ logInferUncurry (env, senv) tyA e tyA senv) $ do
        _ <- premise $ infer (envConcat env senv) (CFullType grdA) e
        return (senv, tyA))

-------------------------------------------------------------------------------
-- Algorithmic Subtyping (sub)
-------------------------------------------------------------------------------

sub :: InferC m => (Env, Env) -> Ty -> Context -> m (Derived (Env, Ty))

-- [S-Empty]
sub (env, senv) tyA CEmpty = do
  closed (envConcat env senv) tyA
  grdA <- ground (envConcat env senv) tyA
  axiomM "[S-Empty]" (logSubFull (env, senv) tyA CEmpty senv grdA) (senv, grdA)

-- [S-Type]
sub (env, senv) tyA (CFullType tyB) =
  deriveWith "[S-Type]" (\(senv', _) -> logSubFull (env, senv) tyA (CFullType tyB) senv' tyB) $ do
    senv' <- premise $ ssub (env, senv) tyA Pos tyB
    return (senv', tyB)

-- [S-Term-Closed] <|> [S-Term-Open]
sub (env, senv) (TArr tyA tyB) (CTerm e h) =
  -- Try closed first
  (do closed (envConcat env senv) tyA
      grdA <- ground (envConcat env senv) tyA
      deriveWith "[S-Term-Closed]" (\(senv', tyD) -> logSubFull (env, senv) (TArr tyA tyB) (CTerm e h) senv' (TArr grdA tyD)) $ do
        tyC <- premise $ infer (envConcat env senv) (CFullType grdA) e
        (senv', tyD) <- premise $ sub (env, senv) tyB h
        return (senv', TArr tyC tyD))
  <|>
  -- Fallback to open
  (do isOpen (envConcat env senv) tyA
      deriveWith "[S-Term-Open]" (\(senv2, tyD) -> logSubFull (env, senv) (TArr tyA tyB) (CTerm e h) senv2 (TArr tyA tyD)) $ do
        tyC <- premise $ infer (envConcat env senv) CEmpty e
        senv1 <- premise $ ssub (env, senv) tyC Neg tyA
        (senv2, tyD) <- premise $ sub (env, senv1) tyB h
        return (senv2, TArr tyC tyD))

-- [S-Arr-UC]
sub (env, senv) (TUncurry tyAs tyB) (CUncurry es h) =
  deriveWith "[S-Arr-UC]" (\(senv'', tyB') -> logSubFull (env, senv) (TUncurry tyAs tyB) (CUncurry es h) senv'' (TUncurry tyAs tyB')) $ do
    (senv', tyAs') <- liftD $ foldM foldFunc (senv, []) (zip tyAs es)
    (senv'', tyB') <- premise $ sub (env, senv') tyB h
    return (senv'', TUncurry tyAs' tyB')
  where
    foldFunc (senv', tyAs') (tyA', e') = do
      Derived (senv'', tyA'') _ <- inferUncurry (env, senv') tyA' e'
      return (senv'', tyAs' ++ [tyA''])

-- [S-Forall-L]
sub (env, senv) (TForall bdA) (CTerm e h) = do
  (a, tyA) <- unbind bdA
  deriveWith "[S-Forall-L]" (\(senv', tyB) -> logSubFull (env, senv) (TForall bdA) (CTerm e h) senv' tyB) $ do
    (ESvar _ _ senv', tyB) <- premise $ sub (env, EEvar a senv) tyA (CTerm e h)
    return (senv', tyB)

-- [S-Forall-L-UC]
sub (env, senv) (TForall bdA) (CUncurry es h) = do
  (a, tyA) <- unbind bdA
  deriveWith "[S-Forall-L-UC]" (\(senv', tyB) -> logSubFull (env, senv) (TForall bdA) (CUncurry es h) senv' tyB) $ do
    (ESvar _ _ senv', tyB) <- premise $ sub (env, EEvar a senv) tyA (CUncurry es h)
    return (senv', tyB)

-- [S-Svar]
sub (env, senv) (TVar k) h | isSvar (envConcat env senv) k = do
  tyA <- findSol (envConcat env senv) k
  deriveWith "[S-Svar]" (\(senv', tyB) -> logSubFull (env, senv) (TVar k) h senv' tyB) $ do
    premise $ sub (env, senv) tyA h

-- [S-Infers]
sub (env, senv) (TVar k) (CTerm e h) | isUvar (envConcat env senv) k =
  deriveWith "[S-Infers]" (\(newenv, tyA) -> logSubFull (env, senv) (TVar k) (CTerm e h) newenv tyA) $ do
    tyA <- premise $ infers (envConcat env senv) (CTerm e h)
    case inst senv k tyA of
      Just newenv -> return (newenv, tyA)
      Nothing -> throwError $ formatError "sub: inst failed"
                 [("Function", "sub [S-Infers]"), ("Type variable", show k)
                 ,("Type", show tyA), ("Term", show e), ("Context", show h)
                 ,("Solution environment", show senv)]

-- [S-Prod-Fst]
sub (env, senv) (TProd tyA tyB) (CFst h) =
  deriveWith "[S-Prod-Fst]" (\(senv', tyA') -> logSubFull (env, senv) (TProd tyA tyB) (CFst h) senv' tyA') $ do
    (senv', tyA') <- premise $ sub (env, senv) tyA h
    return (senv', TProd tyA' tyB)

-- [S-Prod-Snd]
sub (env, senv) (TProd tyA tyB) (CSnd h) =
  deriveWith "[S-Prod-Snd]" (\(senv', tyB') -> logSubFull (env, senv) (TProd tyA tyB) (CSnd h) senv' tyB') $ do
    (senv', tyB') <- premise $ sub (env, senv) tyB h
    return (senv', TProd tyA tyB')

-- Fallback
sub (_, senv) ty ctx = throwError $ formatError "sub: unexpected case"
  [("Function", "sub"), ("Type", show ty), ("Context", show ctx)
  ,("Solution environment", show senv)]

-------------------------------------------------------------------------------
-- Context Inference (infers)
-------------------------------------------------------------------------------

infers :: InferC m => Env -> Context -> m (Derived Ty)

infers env (CFullType tyA) =
  axiomM "[CI-Type]" (logInfersFull env (CFullType tyA) tyA) tyA

infers env (CTerm tm h) =
  deriveWith "[CI-Term]" (logInfersFull env (CTerm tm h)) $ do
    tyA <- premise $ infer env CEmpty tm
    tyB <- premise $ infers env h
    return $ TArr tyA tyB

infers _env ctx = throwError $ formatError "infers: unexpected case"
  [("Function", "infers"), ("Context", show ctx)]

-------------------------------------------------------------------------------
-- Type Inference (infer)
-------------------------------------------------------------------------------

infer :: InferC m => Env -> Context -> Tm -> m (Derived Ty)

-- [Ty-Int]
infer env CEmpty (LitInt n) =
  axiomM "[Ty-Int]" (logInferFull env CEmpty (LitInt n) TInt) TInt

-- [Ty-Bool]
infer env CEmpty (LitBool b) =
  axiomM "[Ty-Bool]" (logInferFull env CEmpty (LitBool b) TBool) TBool

-- [Ty-Var]
infer env CEmpty (Var i) = case lookupTmVar env i of
  Just tyA -> axiomM "[Ty-Var]" (logInferFull env CEmpty (Var i) tyA) tyA
  Nothing -> throwError $ name2String i ++ " is not in the environment"

-- [Ty-Ann]
infer env CEmpty (Ann tm tyA) =
  deriveWith "[Ty-Ann]" (const $ logInferFull env CEmpty (Ann tm tyA) tyA) $ do
    _ <- premise $ infer env (CFullType tyA) tm
    return tyA

-- [Ty-App]
infer env h (App tm1 tm2) =
  deriveWith "[Ty-App]" (logInferFull env h (App tm1 tm2)) $ do
    TArr _ ty <- premise $ infer env (CTerm tm2 h) tm1
    return ty

-- [Ty-App-UC]
infer env h (AppUncurry tm1 tm2s) =
  deriveWith "[Ty-App-UC]" (logInferFull env h (AppUncurry tm1 tm2s)) $ do
    TUncurry _ ty <- premise $ infer env (CUncurry tm2s h) tm1
    return ty

-- [Ty-Abs1]
infer env (CFullType (TArr tyA tyB)) (Abs bdTm) = do
  (x, tm) <- unbind bdTm
  deriveWith "[Ty-Abs1]" (logInferFull env (CFullType (TArr tyA tyB)) (Abs bdTm)) $ do
    tyC <- premise $ infer (ETrm x tyA env) (CFullType tyB) tm
    return $ TArr tyA tyC

-- [Ty-Abs2]
infer env (CTerm tm2 h) (Abs bdTm) = do
  (x, tm) <- unbind bdTm
  deriveWith "[Ty-Abs2]" (logInferFull env (CTerm tm2 h) (Abs bdTm)) $ do
    tyA <- premise $ infer env CEmpty tm2
    tyB <- premise $ infer (ETrm x tyA env) h tm
    return $ TArr tyA tyB

-- [Ty-AbsAnn1]
infer env (CFullType (TArr tyA tyB)) (AbsAnn bdTm) = do
  ((x, Embed tyA'), tm) <- unbind bdTm
  guard (tyA `aeq` tyA')
  deriveWith "[Ty-AbsAnn1]" (const $ logInferFull env (CFullType (TArr tyA tyB)) (AbsAnn bdTm) (TArr tyA tyB)) $ do
    _ <- premise $ infer (ETrm x tyA env) (CFullType tyB) tm
    return $ TArr tyA tyB

-- [Ty-AbsAnn2]
infer env (CTerm tm2 h) (AbsAnn bdTm) = do
  ((x, Embed tyA), tm) <- unbind bdTm
  deriveWith "[Ty-AbsAnn2]" (logInferFull env (CTerm tm2 h) (AbsAnn bdTm)) $ do
    _ <- premise $ infer env (CFullType tyA) tm2
    tyB <- premise $ infer (ETrm x tyA env) h tm
    return $ TArr tyA tyB

-- [Ty-AbsAnn3]
infer env CEmpty (AbsAnn bdTm) = do
  ((x, Embed tyA), tm) <- unbind bdTm
  deriveWith "[Ty-AbsAnn3]" (logInferFull env CEmpty (AbsAnn bdTm)) $ do
    tyB <- premise $ infer (ETrm x tyA env) CEmpty tm
    return $ TArr tyA tyB

-- [Ty-AbsAnn-UC1]
infer env (CFullType (TUncurry tyAs tyB)) (AbsUncurryAnn bdTm) = do
  (xs_tyAs, tm) <- unbind bdTm
  let xs = [x_A | (x_A, _) <- xs_tyAs]
      tyAs' = [ty_A | (_, Embed ty_A) <- xs_tyAs]
  guard $ all (uncurry aeq) (zip tyAs tyAs')
  deriveWith "[Ty-AbsAnn-UC1]" (const $ logInferFull env (CFullType (TUncurry tyAs tyB)) (AbsUncurryAnn bdTm) (TUncurry tyAs tyB)) $ do
    _ <- premise $ infer (foldl (\env' (x, tyA) -> ETrm x tyA env') env (zip xs tyAs')) (CFullType tyB) tm
    return $ TUncurry tyAs tyB

-- [Ty-AbsAnn-UC2]
infer env (CUncurry tm2s h) (AbsUncurryAnn bdTm) = do
  (xs_tyAs, tm) <- unbind bdTm
  let xs = [x_A | (x_A, _) <- xs_tyAs]
      tyAs = [ty_A | (_, Embed ty_A) <- xs_tyAs]
  deriveWith "[Ty-AbsAnn-UC2]" (logInferFull env (CUncurry tm2s h) (AbsUncurryAnn bdTm)) $ do
    _ <- liftD $ mapM (\(tyA, tm2) -> infer env (CFullType tyA) tm2) (zip tyAs tm2s)
    tyB <- premise $ infer (foldl (\env' (x, tyA) -> ETrm x tyA env') env (zip xs tyAs)) h tm
    return $ TUncurry tyAs tyB

-- [Ty-AbsAnn-UC3]
infer env CEmpty (AbsUncurryAnn bdTm) = do
  (xs_tyAs, tm) <- unbind bdTm
  let xs = [x_A | (x_A, _) <- xs_tyAs]
      tyAs = [ty_A | (_, Embed ty_A) <- xs_tyAs]
  deriveWith "[Ty-AbsAnn-UC3]" (logInferFull env CEmpty (AbsUncurryAnn bdTm)) $ do
    tyB <- premise $ infer (foldl (\env' (x, tyA) -> ETrm x tyA env') env (zip xs tyAs)) CEmpty tm
    return $ TUncurry tyAs tyB

-- [Ty-Abs-UC1]
infer env (CFullType (TUncurry ts tyB)) (AbsUncurry bdTm) = do
  (xs, tm) <- unbind bdTm
  deriveWith "[Ty-Abs-UC1]" (logInferFull env (CFullType (TUncurry ts tyB)) (AbsUncurry bdTm)) $ do
    tyC <- premise $ infer (foldl (\env' (x, tyA) -> ETrm x tyA env') env (zip xs ts)) (CFullType tyB) tm
    return $ TUncurry ts tyC

-- [Ty-Abs-UC2]
infer env (CUncurry tm2s h) (AbsUncurry bd) = do
  (xs, tm) <- unbind bd
  deriveWith "[Ty-Abs-UC2]" (logInferFull env (CUncurry tm2s h) (AbsUncurry bd)) $ do
    tyAs <- liftD $ mapM (fmap result . infer env CEmpty) tm2s
    tyB <- premise $ infer (foldl (\env' (x, tyA) -> ETrm x tyA env') env (zip xs tyAs)) h tm
    return $ TUncurry tyAs tyB

-- [Ty-TAbs]
infer env CEmpty (TAbs bdTm) = do
  (a, tm) <- unbind bdTm
  deriveWith "[Ty-TAbs]" (logInferFull env CEmpty (TAbs bdTm)) $ do
    tyA <- premise $ infer (EUvar a env) CEmpty tm
    return $ TForall (bind a tyA)

-- [Ty-TAbs-Chk]
infer env (CFullType (TForall bdTy)) (TAbs bdTm) = do
  Just (a, tyA, _, tm) <- unbind2 bdTy bdTm
  deriveWith "[Ty-TAbs-Chk]" (const $ logInferFull env (CFullType (TForall bdTy)) (TAbs bdTm) (TForall bdTy)) $ do
    _ <- premise $ infer (EUvar a env) (CFullType tyA) tm
    return $ TForall bdTy

-- [Ty-TApp]
infer env h (TApp tm tyA) =
  deriveWith "[Ty-TApp]" (logInferFull env h (TApp tm tyA)) $ do
    TForall bdTy <- premise $ infer env CEmpty tm
    (a, tyB) <- liftD $ unbind bdTy
    (EEmpty, tyC) <- premise $ sub (env, EEmpty) (subst a tyA tyB) h
    return tyC

-- [Ty-Pair1]
infer env CEmpty (Pair tm1 tm2) =
  deriveWith "[Ty-Pair1]" (logInferFull env CEmpty (Pair tm1 tm2)) $ do
    tyA <- premise $ infer env CEmpty tm1
    tyB <- premise $ infer env CEmpty tm2
    return $ TProd tyA tyB

-- [Ty-Pair2]
infer env (CFullType (TProd tyA tyB)) (Pair tm1 tm2) =
  deriveWith "[Ty-Pair2]" (logInferFull env (CFullType (TProd tyA tyB)) (Pair tm1 tm2)) $ do
    tyA' <- premise $ infer env (CFullType tyA) tm1
    tyB' <- premise $ infer env (CFullType tyB) tm2
    return $ TProd tyA' tyB'

-- [Ty-Fst]
infer env h (Fst tm) =
  deriveWith "[Ty-Fst]" (logInferFull env h (Fst tm)) $ do
    ty <- premise $ infer env (CFst h) tm
    case ty of
      TProd tyA _ -> return tyA
      _ -> throwError $ formatError "infer: Fst expected TProd but got different type"
             [("Function", "infer [Ty-Fst]"), ("Term", show (Fst tm))
             ,("Context", show h), ("Expected type", "TProd tyA tyB")
             ,("Actual type", show ty)]

-- [Ty-Snd]
infer env h (Snd tm) =
  deriveWith "[Ty-Snd]" (logInferFull env h (Snd tm)) $ do
    ty <- premise $ infer env (CSnd h) tm
    case ty of
      TProd _ tyB -> return tyB
      _ -> throwError $ formatError "infer: Snd expected TProd but got different type"
             [("Function", "infer [Ty-Snd]"), ("Term", show (Snd tm))
             ,("Context", show h), ("Expected type", "TProd tyA tyB")
             ,("Actual type", show ty)]

-- [Ty-Pair-Fst]
infer env (CFst h) (Pair tm1 tm2) =
  deriveWith "[Ty-Pair-Fst]" (logInferFull env (CFst h) (Pair tm1 tm2)) $ do
    tyA <- premise $ infer env h tm1
    tyB <- premise $ infer env CEmpty tm2
    return $ TProd tyA tyB

-- [Ty-Pair-Snd]
infer env (CSnd h) (Pair tm1 tm2) =
  deriveWith "[Ty-Pair-Snd]" (logInferFull env (CSnd h) (Pair tm1 tm2)) $ do
    tyA <- premise $ infer env CEmpty tm1
    tyB <- premise $ infer env h tm2
    return $ TProd tyA tyB

-- [Ty-Sub] - generic consumer with non-empty context
infer env h g | genericConsumer g && nonEmptyContext h =
  deriveWith "[Ty-Sub]" (logInferFull env h g) $ do
    tyA <- premise $ infer env CEmpty g
    (EEmpty, tyB) <- premise $ sub (env, EEmpty) tyA h
    return tyB

-- [Ty-Nil-Chk]
infer env (CFullType (TList tyA)) Nil =
  axiomM "[Ty-Nil-Chk]" (logInferFull env (CFullType (TList tyA)) Nil (TList tyA)) (TList tyA)

-- [Ty-Nil]
infer env CEmpty Nil = do
  let tyNil = TForall (bind (s2n "a") (TList (TVar (s2n "a"))))
  axiomM "[Ty-Nil]" (logInferFull env CEmpty Nil tyNil) tyNil

-- Fallback
infer _env ctx tm = throwError $ formatError "infer: unexpected case"
  [("Function", "infer"), ("Term", show tm), ("Context", show ctx)]
