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
ssub envs@(_, senv) TInt p TInt =
  axiomM "[S-Int]" (logSSubFull envs TInt p TInt senv) senv

-- [S-Bool]
ssub envs@(_, senv) TBool p TBool =
  axiomM "[S-Bool]" (logSSubFull envs TBool p TBool senv) senv

-- [S-Refl]
ssub envs@(env, senv) ty1@(TVar a) p ty2@(TVar b) | isUvar (envConcat env senv) a && a == b =
  axiomM "[S-Refl]" (logSSubFull envs ty1 p ty2 senv) senv

-- [S-MVar-L] / [S-SVar-L]
ssub envs@(env, senv) ty1@(TVar a) Pos tyA = do
  case lookupTyVar (envConcat env senv) a of
    Just Evar ->
      case inst senv a tyA of
        Just newenv ->
          axiomM "[S-MVar-L]" (logSSubFull envs ty1 Pos tyA newenv) newenv
        Nothing -> throwError $ formatError "ssub: inst failed"
                   [("Function", "ssub [S-MVar-L]"), ("Polarity", "Pos")
                   ,("Type variable", show a), ("Type", show tyA)
                   ,("Solution environment", show senv)]
    Just (Svar tyB) -> do
      ensure (tyA `aeq` tyB) $ formatError "ssub: type mismatch (tyA /= tyB)"
              [("Function", "ssub [S-SVar-L]"), ("Polarity", "Pos")
              ,("Type variable", show a), ("Expected type", show tyB)
              ,("Actual type", show tyA), ("Solution environment", show senv)]
      axiomM "[S-SVar-L]" (logSSubFull envs ty1 Pos tyA senv) senv
    _ -> throwError $ formatError "ssub: lookupTyVar failed"
           [("Function", "ssub [S-MVar-L/S-SVar-L]"), ("Polarity", "Pos")
           ,("Type variable", show a), ("Type", show tyA)
           ,("Solution environment", show senv)]

-- [S-MVar-R] / [S-SVar-R]
ssub envs@(env, senv) tyA Neg ty2@(TVar a) = do
  case lookupTyVar (envConcat env senv) a of
    Just Evar ->
      case inst senv a tyA of
        Just newenv ->
          axiomM "[S-MVar-R]" (logSSubFull envs tyA Neg ty2 newenv) newenv
        Nothing -> throwError $ formatError "ssub: inst failed"
                   [("Function", "ssub [S-MVar-R]"), ("Polarity", "Neg")
                   ,("Type variable", show a), ("Type", show tyA)
                   ,("Solution environment", show senv)]
    Just (Svar tyB) -> do
      ensure (tyA `aeq` tyB) $ formatError "ssub: type mismatch (tyA /= tyB)"
              [("Function", "ssub [S-SVar-R]"), ("Polarity", "Neg")
              ,("Type variable", show a), ("Expected type", show tyB)
              ,("Actual type", show tyA), ("Solution environment", show senv)]
      axiomM "[S-SVar-R]" (logSSubFull envs tyA Neg ty2 senv) senv
    _ -> throwError $ formatError "ssub: lookupTyVar failed"
           [("Function", "ssub [S-MVar-R/S-SVar-R]"), ("Polarity", "Neg")
           ,("Type variable", show a), ("Type", show tyA)
           ,("Solution environment", show senv)]

-- [S-Arr]
ssub envs@(env, senv) ty1@(TArr tyA tyB) p ty2@(TArr tyC tyD) =
  deriveWith "[S-Arr]" (logSSubFull envs ty1 p ty2) $ do
    senv1 <- premise $ ssub (env, senv) tyC (flipPolar p) tyA
    premise $ ssub (env, senv1) tyB p tyD

-- [S-Uncurry]
ssub envs@(env, senv) ty1@(TUncurry tsA tyA) p ty2@(TUncurry tsC tyD) | length tsA == length tsC =
  deriveWith "[S-Uncurry]" (logSSubFull envs ty1 p ty2) $ do
    senv1 <- liftD $ foldM foldArg senv (zip tsA tsC)
    premise $ ssub (env, senv1) tyA p tyD
  where
    foldArg senv' (tyA', tyC') = do
      Derived senv'' _ <- ssub (env, senv') tyC' (flipPolar p) tyA'
      return senv''

-- [S-Forall]
ssub envs@(env, senv) ty1@(TForall bdA) p ty2@(TForall bdB) = do
  mAB <- unbind2 bdA bdB
  (a, tyA, _, tyB) <- maybe (throwError $ formatError "ssub: unbind2 failed"
                             [("Function", "ssub [S-Forall]"), ("Polarity", show p)
                             ,("Left type", show ty1), ("Right type", show ty2)]) pure mAB
  deriveWith "[S-Forall]" (logSSubFull envs ty1 p ty2) $ do
    EUvar _ senv' <- premise $ ssub (env, EUvar a senv) tyA p tyB
    return senv'

-- [S-List]
ssub envs@(env, senv) ty1@(TList tyA) p ty2@(TList tyB) =
  deriveWith "[S-List]" (logSSubFull envs ty1 p ty2) $ do
    premise $ ssub (env, senv) tyA p tyB

-- [S-Prod]
ssub envs@(env, senv) ty1@(TProd tyA tyB) p ty2@(TProd tyC tyD) =
  deriveWith "[S-Prod]" (logSSubFull envs ty1 p ty2) $ do
    senv1 <- premise $ ssub (env, senv) tyA p tyC
    premise $ ssub (env, senv1) tyB p tyD

-- [S-ST]
ssub envs@(env, senv) ty1@(TST tyA tyB) p ty2@(TST tyC tyD) =
  deriveWith "[S-ST]" (logSSubFull envs ty1 p ty2) $ do
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
inferUncurry envs@(env, senv) tyA e =
  -- Try open first
  (do isOpen (envConcat env senv) tyA
      deriveWith "[UC-Infer]" (\(senv', tyA') -> logInferUncurry envs tyA e tyA' senv') $ do
        tyA' <- premise $ infer (envConcat env senv) CEmpty e
        senv' <- premise $ ssub (env, senv) tyA' Neg tyA
        return (senv', tyA'))
  <|>
  -- Fallback to closed
  (do closed (envConcat env senv) tyA
      grdA <- ground (envConcat env senv) tyA
      deriveWith "[UC-Check]" (const $ logInferUncurry envs tyA e tyA senv) $ do
        _ <- premise $ infer (envConcat env senv) (CFullType grdA) e
        return (senv, tyA))

-------------------------------------------------------------------------------
-- Algorithmic Subtyping (sub)
-------------------------------------------------------------------------------

sub :: InferC m => (Env, Env) -> Ty -> Context -> m (Derived (Env, Ty))

-- [S-Empty]
sub envs@(env, senv) tyA CEmpty = do
  closed (envConcat env senv) tyA
  grdA <- ground (envConcat env senv) tyA
  axiomM "[S-Empty]" (logSubFull envs tyA CEmpty senv grdA) (senv, grdA)

-- [S-Type]
sub envs@(env, senv) tyA ctx@(CFullType tyB) =
  deriveWith "[S-Type]" (\(senv', _) -> logSubFull envs tyA ctx senv' tyB) $ do
    senv' <- premise $ ssub (env, senv) tyA Pos tyB
    return (senv', tyB)

-- [S-Term-Closed] <|> [S-Term-Open]
sub envs@(env, senv) ty@(TArr tyA tyB) ctx@(CTerm e h) =
  -- Try closed first
  (do closed (envConcat env senv) tyA
      grdA <- ground (envConcat env senv) tyA
      deriveWith "[S-Term-Closed]" (\(senv', tyOut) -> logSubFull envs ty ctx senv' tyOut) $ do
        tyC <- premise $ infer (envConcat env senv) (CFullType grdA) e
        (senv', tyD) <- premise $ sub (env, senv) tyB h
        return (senv', TArr tyC tyD))
  <|>
  -- Fallback to open
  (do isOpen (envConcat env senv) tyA
      deriveWith "[S-Term-Open]" (\(senv2, tyOut) -> logSubFull envs ty ctx senv2 tyOut) $ do
        tyC <- premise $ infer (envConcat env senv) CEmpty e
        senv1 <- premise $ ssub (env, senv) tyC Neg tyA
        (senv2, tyD) <- premise $ sub (env, senv1) tyB h
        return (senv2, TArr tyC tyD))

-- [S-Arr-UC]
sub envs@(env, senv) ty@(TUncurry tyAs tyB) ctx@(CUncurry es h) =
  deriveWith "[S-Arr-UC]" (\(senv'', tyOut) -> logSubFull envs ty ctx senv'' tyOut) $ do
    (senv', tyAs') <- liftD $ foldM foldFunc (senv, []) (zip tyAs es)
    (senv'', tyB') <- premise $ sub (env, senv') tyB h
    return (senv'', TUncurry tyAs' tyB')
  where
    foldFunc (senv', tyAs') (tyA', e') = do
      Derived (senv'', tyA'') _ <- inferUncurry (env, senv') tyA' e'
      return (senv'', tyAs' ++ [tyA''])

-- [S-Forall-L]
sub envs@(env, senv) ty@(TForall bdA) ctx@(CTerm e h) = do
  (a, tyA) <- unbind bdA
  deriveWith "[S-Forall-L]" (\(senv', tyB) -> logSubFull envs ty ctx senv' tyB) $ do
    (ESvar _ _ senv', tyB) <- premise $ sub (env, EEvar a senv) tyA (CTerm e h)
    return (senv', tyB)

-- [S-Forall-L-UC]
sub envs@(env, senv) ty@(TForall bdA) ctx@(CUncurry es h) = do
  (a, tyA) <- unbind bdA
  deriveWith "[S-Forall-L-UC]" (\(senv', tyB) -> logSubFull envs ty ctx senv' tyB) $ do
    (ESvar _ _ senv', tyB) <- premise $ sub (env, EEvar a senv) tyA (CUncurry es h)
    return (senv', tyB)

-- [S-Svar]
sub envs@(env, senv) ty@(TVar k) ctx | isSvar (envConcat env senv) k = do
  tyA <- findSol (envConcat env senv) k
  deriveWith "[S-Svar]" (\(senv', tyB) -> logSubFull envs ty ctx senv' tyB) $ do
    premise $ sub (env, senv) tyA ctx

-- [S-Infers]
sub envs@(env, senv) ty@(TVar k) ctx@(CTerm e h) | isUvar (envConcat env senv) k =
  deriveWith "[S-Infers]" (\(newenv, tyA) -> logSubFull envs ty ctx newenv tyA) $ do
    tyA <- premise $ infers (envConcat env senv) (CTerm e h)
    case inst senv k tyA of
      Just newenv -> return (newenv, tyA)
      Nothing -> throwError $ formatError "sub: inst failed"
                 [("Function", "sub [S-Infers]"), ("Type variable", show k)
                 ,("Type", show tyA), ("Term", show e), ("Context", show h)
                 ,("Solution environment", show senv)]

-- [S-Prod-Fst]
sub envs@(env, senv) ty@(TProd tyA tyB) ctx@(CFst h) =
  deriveWith "[S-Prod-Fst]" (\(senv', tyOut) -> logSubFull envs ty ctx senv' tyOut) $ do
    (senv', tyA') <- premise $ sub (env, senv) tyA h
    return (senv', TProd tyA' tyB)

-- [S-Prod-Snd]
sub envs@(env, senv) ty@(TProd tyA tyB) ctx@(CSnd h) =
  deriveWith "[S-Prod-Snd]" (\(senv', tyOut) -> logSubFull envs ty ctx senv' tyOut) $ do
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

infers env ctx@(CFullType tyA) =
  axiomM "[CI-Type]" (logInfersFull env ctx tyA) tyA

infers env ctx@(CTerm tm h) =
  deriveWith "[CI-Term]" (logInfersFull env ctx) $ do
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
infer env ctx@CEmpty tm@(LitInt _) =
  axiomM "[Ty-Int]" (logInferFull env ctx tm TInt) TInt

-- [Ty-Bool]
infer env ctx@CEmpty tm@(LitBool _) =
  axiomM "[Ty-Bool]" (logInferFull env ctx tm TBool) TBool

-- [Ty-Var]
infer env ctx@CEmpty tm@(Var i) = case lookupTmVar env i of
  Just tyA -> axiomM "[Ty-Var]" (logInferFull env ctx tm tyA) tyA
  Nothing -> throwError $ name2String i ++ " is not in the environment"

-- [Ty-Ann]
infer env ctx@CEmpty tm@(Ann e tyA) =
  deriveWith "[Ty-Ann]" (const $ logInferFull env ctx tm tyA) $ do
    _ <- premise $ infer env (CFullType tyA) e
    return tyA

-- [Ty-App]
infer env ctx tm@(App tm1 tm2) =
  deriveWith "[Ty-App]" (logInferFull env ctx tm) $ do
    TArr _ ty <- premise $ infer env (CTerm tm2 ctx) tm1
    return ty

-- [Ty-App-UC]
infer env ctx tm@(AppUncurry tm1 tm2s) =
  deriveWith "[Ty-App-UC]" (logInferFull env ctx tm) $ do
    TUncurry _ ty <- premise $ infer env (CUncurry tm2s ctx) tm1
    return ty

-- [Ty-Abs1]
infer env ctx@(CFullType (TArr tyA tyB)) tm@(Abs bdTm) = do
  (x, body) <- unbind bdTm
  deriveWith "[Ty-Abs1]" (logInferFull env ctx tm) $ do
    tyC <- premise $ infer (ETrm x tyA env) (CFullType tyB) body
    return $ TArr tyA tyC

-- [Ty-Abs2]
infer env ctx@(CTerm tm2 h) tm@(Abs bdTm) = do
  (x, body) <- unbind bdTm
  deriveWith "[Ty-Abs2]" (logInferFull env ctx tm) $ do
    tyA <- premise $ infer env CEmpty tm2
    tyB <- premise $ infer (ETrm x tyA env) h body
    return $ TArr tyA tyB

-- [Ty-AbsAnn1]
infer env ctx@(CFullType tyArr@(TArr tyA tyB)) tm@(AbsAnn bdTm) = do
  ((x, Embed tyA'), body) <- unbind bdTm
  guard (tyA `aeq` tyA')
  deriveWith "[Ty-AbsAnn1]" (const $ logInferFull env ctx tm tyArr) $ do
    _ <- premise $ infer (ETrm x tyA env) (CFullType tyB) body
    return tyArr

-- [Ty-AbsAnn2]
infer env ctx@(CTerm tm2 h) tm@(AbsAnn bdTm) = do
  ((x, Embed tyA), body) <- unbind bdTm
  deriveWith "[Ty-AbsAnn2]" (logInferFull env ctx tm) $ do
    _ <- premise $ infer env (CFullType tyA) tm2
    tyB <- premise $ infer (ETrm x tyA env) h body
    return $ TArr tyA tyB

-- [Ty-AbsAnn3]
infer env ctx@CEmpty tm@(AbsAnn bdTm) = do
  ((x, Embed tyA), body) <- unbind bdTm
  deriveWith "[Ty-AbsAnn3]" (logInferFull env ctx tm) $ do
    tyB <- premise $ infer (ETrm x tyA env) CEmpty body
    return $ TArr tyA tyB

-- [Ty-AbsAnn-UC1]
infer env ctx@(CFullType tyUC@(TUncurry tyAs tyB)) tm@(AbsUncurryAnn bdTm) = do
  (xs_tyAs, body) <- unbind bdTm
  let xs = [x | (x, _) <- xs_tyAs]
      tyAs' = [ty | (_, Embed ty) <- xs_tyAs]
  guard $ all (uncurry aeq) (zip tyAs tyAs')
  deriveWith "[Ty-AbsAnn-UC1]" (const $ logInferFull env ctx tm tyUC) $ do
    _ <- premise $ infer (foldl (\env' (x, tyA) -> ETrm x tyA env') env (zip xs tyAs')) (CFullType tyB) body
    return tyUC

-- [Ty-AbsAnn-UC2]
infer env ctx@(CUncurry tm2s h) tm@(AbsUncurryAnn bdTm) = do
  (xs_tyAs, body) <- unbind bdTm
  let xs = [x | (x, _) <- xs_tyAs]
      tyAs = [ty | (_, Embed ty) <- xs_tyAs]
  deriveWith "[Ty-AbsAnn-UC2]" (logInferFull env ctx tm) $ do
    _ <- liftD $ mapM (\(tyA, e) -> infer env (CFullType tyA) e) (zip tyAs tm2s)
    tyB <- premise $ infer (foldl (\env' (x, tyA) -> ETrm x tyA env') env (zip xs tyAs)) h body
    return $ TUncurry tyAs tyB

-- [Ty-AbsAnn-UC3]
infer env ctx@CEmpty tm@(AbsUncurryAnn bdTm) = do
  (xs_tyAs, body) <- unbind bdTm
  let xs = [x | (x, _) <- xs_tyAs]
      tyAs = [ty | (_, Embed ty) <- xs_tyAs]
  deriveWith "[Ty-AbsAnn-UC3]" (logInferFull env ctx tm) $ do
    tyB <- premise $ infer (foldl (\env' (x, tyA) -> ETrm x tyA env') env (zip xs tyAs)) CEmpty body
    return $ TUncurry tyAs tyB

-- [Ty-Abs-UC1]
infer env ctx@(CFullType (TUncurry ts tyB)) tm@(AbsUncurry bdTm) = do
  (xs, body) <- unbind bdTm
  deriveWith "[Ty-Abs-UC1]" (logInferFull env ctx tm) $ do
    tyC <- premise $ infer (foldl (\env' (x, tyA) -> ETrm x tyA env') env (zip xs ts)) (CFullType tyB) body
    return $ TUncurry ts tyC

-- [Ty-Abs-UC2]
infer env ctx@(CUncurry tm2s h) tm@(AbsUncurry bd) = do
  (xs, body) <- unbind bd
  deriveWith "[Ty-Abs-UC2]" (logInferFull env ctx tm) $ do
    tyAs <- liftD $ mapM (fmap result . infer env CEmpty) tm2s
    tyB <- premise $ infer (foldl (\env' (x, tyA) -> ETrm x tyA env') env (zip xs tyAs)) h body
    return $ TUncurry tyAs tyB

-- [Ty-TAbs]
infer env ctx@CEmpty tm@(TAbs bdTm) = do
  (a, body) <- unbind bdTm
  deriveWith "[Ty-TAbs]" (logInferFull env ctx tm) $ do
    tyA <- premise $ infer (EUvar a env) CEmpty body
    return $ TForall (bind a tyA)

-- [Ty-TAbs-Chk]
infer env ctx@(CFullType tyForall@(TForall bdTy)) tm@(TAbs bdTm) = do
  Just (a, tyA, _, body) <- unbind2 bdTy bdTm
  deriveWith "[Ty-TAbs-Chk]" (const $ logInferFull env ctx tm tyForall) $ do
    _ <- premise $ infer (EUvar a env) (CFullType tyA) body
    return tyForall

-- [Ty-TApp]
infer env ctx tm@(TApp e tyA) =
  deriveWith "[Ty-TApp]" (logInferFull env ctx tm) $ do
    TForall bdTy <- premise $ infer env CEmpty e
    (a, tyB) <- liftD $ unbind bdTy
    (EEmpty, tyC) <- premise $ sub (env, EEmpty) (subst a tyA tyB) ctx
    return tyC

-- [Ty-Pair1]
infer env ctx@CEmpty tm@(Pair tm1 tm2) =
  deriveWith "[Ty-Pair1]" (logInferFull env ctx tm) $ do
    tyA <- premise $ infer env CEmpty tm1
    tyB <- premise $ infer env CEmpty tm2
    return $ TProd tyA tyB

-- [Ty-Pair2]
infer env ctx@(CFullType (TProd tyA tyB)) tm@(Pair tm1 tm2) =
  deriveWith "[Ty-Pair2]" (logInferFull env ctx tm) $ do
    tyA' <- premise $ infer env (CFullType tyA) tm1
    tyB' <- premise $ infer env (CFullType tyB) tm2
    return $ TProd tyA' tyB'

-- [Ty-Fst]
infer env ctx tm@(Fst e) =
  deriveWith "[Ty-Fst]" (logInferFull env ctx tm) $ do
    ty <- premise $ infer env (CFst ctx) e
    case ty of
      TProd tyA _ -> return tyA
      _ -> throwError $ formatError "infer: Fst expected TProd"
             [("Function", "infer [Ty-Fst]"), ("Term", show tm)
             ,("Context", show ctx), ("Actual type", show ty)]

-- [Ty-Snd]
infer env ctx tm@(Snd e) =
  deriveWith "[Ty-Snd]" (logInferFull env ctx tm) $ do
    ty <- premise $ infer env (CSnd ctx) e
    case ty of
      TProd _ tyB -> return tyB
      _ -> throwError $ formatError "infer: Snd expected TProd"
             [("Function", "infer [Ty-Snd]"), ("Term", show tm)
             ,("Context", show ctx), ("Actual type", show ty)]

-- [Ty-Pair-Fst]
infer env ctx@(CFst h) tm@(Pair tm1 tm2) =
  deriveWith "[Ty-Pair-Fst]" (logInferFull env ctx tm) $ do
    tyA <- premise $ infer env h tm1
    tyB <- premise $ infer env CEmpty tm2
    return $ TProd tyA tyB

-- [Ty-Pair-Snd]
infer env ctx@(CSnd h) tm@(Pair tm1 tm2) =
  deriveWith "[Ty-Pair-Snd]" (logInferFull env ctx tm) $ do
    tyA <- premise $ infer env CEmpty tm1
    tyB <- premise $ infer env h tm2
    return $ TProd tyA tyB

-- [Ty-Sub] - generic consumer with non-empty context
infer env ctx tm | genericConsumer tm && nonEmptyContext ctx =
  deriveWith "[Ty-Sub]" (logInferFull env ctx tm) $ do
    tyA <- premise $ infer env CEmpty tm
    (EEmpty, tyB) <- premise $ sub (env, EEmpty) tyA ctx
    return tyB

-- [Ty-Nil-Chk]
infer env ctx@(CFullType tyList@(TList _)) tm@Nil =
  axiomM "[Ty-Nil-Chk]" (logInferFull env ctx tm tyList) tyList

-- [Ty-Nil]
infer env ctx@CEmpty tm@Nil = do
  let tyNil = TForall (bind (s2n "a") (TList (TVar (s2n "a"))))
  axiomM "[Ty-Nil]" (logInferFull env ctx tm tyNil) tyNil

-- Fallback
infer _env ctx tm = throwError $ formatError "infer: unexpected case"
  [("Function", "infer"), ("Term", show tm), ("Context", show ctx)]
