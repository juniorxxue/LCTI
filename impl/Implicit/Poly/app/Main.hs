{-# LANGUAGE MultiWayIf, LambdaCase, RankNTypes, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant multi-way if" #-}
{-# HLINT ignore "Use if" #-}
module Main where
import Control.Monad.Writer
import Control.Monad (forM_)
import Debug.Trace
import System.IO (hFlush, stdout)

import Syntax
import DeBruijn
import Counter
import Log

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
findSol (ESvar ty _) 0 = return ty
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
ssubP (env, senv) (TVar a) tyA | isEvar senv a = do
  case inst senv a tyA of
    Just newenv -> do
      tell ["[S-Ex-L] " ++ logSSubFull (env, senv) (TVar a) tyA newenv]
      return newenv
    Nothing -> lift Nothing
ssubP (env, senv) (TVar a) tyA = do
  tyB <- findSol senv a
  if tyA == tyB then do
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
ssubN (env, senv) tyA (TVar a) | isEvar senv a = do
  case inst senv a tyA of
    Just newenv -> do
      tell ["[S-Ex-R] " ++ logSSubFull (env, senv) (TVar a) tyA newenv]
      return newenv
    Nothing -> lift Nothing
ssubN (env, senv) tyA (TVar a) = do
  tyB <- findSol senv a
  if tyA == tyB then do
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
  ((ESvar _ senv' , tyB), _log1) <- peek $ sub (env, EEvar senv) tyA (shiftTyContext0 (CTerm e h))
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
infer _ _ _ = lift Nothing


idTyp :: Typ
idTyp = TForall (TArr (TVar 0) (TVar 0))

idTrm :: Trm
idTrm = TAbs (Ann (Abs (Var 0)) (TArr (TVar 0) (TVar 0)))

idTrm' :: Typ -> Trm
idTrm' ty = Ann (Abs (Var 0)) (TArr ty ty)

cons :: Trm -> Trm -> Trm
cons = App . App Cons

pair :: Trm -> Trm -> Trm
pair = App . App Pair

chooseTyp :: Typ
chooseTyp = TForall $ TArr (TVar 0) $ TArr (TVar 0) (TVar 0)

main :: IO ()
main = do
  -- print idTyp
  let
      -- /\a. (\x. x : a -> a)
      ex_id = infer EEmpty CEmpty idTrm
      -- id 1
      ex_id1 = infer EEmpty CEmpty (App idTrm (LitInt 1))
      -- id @Int
      ex_idInt = infer EEmpty CEmpty (TApp idTrm TInt)
      -- id @Int 1
      ex_idInt1 = infer EEmpty CEmpty (App (TApp idTrm TInt) (LitInt 42))
      -- f : forall a. a -> a
      -- f 1
      ex_f1 = infer (ETrm (TForall (TArr (TVar 0) (TVar 0))) EEmpty) CEmpty (App (Var 0) (LitInt 42))
      -- g : forall a. (Int -> a) -> a
      -- g (\x. x)
      ex_gid = infer (ETrm (TForall (TArr (TArr TInt (TVar 0)) (TVar 0))) EEmpty) CEmpty (App (Var 0) (Abs (Var 0)))
      -- test order-insensitive
      -- g : forall a. (a -> a) -> a -> a
      -- g (\x. x) 1
      ex_gid1 = infer (ETrm (TForall (TArr (TArr (TVar 0) (TVar 0)) (TArr (TVar 0) (TVar 0)))) EEmpty) CEmpty (App (App (Var 0) (Abs (Var 0))) (LitInt 1))
      -- spine-local
      -- g : forall a. b. (a -> a) -> b -> ((a -> a) -> b)
      -- (g (\x. x) (lit 1)) : ((Int -> Int) -> Int))
      ex_g2 = infer (ETrm (TForall (TForall (TArr (TArr (TVar 1) (TVar 1))
                                                  (TArr (TVar 0)
                                                        (TArr (TArr (TVar 1) (TVar 1))
                                                              (TVar 0)))))) EEmpty)
                    CEmpty
                    (Ann (App (App (Var 0) (Abs (Var 0)))
                              (LitInt 1))
                         (TArr (TArr TInt TInt) TInt))
      -- id [1, 2]
      test_list1 = infer EEmpty CEmpty (App idTrm (cons (LitInt 1) (cons (LitInt 2) Nil)))
      -- id @ [Int] []
      test_list2 = infer EEmpty CEmpty (App (TApp idTrm (TList TInt)) Nil)
      -- rejected: id @ [Int -> Int] [forall a. a -> a]
      test_list3 = infer EEmpty CEmpty (App (TApp idTrm (TList (TArr TInt TInt))) (cons idTrm Nil))
      -- id [id]
      test_list4 = infer EEmpty CEmpty (App idTrm (cons idTrm Nil))
      -- id [id @ (Int -> Int)]
      test_list5 = infer EEmpty CEmpty (App idTrm (cons (TApp idTrm (TArr TInt TInt)) Nil))
      -- id @ [Int -> Int] [id @ Int]
      test_list6 = infer EEmpty CEmpty (App (TApp idTrm (TList (TArr TInt TInt))) (cons (TApp idTrm TInt) Nil))
      -- (1, True)
      test_pair1 = infer EEmpty CEmpty (pair (LitInt 1) (LitBool True))
      -- A1: \x. \y. y  Ann~>  /\a. /\b. (\x. \y. y) : a -> b -> b
      ex_a1 = infer EEmpty CEmpty $ TAbs $ TAbs $ Ann (Abs (Abs (Var 0))) (TArr (TVar 1) (TArr (TVar 0) (TVar 0)))
      -- A2: choose id
      ex_a2 = infer (ETrm idTyp (ETrm chooseTyp EEmpty)) CEmpty $ (Var 1) `App` (Var 0)
      -- A3: choose Nil id
      ex_a3 = infer (ETrm (TList idTyp) (ETrm chooseTyp EEmpty)) CEmpty $ (Var 1) `App` (Nil `Ann` (TList idTyp)) `App` (Var 0)
      -- [ex_id, ex_id1, ex_idInt, ex_idInt1, ex_f1, ex_gid, ex_gid1, ex_g2, test_list1, test_list2, test_list3, test_list4, test_list5, test_list6, test_pair1]
  forM_ [ex_a1, ex_a2, ex_a3] $ \ex -> case runWriterT ex of
    Just (tyA, logs) -> do
      putStrLn $ "inferred type: " ++ show tyA
      mapM_ putStrLn logs
      hFlush stdout
    Nothing -> print "Nothing"




-- closed (EEvar EEmpty) (TArr (TVar 0) TInt)
