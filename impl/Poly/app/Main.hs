{-# LANGUAGE MultiWayIf, GADTs, LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant multi-way if" #-}
module Main where
import Debug.Trace (trace)
import Control.Monad.Writer

type Log = [String]

data Typ = TInt | TVar Int | TArr Typ Typ | TForall Typ
data Trm = Lit Int | Var Int | Abs Trm | App Trm Trm | Ann Trm Typ | TAbs Trm | TApp Trm Typ

instance Show Typ where
  show TInt = "Int"
  show (TVar i) = "t" ++ show i
  show (TArr t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (TForall t) = "∀. " ++ show t

instance Show Trm where
  show (Lit i) = show i
  show (Var i) = show i
  show (Abs t) = "(λ. " ++ show t ++ ")"
  show (App t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
  show (Ann t ty) = "(" ++ show t ++ " : " ++ show ty ++ ")"
  show (TAbs t) = "(Λ. " ++ show t ++ ")"
  show (TApp t ty) = "(" ++ show t ++ " [" ++ show ty ++ "])"

idTyp :: Typ
idTyp = TForall (TArr (TVar 0) (TVar 0))

idTrm :: Trm
idTrm = TAbs (Ann (Abs (Var 0)) (TArr (TVar 0) (TVar 0)))

data Env = EEmpty | EBind Typ Env | ETyp Env | ESol Typ Env
data SEnv = Base Env | STyp SEnv | SEx SEnv | SSol Typ SEnv

instance Show Env where
  show EEmpty = "∅"
  show (EBind ty env) = show env ++ " , : " ++ show ty
  show (ETyp env) = show env ++ " , ▸ "
  show (ESol ty env) = show env ++ " , =" ++ show ty

instance Show SEnv where
  show (Base env) = show env
  show (STyp env) = show env ++ " , ▸"
  show (SEx env) = show env ++ " , ^"
  show (SSol ty env) = show env ++ " , =" ++ show ty


data Context = CEmpty | CFullType Typ | CTerm Trm Context | CTApp Typ Context

instance Show Context where
  show CEmpty = "[]"
  show (CFullType ty) = show ty
  show (CTerm trm ctx) = "[" ++ show trm ++ "]" ++ " ~> " ++ show ctx
  show (CTApp ty ctx) = "[" ++ show ty ++ "]" ++ " ~> " ++ show ctx

-- shifting --

shiftTyp :: Int -> Typ -> Typ
shiftTyp _ TInt = TInt
shiftTyp k (TVar x) = if | x < k -> TVar x
                         | otherwise -> TVar (x + 1)
shiftTyp k (TArr t1 t2) = TArr (shiftTyp k t1) (shiftTyp k t2)
shiftTyp k (TForall t) = TForall (shiftTyp (k + 1) t)

shiftTyp0 :: Typ -> Typ
shiftTyp0 = shiftTyp 0

substTyp :: Int -> Typ -> Typ -> Typ
substTyp _ _ TInt = TInt
substTyp k tyA (TVar x) = if | k == x -> tyA
                             | otherwise -> TVar $ punchOut k x
                          where punchOut i j = if j > i then j - 1 else j
substTyp k tyA (TArr t1 t2) = TArr (substTyp k tyA t1) (substTyp k tyA t2)
substTyp k tyA (TForall tyB) = TForall (substTyp (k + 1) (shiftTyp0 tyA) tyB)

unshiftTyp0 :: Typ -> Typ
unshiftTyp0 = substTyp 0 TInt

shiftTerm :: Int -> Trm -> Trm
shiftTerm _ (Lit i) = Lit i
shiftTerm k (Var x) = if | x < k -> Var x
                         | otherwise -> Var (x + 1)
shiftTerm k (Abs t) = Abs (shiftTerm (k + 1) t)
shiftTerm k (App t1 t2) = App (shiftTerm k t1) (shiftTerm k t2)
shiftTerm k (Ann t ty) = Ann (shiftTerm k t) ty
shiftTerm k (TAbs t) = TAbs (shiftTerm k t)
shiftTerm k (TApp t ty) = TApp (shiftTerm k t) ty

shiftTerm0 :: Trm -> Trm
shiftTerm0 = shiftTerm 0

shiftContext :: Int -> Context -> Context
shiftContext _ CEmpty = CEmpty
shiftContext _ (CFullType ty) = CFullType ty
shiftContext k (CTerm trm ctx) = CTerm (shiftTerm k trm) (shiftContext k ctx)
shiftContext k (CTApp ty ctx) = CTApp ty (shiftContext k ctx)

shiftContext0 :: Context -> Context
shiftContext0 = shiftContext 0

-- end shifting --

lookupEnv :: Int -> Env -> Maybe Typ
lookupEnv 0 (EBind ty _) = Just ty
lookupEnv k (EBind _ env) = lookupEnv (k - 1) env
lookupEnv k (ETyp env) = shiftTyp0 <$> lookupEnv k env
lookupEnv k (ESol _ env) = shiftTyp0 <$> lookupEnv k env
lookupEnv _ _ = Nothing

genericConsumer :: Trm -> Bool
genericConsumer (Lit _) = True
genericConsumer (Var _) = True
genericConsumer (Ann _ _) = True
genericConsumer (TAbs _) = True
genericConsumer _ = False

isEx :: SEnv -> Int -> Bool
isEx (Base _) _ = False
isEx (STyp senv) n = if | n == 0 -> False
                        | otherwise -> isEx senv (n - 1)
isEx (SEx senv) n = if | n == 0 -> True
                       | otherwise -> isEx senv (n - 1)
isEx (SSol _ env) n = if | n == 0 -> False
                         | otherwise -> isEx env (n - 1)

isTyp' :: Env -> Int -> Bool
isTyp' EEmpty _ = False
isTyp' (EBind _ env) n = if | n == 0 -> False
                            | otherwise -> isTyp' env n
isTyp' (ETyp env) n = if | n == 0 -> True
                         | otherwise -> isTyp' env (n - 1)
isTyp' (ESol _ env) n = if | n == 0 -> False
                           | otherwise -> isTyp' env (n - 1)

isTyp :: SEnv -> Int -> Bool
isTyp (Base env) n = isTyp' env n
isTyp (STyp senv) n = if | n == 0 -> True
                         | otherwise -> isTyp senv (n - 1)
isTyp (SEx senv) n = if | n == 0 -> False
                        | otherwise -> isTyp senv (n - 1)
isTyp (SSol _ env) n = if | n == 0 -> False
                          | otherwise -> isTyp env (n - 1)

closed :: SEnv -> Typ -> Bool
closed _ TInt = True
closed senv (TVar x) = not $ isEx senv x
closed senv (TArr t1 t2) = closed senv t1 && closed senv t2
closed senv (TForall t) = closed (STyp senv) t

open :: SEnv -> Typ -> Bool
open senv ty = not $ closed senv ty

findSol' :: Env -> Int -> Maybe Typ
findSol' EEmpty _ = Nothing
findSol' (EBind _ env) n = findSol' env n
findSol' (ETyp env) n = if | n == 0 -> Nothing
                           | otherwise -> shiftTyp0 <$> findSol' env (n - 1)
findSol' (ESol ty env) n = if | n == 0 -> Just ty
                              | otherwise -> shiftTyp0 <$> findSol' env (n - 1)

findSol :: SEnv -> Int -> Maybe Typ
findSol (Base env) n = findSol' env n
findSol (STyp senv) n = if | n == 0 -> Nothing
                           | otherwise -> shiftTyp0 <$> findSol senv (n - 1)
findSol (SEx senv) n = if | n == 0 -> Nothing
                          | otherwise -> shiftTyp0 <$> findSol senv (n - 1)
findSol (SSol ty env) n = if | n == 0 -> Just ty
                             | otherwise -> shiftTyp0 <$> findSol env (n - 1)

fullInst :: SEnv -> Typ -> Typ
fullInst _ TInt = TInt
fullInst senv (TVar n) = case findSol senv n of
  Just ty -> fullInst senv ty
  Nothing -> TVar n
fullInst senv (TArr t1 t2) = TArr (fullInst senv t1) (fullInst senv t2)
fullInst senv (TForall t) = TForall $ fullInst (STyp senv) t

-- the side conditions in the sub ensures that
-- when reaching the zero, it should be SEx
-- and I noticed that we iterate more than time, if it's possible to merge them?
contextSubst :: Typ -> Int -> SEnv -> SEnv
contextSubst tyA 0 (SEx senv) = SSol (unshiftTyp0 tyA) senv
contextSubst tyA n (SEx senv) | n /= 0 = SEx $ contextSubst (unshiftTyp0 tyA) (n - 1) senv
contextSubst tyA n (STyp senv) | n /= 0 = STyp $ contextSubst (unshiftTyp0 tyA) (n - 1) senv
contextSubst tyA n (SSol tyB senv) | n /= 0 = SSol tyB $ contextSubst (unshiftTyp0 tyA) (n - 1) senv
contextSubst _ _ _ = error "contextSubst: invalid arguments"

erase :: SEnv -> Env
erase (Base env) = env
erase (STyp senv) = ETyp $ erase senv
erase (SEx senv) = ESol TInt $ erase senv
erase (SSol ty senv) = ESol ty $ erase senv

sub :: SEnv -> Typ -> Context -> Maybe (SEnv, Typ)
sub senv ty ctx | trace ("tracing -- sub " ++ show senv ++ " " ++ show ty ++ " " ++ show ctx) False = undefined
sub senv TInt (CFullType TInt) = return (senv, TInt)
sub senv tyA CEmpty | closed senv tyA = return (senv, newtyA)
  where newtyA = fullInst senv tyA
sub senv (TVar a) (CFullType (TVar b)) | isTyp senv a && a == b = return (senv, TVar a)
sub senv (TVar a) (CFullType tyA) | isEx senv a && closed senv tyA = return (contextSubst tyA a senv, tyA)
sub senv (TVar a) (CFullType tyA) | closed senv tyA = do
  tyB <- findSol senv a
  (senv', tyA') <- sub senv tyB (CFullType tyA)
  return (senv', tyA')
sub senv tyA (CFullType (TVar a)) | isEx senv a && closed senv tyA = return (contextSubst tyA a senv, tyA)
sub senv tyA (CFullType (TVar a)) | closed senv tyA = do
  tyB <- findSol senv a
  (senv', tyA') <- sub senv tyA (CFullType tyB)
  return (senv', tyA')
sub senv (TArr tyA tyB) (CFullType (TArr tyC tyD)) = do
  (senv1, _) <- sub senv tyC (CFullType tyA)
  (senv2, _) <- sub senv1 tyB (CFullType tyD)
  return (senv2, TArr tyC tyD)
sub senv (TArr tyA tyB) (CTerm e h) | closed senv tyA && closed senv tyB = do
  _ <- infer (erase senv) (CFullType tyA) e
  (senv', tyD) <- sub senv tyB h
  return (senv', TArr tyA tyD)
sub senv (TArr tyA tyB) (CTerm e h) | open senv tyA = do
  tyC <- infer (erase senv) CEmpty e
  (senv1, tyA') <- sub senv tyC (CFullType tyA)
  (senv2, tyD) <- sub senv1 tyB h
  return (senv2, TArr tyA' tyD)
sub senv (TForall tyA) (CFullType (TForall tyB)) = do
  (STyp senv', tyC) <- sub (STyp senv) tyA (CFullType tyB)
  return (senv', TForall tyC)
sub senv (TForall tyA) (CTerm e h) = do
  (senv', tyB) <- sub (SEx senv) tyA (shiftContext0 (CTerm e h))
  case senv' of
    STyp senv'' -> return (senv'', unshiftTyp0 tyB)
    SSol _ senv'' -> return (senv'', unshiftTyp0 tyB)
    _ -> Nothing
sub senv (TForall tyA) (CTApp tyB h) = do
  (SSol _ senv', tyC) <- sub (SSol tyB senv) tyA (shiftContext0 h)
  return (senv', unshiftTyp0 tyC)
sub _ _ _ = Nothing

nonEmptyContext :: Context -> Bool
nonEmptyContext CEmpty = False
nonEmptyContext _ = True

infer :: Env -> Context -> Trm -> Maybe Typ
infer a b c | trace ("tracing -- infer " ++ show a ++ " " ++ show b ++ " " ++ show c) False = undefined
infer _ CEmpty (Lit _) = Just TInt
infer e CEmpty (Var i) = lookupEnv i e
infer e CEmpty (Ann tm tyA) = infer e (CFullType tyA) tm >> return tyA
infer e h (App tm1 tm2) = infer e (CTerm tm2 h) tm1 >>= (\case {TArr _ ty12 -> return ty12; _ -> Nothing})
infer e (CFullType (TArr tyA tyB)) (Abs tm) = do
  tyC <- infer (EBind tyA e) (CFullType tyB) tm
  return $ TArr tyA tyC
infer e (CTerm tm2 h) (Abs tm) = do
  tyA <- infer e CEmpty tm2
  tyB <- infer (EBind tyA e) (shiftContext0 h) tm
  return $ TArr tyA tyB
infer e h g | genericConsumer g && nonEmptyContext h = do
  tyA <- infer e CEmpty g
  (_, tyB) <- sub (Base e) tyA h
  return tyB
infer e CEmpty (TAbs tm) = do
  tyA <- infer (ETyp e) CEmpty tm
  return $ TForall tyA
infer e h (TApp tm tyA) = infer e (CTApp tyA h) tm
infer _ _ _ = Nothing

main :: IO ()
main = do
  print idTyp
  print idTrm
  -- print $ sub (Base EEmpty) (TForall (TArr (TVar 0) (TVar 0))) (CTerm (Lit 1) CEmpty)
  -- print $ sub (Base EEmpty) (TForall (TArr (TVar 0) (TVar 0))) (CTApp TInt (CTerm (Lit 1) CEmpty))
  -- print $ infer EEmpty CEmpty (App idTrm (Lit 1))
  print $ infer EEmpty CEmpty idTrm
  -- print $ infer (ETyp EEmpty) CEmpty (Ann (Abs (Var 0)) (TArr (TVar 0) (TVar 0)))
  -- print $ infer EEmpty CEmpty idTrm
  -- print $ infer EEmpty CEmpty (Lit 1)
  -- print $ infer (ETyp EEmpty) CEmpty (Ann (Abs (Var 0)) (TArr (TVar 0) (TVar 0)))
