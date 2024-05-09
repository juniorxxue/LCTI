{-# LANGUAGE MultiWayIf, GADTs, LambdaCase #-}
module Main where
import Debug.Trace (trace)

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


-- could do via substitution
unshiftTyp :: Int -> Typ -> Typ
unshiftTyp = undefined

unshiftTyp0 :: Typ -> Typ
unshiftTyp0 = unshiftTyp 0

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

fullInst :: SEnv -> Typ -> Typ
fullInst = undefined

closed :: SEnv -> Typ -> Bool
closed = undefined

isEx :: SEnv -> Int -> Bool
isEx = undefined

findSol :: SEnv -> Int -> Maybe Typ
findSol = undefined

isTyp :: SEnv -> Int -> Bool
isTyp = undefined

contextSubst :: Typ -> Int -> SEnv -> SEnv
contextSubst = undefined

open :: SEnv -> Typ -> Bool
open = undefined

erase :: SEnv -> Env
erase = undefined

sub :: SEnv -> Typ -> Context -> Maybe (SEnv, Typ)
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
infer e h g | genericConsumer g = do
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
  -- print $ infer EEmpty CEmpty idTrm
  -- print $ infer EEmpty CEmpty (Lit 1)
  -- print $ infer (ETyp EEmpty) CEmpty (Ann (Abs (Var 0)) (TArr (TVar 0) (TVar 0)))
