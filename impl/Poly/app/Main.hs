{-# LANGUAGE MultiWayIf, LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant multi-way if" #-}
module Main where
import Debug.Trace
import Control.Monad.Writer
import Control.Monad (forM_)

type Log = [String]

data Typ = TInt | TVar Int | TArr Typ Typ | TForall Typ
data Trm = Lit Int | Var Int | Abs Trm | App Trm Trm | Ann Trm Typ | TAbs Trm | TApp Trm Typ

instance Show Typ where
  show TInt = "Int"
  show (TVar i) = "t" ++ show i
  show (TArr t1 t2) = "(" ++ show t1 ++ " → " ++ show t2 ++ ")"
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
  show (ETyp env) = show env ++ " , • "
  show (ESol ty env) = show env ++ " , =" ++ show ty

instance Show SEnv where
  show (Base env) = show env
  show (STyp env) = show env ++ " , •"
  show (SEx env) = show env ++ " , ^"
  show (SSol ty env) = show env ++ " , =" ++ show ty


data Context = CEmpty | CFullType Typ | CTerm Trm Context | CTApp Typ Context

instance Show Context where
  show CEmpty = "□"
  show (CFullType ty) = show ty
  show (CTerm trm ctx) = "[" ++ show trm ++ "]" ++ " ↝ " ++ show ctx
  show (CTApp ty ctx) = "[" ++ show ty ++ "]" ++ " ↝ " ++ show ctx

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

lookupEnv :: Int -> Env -> WriterT Log Maybe Typ
lookupEnv 0 (EBind ty _) = do
  tell ["[Lookup] " ++ show ty ++ " in Γ"]
  return ty
lookupEnv k (EBind _ env) = lookupEnv (k - 1) env
lookupEnv k (ETyp env) = shiftTyp0 <$> lookupEnv k env
lookupEnv k (ESol _ env) = shiftTyp0 <$> lookupEnv k env
lookupEnv _ _ = lift Nothing

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
-- isTyp' a b | trace ("isTyp' " ++ show a ++ " " ++ show b) False = undefined
isTyp' EEmpty _ = False
isTyp' (EBind _ env) n = isTyp' env n
isTyp' (ETyp env) n = if | n == 0 -> True
                         | otherwise -> isTyp' env (n - 1)
isTyp' (ESol _ env) n = if | n == 0 -> False
                           | otherwise -> isTyp' env (n - 1)

isTyp :: SEnv -> Int -> Bool
-- isTyp a b | trace ("isTyp " ++ show a ++ " " ++ show b) False = undefined
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

findSol' :: Env -> Int -> WriterT Log Maybe Typ
findSol' EEmpty _ = lift Nothing
findSol' (EBind _ env) n = findSol' env n
findSol' (ETyp env) n = if | n == 0 -> lift Nothing
                           | otherwise -> shiftTyp0 <$> findSol' env (n - 1)
findSol' (ESol ty env) n = if | n == 0 -> return ty
                              | otherwise -> shiftTyp0 <$> findSol' env (n - 1)

findSol :: SEnv -> Int -> WriterT Log Maybe Typ
findSol (Base env) n = findSol' env n
findSol (STyp senv) n = if | n == 0 -> lift Nothing
                           | otherwise -> shiftTyp0 <$> findSol senv (n - 1)
findSol (SEx senv) n = if | n == 0 -> lift Nothing
                          | otherwise -> shiftTyp0 <$> findSol senv (n - 1)
findSol (SSol ty env) n = if | n == 0 -> return ty
                             | otherwise -> shiftTyp0 <$> findSol env (n - 1)

fullInst :: SEnv -> Typ -> WriterT Log Maybe Typ
fullInst _ TInt = return TInt
fullInst senv (TVar n) = case runWriterT $ findSol senv n of
  Just (ty, log') -> do
    tell log'
    fullInst senv ty
  Nothing -> return $ TVar n
fullInst senv (TArr t1 t2) = do
  t1' <- fullInst senv t1
  t2' <- fullInst senv t2
  return $ TArr t1' t2'
fullInst senv (TForall t) = do
  t' <- fullInst (STyp senv) t
  return $ TForall t'

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

logSub :: SEnv -> Typ -> Context -> String
logSub senv ty ctx = show senv ++ " ⊢ " ++ show ty ++ " <: " ++ show ctx ++ " ⊣ "

logSubFull :: SEnv -> Typ -> Context -> SEnv -> Typ -> String
logSubFull senv ty ctx senv' ty' = show senv ++ " ⊢ " ++ show ty ++ " <: " ++ show ctx ++ " ⊣ " ++ show senv' ++ " ⇝ " ++ show ty'

sub :: SEnv -> Typ -> Context -> WriterT Log Maybe (SEnv, Typ)
-- sub a b c | trace ("sub " ++ show a ++ " |- " ++ show b ++ " <: " ++ show c) False = undefined
sub senv TInt (CFullType TInt) = do
  tell ["[S-Int] " ++ logSubFull senv TInt (CFullType TInt) senv TInt]
  return (senv, TInt)
sub senv tyA CEmpty | closed senv tyA = do
  (newtyA, log') <- censor (const mempty) . listen $ fullInst senv tyA
  tell ["[S-Var] " ++ logSubFull senv tyA CEmpty senv newtyA]
  tell $ indentAll log'
  return (senv, newtyA)
sub senv (TVar a) (CFullType (TVar b)) | isTyp senv a && a == b = do
  tell ["[S-Refl] " ++ logSubFull senv (TVar a) (CFullType (TVar b)) senv (TVar a)]
  return (senv, TVar a)
sub senv (TVar a) (CFullType tyA) | isEx senv a && closed senv tyA = do
  tell ["[S-Ex-L] " ++ logSubFull senv (TVar a) (CFullType tyA) (contextSubst tyA a senv) tyA]
  return (contextSubst tyA a senv, tyA)
sub senv (TVar a) (CFullType tyA) | closed senv tyA = do
  (tyB, _log1) <- censor (const mempty) . listen $ findSol senv a
  ((senv', tyA'), _log2) <- censor (const mempty) . listen $ sub senv tyB (CFullType tyA)
  tell ["[S-Sol-L] " ++ logSubFull senv (TVar a) (CFullType tyA) senv' tyA']
  tell $ indentAll _log1
  tell $ indentAll _log2
  return (senv', tyA')
sub senv tyA (CFullType (TVar a)) | isEx senv a && closed senv tyA = do
  tell ["[S-Ex-R] " ++ logSubFull senv tyA (CFullType (TVar a)) (contextSubst tyA a senv) tyA]
  return (contextSubst tyA a senv, tyA)
sub senv tyA (CFullType (TVar a)) | closed senv tyA = do
  (tyB, _log1) <- censor (const mempty) . listen $ findSol senv a
  ((senv', tyA'), _log2) <- censor (const mempty) . listen $ sub senv tyA (CFullType tyB)
  tell ["[S-Sol-R] " ++ logSubFull senv tyA (CFullType (TVar a)) senv' tyA']
  tell $ indentAll _log1
  tell $ indentAll _log2
  return (senv', tyA')
sub senv (TArr tyA tyB) (CFullType (TArr tyC tyD)) = do
  ((senv1, _), _log1) <- censor (const mempty) . listen $ sub senv tyC (CFullType tyA)
  ((senv2, _), _log2) <- censor (const mempty) . listen $ sub senv1 tyB (CFullType tyD)
  tell ["[S-Arr] " ++ logSubFull senv (TArr tyA tyB) (CFullType (TArr tyC tyD)) senv2 (TArr tyC tyD)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return (senv2, TArr tyC tyD)
sub senv (TArr tyA tyB) (CTerm e h) | closed senv tyA = do
  (_ , _log1) <- censor (const mempty) . listen $ infer (erase senv) (CFullType tyA) e
  ((senv', tyD), _log2) <- censor (const mempty) . listen $ sub senv tyB h
  tell ["[S-Term-Closed] " ++ logSubFull senv (TArr tyA tyB) (CTerm e h) senv' (TArr tyA tyD)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return (senv', TArr tyA tyD)
sub senv (TArr tyA tyB) (CTerm e h) | open senv tyA = do
  (tyC, _log1) <- censor (const mempty) . listen $ infer (erase senv) CEmpty e
  ((senv1, tyA'), _log2) <- censor (const mempty) . listen $ sub senv tyC (CFullType tyA)
  ((senv2, tyD), _log3) <- censor (const mempty) . listen $ sub senv1 tyB h
  tell ["[S-Term-Open] " ++ logSubFull senv (TArr tyA tyB) (CTerm e h) senv2 (TArr tyA' tyD)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  tell $ indentAll _log3
  return (senv2, TArr tyA' tyD)
sub senv (TForall tyA) (CFullType (TForall tyB)) = do
  ((STyp senv', tyC), _log1) <- censor (const mempty) . listen $ sub senv tyA (CFullType tyB)
  tell ["[S-Forall] " ++ logSubFull senv (TForall tyA) (CFullType (TForall tyB)) senv' (TForall tyC)]
  tell $ indentAll _log1
  return (senv', TForall tyC)
sub senv (TForall tyA) (CTerm e h) = do
  ((senv', tyB), _log1) <- censor (const mempty) . listen $ sub (SEx senv) tyA (shiftContext0 (CTerm e h))
  case senv' of
    STyp senv'' -> do
      tell ["[S-Forall-L] " ++ logSubFull senv (TForall tyA) (CTerm e h) senv'' (unshiftTyp0 tyB)]
      tell $ indentAll _log1
      return (senv'', unshiftTyp0 tyB)
    SSol _ senv'' -> do
      tell ["[S-Forall-L] " ++ logSubFull senv (TForall tyA) (CTerm e h) senv'' (unshiftTyp0 tyB)]
      tell $ indentAll _log1
      return (senv'', unshiftTyp0 tyB)
    _ -> lift Nothing
sub senv (TForall tyA) (CTApp tyB h) = do
  ((SSol _ senv', tyC), _log1) <- censor (const mempty) . listen $ sub (SSol tyB senv) tyA (shiftContext0 h)
  tell ["[S-Forall-TApp] " ++ logSubFull senv (TForall tyA) (CTApp tyB h) senv' (unshiftTyp0 tyC)]
  tell $ indentAll _log1
  return (senv', unshiftTyp0 tyC)
sub _ _ _ = lift Nothing

nonEmptyContext :: Context -> Bool
nonEmptyContext CEmpty = False
nonEmptyContext _ = True

logInfer :: Env -> Context -> Trm -> String
logInfer env ctx tm = show env ++ " ⊢ " ++ show ctx ++ " ⇒ " ++ show tm ++ " ⇒ "

logInferFull :: Env -> Context -> Trm -> Typ -> String
logInferFull env ctx tm ty = show env ++ " ⊢ " ++ show ctx ++ " ⇒ " ++ show tm ++ " ⇒ " ++ show ty

indentAll :: [String] -> [String]
indentAll = map ("  "++)

infer :: Env -> Context -> Trm -> WriterT Log Maybe Typ
-- infer a b c | trace ("infer " ++ show a ++ " |- " ++ show b ++ " => " ++ show c) False = undefined
infer env CEmpty (Lit n) = do
  tell ["[Ty-Int] " ++ logInferFull env CEmpty (Lit n) TInt]
  return TInt
infer env CEmpty (Var i) = do
  tell ["[Ty-Var] " ++ logInferFull env CEmpty (Var i) TInt]
  censor indentAll $ lookupEnv i env
infer env CEmpty (Ann tm tyA) = do
  (_, _log) <- censor (const mempty) . listen $ infer env (CFullType tyA) tm
  tell ["[Ty-Ann] " ++ logInferFull env CEmpty (Ann tm tyA) tyA]
  tell $ indentAll _log
  return tyA
infer env h (App tm1 tm2) = do
  (TArr _ ty12, _log) <- censor (const mempty) . listen $ infer env (CTerm tm2 h) tm1
  tell ["[Ty-App] " ++ logInferFull env h (App tm1 tm2) ty12]
  tell $ indentAll _log
  return ty12
infer env (CFullType (TArr tyA tyB)) (Abs tm) = do
  (tyC, _log) <- censor (const mempty) . listen $ infer (EBind tyA env) (CFullType tyB) tm
  tell ["[Ty-Abs1] " ++ logInferFull env (CFullType (TArr tyA tyB)) (Abs tm) (TArr tyA tyC)]
  tell $ indentAll _log
  return $ TArr tyA tyC
infer env (CTerm tm2 h) (Abs tm) = do
  (tyA, _log1) <- censor (const mempty) . listen $ infer env CEmpty tm2
  (tyB, _log2) <- censor (const mempty) . listen $ infer (EBind tyA env) (shiftContext0 h) tm
  tell ["[Ty-Abs2] " ++ logInferFull env (CTerm tm2 h) (Abs tm) (TArr tyA tyB)]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return $ TArr tyA tyB
infer env h g | genericConsumer g && nonEmptyContext h = do
  (tyA, _log1) <- censor (const mempty) . listen $ infer env CEmpty g
  ((_, tyB), _log2) <- censor (const mempty) . listen $ sub (Base env) tyA h
  tell ["[Ty-Sub] " ++ logInferFull env h g tyB]
  tell $ indentAll _log1
  tell $ indentAll _log2
  return tyB
infer e CEmpty (TAbs tm) = do
  (tyA, _log) <- censor (const mempty) . listen $ infer (ETyp e) CEmpty tm
  tell ["[Ty-TAbs] " ++ logInferFull e CEmpty (TAbs tm) (TForall tyA)]
  tell $ indentAll _log
  return $ TForall tyA
infer e h (TApp tm tyA) = do
  (tyB, _log) <- censor (const mempty) . listen $ infer e (CTApp tyA h) tm
  tell ["[Ty-TApp] " ++ logInferFull e h (TApp tm tyA) tyB]
  tell $ indentAll _log
  return tyB
infer _ _ _ = lift Nothing

main :: IO ()
main = do
  -- print idTyp
  let ex_id = infer EEmpty CEmpty idTrm
      ex_id1 = infer EEmpty CEmpty (App idTrm (Lit 1))
      ex_idInt = infer EEmpty CEmpty (TApp idTrm TInt)
      ex_idInt1 = infer EEmpty CEmpty (App (TApp idTrm TInt) (Lit 42))
      ex_f1 = infer (EBind (TForall (TArr (TVar 0) (TVar 0))) EEmpty) CEmpty (App (Var 0) (Lit 42))
  forM_ [ex_id, ex_id1, ex_idInt, ex_idInt1, ex_f1] $ \ex -> case runWriterT ex of
    Just (tyA, logs) -> do
      putStrLn $ "inferred type: " ++ show tyA
      mapM_ putStrLn logs
    Nothing -> print "Nothing"
