{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Syntax where

import Data.List (intercalate)

type Log = [String]

data Typ = TInt | TBool | TVar Int | TArr Typ Typ | TForall Typ | TUncurry [Typ] Typ | TList Typ | TProd Typ Typ | TST Typ Typ deriving (Eq)

data Trm
  = LitInt Int
  | LitBool Bool
  | Var Int
  | Abs Trm
  | AbsAnn Typ Trm
  | AbsUncurry Int Trm
  | AbsUncurryAnn [Typ] Trm
  | App Trm Trm
  | AppUncurry Trm [Trm]
  | Ann Trm Typ
  | TAbs Trm
  | TApp Trm Typ
  | Nil
  | Cons
  | Pair
  | ST
  | ConsUncurry
  | PairUncurry
  | STUncurry

instance Show Typ where
  showsPrec _ TInt = showString "Int"
  showsPrec _ TBool = showString "Bool"
  showsPrec _ (TVar i) = showString "t" . shows i
  showsPrec p (TArr t1 t2) = showParen (p > 0) $ showsPrec 1 t1 . showString " → " . shows t2
  showsPrec p (TForall t) = showParen (p > 0) $ showString "∀. " . shows t
  showsPrec p (TUncurry ts t) =
    showParen (p > 0) $
      showString "(" . showString (intercalate ", " $ map show ts) . showString ") → " . shows t
  showsPrec _ (TList t) = showString "[" . shows t . showString "]"
  showsPrec p (TProd t1 t2) = showParen (p > 1) $ showsPrec 1 t1 . showString " × " . showsPrec 1 t2
  showsPrec p (TST t1 t2) = showParen (p > 1) $ showString "ST " . showsPrec 1 t1 . showString " " . showsPrec 1 t2

instance Show Trm where
  showsPrec _ (LitInt i) = shows i
  showsPrec _ (LitBool b) = shows b
  showsPrec _ (Var i) = showString "e" . shows i
  showsPrec p (Abs t) = showParen (p > 0) $ showString "λ. " . shows t
  showsPrec p (AbsAnn ty t) = showParen (p > 0) $ showString "λ" . showString " : " . shows ty . showString ". " . shows t
  showsPrec p (AbsUncurry n t) = showParen (p > 0) $ showString "λ" . shows n . showString ". " . shows t
  showsPrec p (AbsUncurryAnn ts t) = showParen (p > 0) $ showString "λ" . showString " : (" . showString (intercalate ", " $ map show ts) . showString "). " . shows t
  showsPrec p (App t1 t2) = showParen (p > 9) $ showsPrec 9 t1 . showString " " . showsPrec 10 t2
  showsPrec p (AppUncurry t ts) = showParen (p > 9) $ showsPrec 9 t . showString "(" . showString (intercalate ", " $ map show ts) . showString ")"
  showsPrec p (Ann t ty) = showParen (p > 1) $ showsPrec 1 t . showString " : " . shows ty
  showsPrec p (TAbs t) = showParen (p > 0) $ showString "Λ. " . shows t
  showsPrec p (TApp t ty) = showParen (p > 9) $ showsPrec 9 t . showString " @" . showsPrec 10 ty
  showsPrec _ Nil = showString "Nil"
  showsPrec _ Cons = showString "Cons"
  showsPrec _ Pair = showString "Pair"
  showsPrec _ ST = showString "ST"
  showsPrec _ ConsUncurry = showString "Cons"
  showsPrec _ PairUncurry = showString "Pair"
  showsPrec _ STUncurry = showString "ST"

data Env = EEmpty | ETrm Typ Env | EUvar Env | EEvar Env | ESvar Typ Env

envConcat :: Env -> Env -> Env
envConcat env EEmpty = env
envConcat env (ETrm ty senv) = ETrm ty (envConcat env senv)
envConcat env (EUvar senv) = EUvar (envConcat env senv)
envConcat env (EEvar senv) = EEvar (envConcat env senv)
envConcat env (ESvar ty senv) = ESvar ty (envConcat env senv)

instance Show Env where
  show EEmpty = "∅"
  show (ETrm ty env) = show env ++ ", :" ++ show ty
  show (EUvar env) = show env ++ ", •"
  show (ESvar ty env) = show env ++ ", =" ++ show ty
  show (EEvar env) = show env ++ ", ^"

data Context = CEmpty | CFullType Typ | CTerm Trm Context | CTApp Typ Context | CUncurry [Trm] Context

instance Show Context where
  show CEmpty = "□"
  show (CFullType ty) = show ty
  show (CTerm trm ctx) = "[" ++ show trm ++ "]" ++ " ↝ " ++ show ctx
  show (CTApp ty ctx) = show ty ++ " @↝ " ++ show ctx
  show (CUncurry ts ctx) = "(" ++ intercalate ", " (map show ts) ++ ") ↝ " ++ show ctx

genericConsumer :: Trm -> Bool
genericConsumer (LitInt _) = True
genericConsumer (LitBool _) = True
genericConsumer (Var _) = True
genericConsumer (Ann _ _) = True
genericConsumer (TAbs _) = True
genericConsumer Cons = True
genericConsumer Pair = True
genericConsumer ST = True
genericConsumer ConsUncurry = True
genericConsumer PairUncurry = True
genericConsumer STUncurry = True
genericConsumer _ = False

nonEmptyContext :: Context -> Bool
nonEmptyContext CEmpty = False
nonEmptyContext _ = True

isEvar :: Env -> Int -> Bool
isEvar EEmpty _ = False
isEvar (ETrm _ env) k = isEvar env k
isEvar (EUvar env) k = (k /= 0) && isEvar env (k - 1)
isEvar (EEvar env) k = k == 0 || isEvar env (k - 1)
isEvar (ESvar _ env) k = (k /= 0) && isEvar env (k - 1)

isUvar :: Env -> Int -> Bool
-- isUvar a b  | trace ("isUvar " ++ show a ++ " in " ++ show b) False = undefined
isUvar EEmpty _ = False
isUvar (ETrm _ env) k = isUvar env k
isUvar (EUvar env) k = k == 0 || isUvar env (k - 1)
isUvar (EEvar env) k = (k /= 0) && isUvar env (k - 1)
isUvar (ESvar _ env) k = (k /= 0) && isUvar env (k - 1)

isSvar :: Env -> Int -> Bool
isSvar EEmpty _ = False
isSvar (ETrm _ env) k = isSvar env k
isSvar (EUvar env) k = (k /= 0) && isSvar env (k - 1)
isSvar (EEvar env) k = (k /= 0) && isSvar env (k - 1)
isSvar (ESvar _ env) k = k == 0 || isSvar env (k - 1)

closed :: Env -> Typ -> Bool
-- closed env ty | trace ("closed " ++ show env ++ " |- " ++ show ty) False = undefined
closed _ TInt = True
closed _ TBool = True
closed senv (TVar x) = not $ isEvar senv x
closed senv (TArr t1 t2) = closed senv t1 && closed senv t2
closed senv (TForall t) = closed (EUvar senv) t
closed senv (TUncurry ts t) = all (closed senv) ts && closed senv t
closed senv (TList t) = closed senv t
closed senv (TProd t1 t2) = closed senv t1 && closed senv t2
closed senv (TST t1 t2) = closed senv t1 && closed senv t2

open :: Env -> Typ -> Bool
-- open env ty | trace ("open " ++ show env ++ " |- " ++ show ty) False = undefined
open senv ty = not $ closed senv ty
