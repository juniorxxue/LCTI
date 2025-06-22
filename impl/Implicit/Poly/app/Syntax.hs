{-# LANGUAGE MultiWayIf, LambdaCase, RankNTypes, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant multi-way if" #-}
module Syntax where

import Debug.Trace

type Log = [String]
data Typ = TInt | TBool | TVar Int | TArr Typ Typ | TForall Typ | TList Typ | TProd Typ Typ | TST Typ Typ deriving (Eq)
data Trm = LitInt Int | LitBool Bool | Var Int | Abs Trm | App Trm Trm | Ann Trm Typ | TAbs Trm | TApp Trm Typ | Nil | Cons | Pair | ST

instance Show Typ where
  show TInt = "Int"
  show TBool = "Bool"
  show (TVar i) = "t" ++ show i
  show (TArr t1 t2) = "(" ++ show t1 ++ " → " ++ show t2 ++ ")"
  show (TForall t) = "∀. " ++ show t
  show (TList t) = "[" ++ show t ++ "]"
  show (TProd t1 t2) = "(" ++ show t1 ++ " × " ++ show t2 ++ ")"
  show (TST t1 t2) = "(ST " ++ show t1 ++ " " ++ show t2 ++ ")"

instance Show Trm where
  show (LitInt i) = show i
  show (LitBool b) = show b
  show (Var i) = "e" ++ show i
  show (Abs t) = "(λ. " ++ show t ++ ")"
  show (App t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
  show (Ann t ty) = "(" ++ show t ++ " : " ++ show ty ++ ")"
  show (TAbs t) = "(Λ. " ++ show t ++ ")"
  show (TApp t ty) = "(" ++ show t ++ " @" ++ show ty ++ ")"
  show Nil = "Nil"
  show Cons = "Cons"
  show Pair = "Pair"
  show ST = "ST"

data Env = EEmpty | ETrm Typ Env | EUvar Env | EEvar Env | ESvar Typ Env

envConcat :: Env -> Env -> Env
envConcat env EEmpty = env
envConcat env (ETrm ty senv) = ETrm ty (envConcat env senv)
envConcat env (EUvar senv) = EUvar (envConcat env senv)
envConcat env (EEvar senv) = EEvar (envConcat env senv)
envConcat env (ESvar ty senv) = ESvar ty (envConcat env senv)

instance Show Env where
  show EEmpty = "∅"
  show (ETrm ty env) = show env ++ " , : " ++ show ty
  show (EUvar env) = show env ++ " , • "
  show (ESvar ty env) = show env ++ " , =" ++ show ty
  show (EEvar env) = show env ++ " , ^"

data Context = CEmpty | CFullType Typ | CTerm Trm Context | CTApp Typ Context

instance Show Context where
  show CEmpty = "□"
  show (CFullType ty) = show ty
  show (CTerm trm ctx) = "[" ++ show trm ++ "]" ++ " ↝ " ++ show ctx
  show (CTApp ty ctx) = show ty ++ " @↝ " ++ show ctx

genericConsumer :: Trm -> Bool
genericConsumer (LitInt _) = True
genericConsumer (LitBool _) = True
genericConsumer (Var _) = True
genericConsumer (Ann _ _) = True
genericConsumer (TAbs _) = True
genericConsumer Cons = True
genericConsumer Pair = True
genericConsumer _ = False


nonEmptyContext :: Context -> Bool
nonEmptyContext CEmpty = False
nonEmptyContext _ = True


isEvar :: Env -> Int -> Bool
isEvar EEmpty _ = False
isEvar (ETrm _ env) k = isEvar env k
isEvar (EUvar env) k = if | k == 0 -> False
                          | otherwise -> isEvar env (k - 1)
isEvar (EEvar env) k = if | k == 0 -> True
                          | otherwise -> isEvar env (k - 1)
isEvar (ESvar _ env) k = if | k == 0 -> False
                            | otherwise -> isEvar env (k - 1)

isUvar :: Env -> Int -> Bool
-- isUvar a b  | trace ("isUvar " ++ show a ++ " in " ++ show b) False = undefined
isUvar EEmpty _ = False
isUvar (ETrm _ env) k = isUvar env k
isUvar (EUvar env) k = if | k == 0 -> True
                          | otherwise -> isUvar env (k - 1)
isUvar (EEvar env) k = if | k == 0 -> False
                          | otherwise -> isUvar env (k - 1)
isUvar (ESvar _ env) k = if | k == 0 -> False
                            | otherwise -> isUvar env (k - 1)

isSvar :: Env -> Int -> Bool
isSvar EEmpty _ = False
isSvar (ETrm _ env) k = isSvar env k
isSvar (EUvar env) k = if | k == 0 -> False
                          | otherwise -> isSvar env (k - 1)
isSvar (EEvar env) k = if | k == 0 -> False
                          | otherwise -> isSvar env (k - 1)
isSvar (ESvar _ env) k = if | k == 0 -> True
                            | otherwise -> isSvar env (k - 1)

closed :: Env -> Typ -> Bool
-- closed env ty | trace ("closed " ++ show env ++ " |- " ++ show ty) False = undefined
closed _ TInt = True
closed _ TBool = True
closed senv (TVar x) = not $ isEvar senv x
closed senv (TArr t1 t2) = closed senv t1 && closed senv t2
closed senv (TForall t) = closed (EUvar senv) t
closed senv (TList t) = closed senv t
closed senv (TProd t1 t2) = closed senv t1 && closed senv t2
closed senv (TST t1 t2) = closed senv t1 && closed senv t2

open :: Env -> Typ -> Bool
-- open env ty | trace ("open " ++ show env ++ " |- " ++ show ty) False = undefined
open senv ty = not $ closed senv ty
