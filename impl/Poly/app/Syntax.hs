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
  | Pair Trm Trm
  | Fst Trm
  | Snd Trm

instance Show Typ where
  -- Primitive/base types align with the parser's lowercase keywords
  showsPrec _ TInt = showString "int"
  showsPrec _ TBool = showString "bool"
  -- De Bruijn type variable, printed as a named identifier usable by the parser
  showsPrec _ (TVar i) = showString "t" . shows i
  -- Arrow uses ASCII '->'
  showsPrec p (TArr t1 t2) = showParen (p > 0) $ showsPrec 1 t1 . showString " -> " . showsPrec 0 t2
  -- Forall: we don't have names here; print a placeholder 'a' each time
  showsPrec p (TForall t) = showParen (p > 0) $ showString "forall a. " . showsPrec 0 t
  -- Uncurried function type uses braces and ASCII arrow
  showsPrec p (TUncurry ts t) =
    showParen (p > 0) $
      showString "{" . showString (intercalate ", " $ map show ts) . showString "} -> " . showsPrec 0 t
  -- Lists as usual
  showsPrec _ (TList t) = showString "[" . shows t . showString "]"
  -- Product uses '*' instead of '×'
  showsPrec p (TProd t1 t2) = showParen (p > 1) $ showsPrec 1 t1 . showString " * " . showsPrec 1 t2
  showsPrec p (TST t1 t2) = showParen (p > 1) $ showString "ST " . showsPrec 1 t1 . showString " " . showsPrec 1 t2

instance Show Trm where
  showsPrec _ (LitInt i) = shows i
  -- Booleans in lowercase to match the parser
  showsPrec _ (LitBool b) = showString (if b then "true" else "false")
  -- De Bruijn term var printed as an identifier the parser accepts
  showsPrec _ (Var i) = showString "e" . shows i
  -- Use ASCII 'lambda' instead of 'λ' for easier typing
  showsPrec p (Abs t) = showParen (p > 0) $ showString "lambda . " . shows t
  showsPrec p (AbsAnn ty t) = showParen (p > 0) $ showString "lambda" . showString " : " . shows ty . showString ". " . shows t
  -- Uncurried abstractions: keep the count form for lack of names
  showsPrec p (AbsUncurry n t) = showParen (p > 0) $ showString "lambda" . shows n . showString ". " . shows t
  -- Uncurried annotated abstractions: print brace list of types
  showsPrec p (AbsUncurryAnn ts t) = showParen (p > 0) $ showString "lambda" . showString " : {" . showString (intercalate ", " $ map show ts) . showString "}. " . shows t
  -- Applications
  showsPrec p (App t1 t2) = showParen (p > 9) $ showsPrec 9 t1 . showString " " . showsPrec 10 t2
  -- Uncurried application uses braces
  showsPrec p (AppUncurry t ts) = showParen (p > 9) $ showsPrec 9 t . showString " {" . showString (intercalate ", " $ map show ts) . showString "}"
  -- Annotations
  showsPrec p (Ann t ty) = showParen (p > 1) $ showsPrec 1 t . showString " : " . shows ty
  -- Type abstraction/application use ASCII 'Lambda' and '@'
  showsPrec p (TAbs t) = showParen (p > 0) $ showString "Lambda . " . shows t
  showsPrec p (TApp t ty) = showParen (p > 9) $ showsPrec 9 t . showString " @" . showsPrec 10 ty
  -- Nil and pairs
  showsPrec _ Nil = showString "nil"
  showsPrec _ (Pair t1 t2) = showParen True $ shows t1 . showString ", " . shows t2
  -- Projections
  showsPrec p (Fst t) = showParen (p > 9) $ showString "fst " . showsPrec 10 t
  showsPrec p (Snd t) = showParen (p > 9) $ showString "snd " . showsPrec 10 t

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

data Context = CEmpty | CFullType Typ | CTerm Trm Context | CUncurry [Trm] Context | CFst Context | CSnd Context

instance Show Context where
  show CEmpty = "□"
  show (CFullType ty) = show ty
  show (CTerm trm ctx) = "[" ++ show trm ++ "]" ++ " ↝ " ++ show ctx
  show (CUncurry ts ctx) = "(" ++ intercalate ", " (map show ts) ++ ") ↝ " ++ show ctx
  show (CFst ctx) = "fst ↝ " ++ show ctx
  show (CSnd ctx) = "snd ↝ " ++ show ctx

genericConsumer :: Trm -> Bool
genericConsumer (LitInt _) = True
genericConsumer (LitBool _) = True
genericConsumer (Var _) = True
genericConsumer (Ann _ _) = True
genericConsumer (TAbs _) = True
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
