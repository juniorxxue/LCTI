{-# LANGUAGE DeriveGeneric,
             DeriveDataTypeable,
             FlexibleInstances,
             FlexibleContexts,
             MultiParamTypeClasses,
             ScopedTypeVariables
  #-}
module Syntax where

import Data.List (intercalate)

import Unbound.Generics.LocallyNameless
    ( name2String,
      unbind,
      Alpha,
      Bind,
      Embed(Embed),
      Fresh,
      Name,
      Subst(isvar),
      SubstName(SubstName),
      runFreshMT )

import GHC.Generics
import Data.Typeable (Typeable)
import Control.Monad (guard)
import Control.Applicative (Alternative, empty, (<|>))
import Debug.Trace

type TyName = Name Ty
type TmName = Name Tm


type Log = [String]

data Ty = TInt 
        | TBool 
        | TVar TyName
        | TArr Ty Ty 
        | TForall (Bind TyName Ty)
        | TUncurry [Ty] Ty 
        | TList Ty 
        | TProd Ty Ty 
        | TST Ty Ty 
        deriving (Generic, Typeable)

data Tm
  = LitInt Int
  | LitBool Bool
  | Var TmName
  | Abs (Bind TmName Tm)
  | AbsAnn (Bind (TmName, Embed Ty) Tm)
  | AbsUncurry (Bind [TmName] Tm)
  | AbsUncurryAnn (Bind [(TmName, Embed Ty)] Tm)
  | App Tm Tm
  | AppUncurry Tm [Tm]
  | Ann Tm Ty
  | TAbs (Bind TyName Tm)
  | TApp Tm Ty
  | Nil
  | Pair Tm Tm
  | Fst Tm
  | Snd Tm
  deriving (Generic, Typeable)

-- Precedence levels for types
data TypePrec = PrecAtom | PrecProd | PrecArr deriving (Eq, Ord)

-- Precedence levels for terms
data TermPrec = PrecAtomTerm | PrecAppTerm | PrecAnnTerm | PrecAbsTerm deriving (Eq, Ord)

-- Pretty print a type
prettyTyp :: (Fresh m) => Ty -> m String
prettyTyp = prettyTyp' PrecAtom

prettyTyp' :: (Fresh m) => TypePrec -> Ty -> m String
prettyTyp' _ TInt = return "int"
prettyTyp' _ TBool = return "bool"
prettyTyp' _ (TVar a) = return (name2String a)
prettyTyp' p (TArr t1 t2) = do
  -- Arrow is right-associative
  -- Left side: if it's an arrow, needs parentheses; if it's a product, no parentheses needed
  -- Right side: same precedence (right-associative)
  s1 <- case t1 of
    TArr _ _ -> do
      s <- prettyTyp' PrecArr t1
      return $ "(" ++ s ++ ")"
    _ -> prettyTyp' PrecProd t1
  s2 <- prettyTyp' PrecArr t2
  let result = s1 ++ " -> " ++ s2
  return $ if p <= PrecArr then result else "(" ++ result ++ ")"
prettyTyp' p (TProd t1 t2) = do
  -- Product is left-associative, so left side uses same precedence
  -- Right side uses higher precedence (PrecAtom)
  s1 <- prettyTyp' PrecProd t1
  s2 <- prettyTyp' PrecAtom t2
  let s1' = if p <= PrecProd then s1 else "(" ++ s1 ++ ")"
  return $ s1' ++ " * " ++ s2
prettyTyp' p (TForall b) = do
  (a, ty) <- unbind b
  s <- prettyTyp' PrecAtom ty
  return $ "forall " ++ name2String a ++ ". " ++ s
prettyTyp' p (TUncurry ts t) = do
  tsStrs <- mapM (prettyTyp' PrecAtom) ts
  tStr <- prettyTyp' PrecAtom t
  return $ "{" ++ intercalate ", " tsStrs ++ "} -> " ++ tStr
prettyTyp' _ (TList t) = do
  s <- prettyTyp' PrecAtom t
  return $ "[" ++ s ++ "]"
prettyTyp' _ (TST t1 t2) = do
  s1 <- prettyTyp' PrecAtom t1
  s2 <- prettyTyp' PrecAtom t2
  return $ "ST " ++ s1 ++ " " ++ s2

prettyTerm :: (Fresh m) => Tm -> m String
prettyTerm = prettyTerm' PrecAtomTerm

prettyTerm' :: (Fresh m) => TermPrec -> Tm -> m String
prettyTerm' _ (LitInt n) = return (show n)
prettyTerm' _ (LitBool True) = return "true"
prettyTerm' _ (LitBool False) = return "false"
prettyTerm' _ (Var x) = return (name2String x)
prettyTerm' _ Nil = return "nil"
prettyTerm' p (Abs b) = do
  (x, e) <- unbind b
  s <- prettyTerm' PrecAtomTerm e
  let result = "λ" ++ name2String x ++ ". " ++ s
  return $ if p <= PrecAbsTerm then result else "(" ++ result ++ ")"
prettyTerm' p (AbsAnn b) = do
  ((x, Embed ty), e) <- unbind b
  tyStr <- prettyTyp' PrecAtom ty
  s <- prettyTerm' PrecAtomTerm e
  let result = "λ" ++ name2String x ++ " : " ++ tyStr ++ ". " ++ s
  return $ if p <= PrecAbsTerm then result else "(" ++ result ++ ")"
prettyTerm' p (AbsUncurry b) = do
  (xs, e) <- unbind b
  s <- prettyTerm' PrecAtomTerm e
  let xsStr = intercalate ", " (map name2String xs)
  let result = "λ{" ++ xsStr ++ "}. " ++ s
  return $ if p <= PrecAbsTerm then result else "(" ++ result ++ ")"
prettyTerm' p (AbsUncurryAnn b) = do
  (anns, e) <- unbind b
  s <- prettyTerm' PrecAtomTerm e
  annStrs <- mapM (\(x, Embed ty) -> do
    tyStr <- prettyTyp' PrecAtom ty
    return $ name2String x ++ " : " ++ tyStr) anns
  let annStr = intercalate ", " annStrs
  let result = "λ{" ++ annStr ++ "}. " ++ s
  return $ if p <= PrecAbsTerm then result else "(" ++ result ++ ")"
prettyTerm' p (TAbs b) = do
  (a, e) <- unbind b
  s <- prettyTerm' PrecAtomTerm e
  let result = "Λ" ++ name2String a ++ ". " ++ s
  return $ if p <= PrecAbsTerm then result else "(" ++ result ++ ")"
prettyTerm' p (App e1 e2) = do
  -- Application is left-associative, so left side uses same precedence
  -- Right side uses higher precedence (PrecAtom)
  s1 <- prettyTerm' PrecAppTerm e1
  s2 <- prettyTerm' PrecAtomTerm e2
  let s1' = if p <= PrecAppTerm then s1 else "(" ++ s1 ++ ")"
  return $ s1' ++ " " ++ s2
prettyTerm' p (AppUncurry e es) = do
  s1 <- prettyTerm' PrecAppTerm e
  esStrs <- mapM (prettyTerm' PrecAtomTerm) es
  let esStr = "{" ++ intercalate ", " esStrs ++ "}"
  let s1' = if p <= PrecAppTerm then s1 else "(" ++ s1 ++ ")"
  return $ s1' ++ " " ++ esStr
prettyTerm' p (TApp e ty) = do
  s1 <- prettyTerm' PrecAppTerm e
  tyStr <- prettyTyp' PrecAtom ty
  let s1' = if p <= PrecAppTerm then s1 else "(" ++ s1 ++ ")"
  return $ s1' ++ " @ " ++ tyStr
prettyTerm' p (Ann e ty) = do
  s1 <- prettyTerm' PrecAnnTerm e
  tyStr <- prettyTyp' PrecAtom ty
  let s1' = if p <= PrecAnnTerm then s1 else "(" ++ s1 ++ ")"
  return $ s1' ++ " : " ++ tyStr
prettyTerm' p (Pair e1 e2) = do
  s1 <- prettyTerm' PrecAtomTerm e1
  s2 <- prettyTerm' PrecAtomTerm e2
  return $ "<" ++ s1 ++ ", " ++ s2 ++ ">"
prettyTerm' p (Fst e) = do
  s <- prettyTerm' PrecAtomTerm e
  return $ "fst " ++ s
prettyTerm' p (Snd e) = do
  s <- prettyTerm' PrecAtomTerm e
  return $ "snd " ++ s

-- Convenience functions that run in the Fresh monad
prettyTypIO :: Ty -> String
prettyTypIO ty = head (runFreshMT (prettyTyp ty))

prettyTermIO :: Tm -> String
prettyTermIO tm = head (runFreshMT (prettyTerm tm))

instance Show Ty where
  show = prettyTypIO
instance Show Tm where
  show = prettyTermIO

instance Alpha Ty
instance Alpha Tm

instance Subst Tm Ty
instance Subst Tm Tm where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing

instance Subst Ty Ty where  
  isvar (TVar x) = Just (SubstName x)
  isvar _ = Nothing  

data Env = EEmpty | ETrm TmName Ty Env | EUvar TyName Env | EEvar TyName Env | ESvar TyName Ty Env

envConcat :: Env -> Env -> Env
envConcat env EEmpty = env
envConcat env (ETrm x ty senv) = ETrm x ty (envConcat env senv)
envConcat env (EUvar a senv) = EUvar a (envConcat env senv)
envConcat env (EEvar a senv) = EEvar a (envConcat env senv)
envConcat env (ESvar a ty senv) = ESvar a ty (envConcat env senv)

instance Show Env where
  show EEmpty = "∅"
  show (ETrm x ty env) = show env ++ ", " ++ name2String x ++ ":" ++ show ty
  show (EUvar a env) = show env ++ ", " ++ name2String a
  show (EEvar a env) = show env ++ ", " ++ name2String a ++ "^"
  show (ESvar a ty env) = show env ++ ", " ++ name2String a ++ "=" ++ show ty

data Context = CEmpty | CFullType Ty | CTerm Tm Context | CUncurry [Tm] Context | CFst Context | CSnd Context

instance Show Context where
  show CEmpty = "■"
  show (CFullType ty) = show ty
  show (CTerm tm ctx) = "[" ++ show tm ++ "]" ++ " ↝ " ++ show ctx
  show (CUncurry ts ctx) = "{" ++ intercalate ", " (map show ts) ++ "} ↝ " ++ show ctx
  show (CFst ctx) = "fst ↝ " ++ show ctx
  show (CSnd ctx) = "snd ↝ " ++ show ctx

genericConsumer :: Tm -> Bool
genericConsumer (LitInt _) = True
genericConsumer (LitBool _) = True
genericConsumer (Var _) = True
genericConsumer (Ann _ _) = True
genericConsumer (TAbs _) = True
genericConsumer _ = False

nonEmptyContext :: Context -> Bool
nonEmptyContext CEmpty = False
nonEmptyContext _ = True

lookupTmVar :: Env -> TmName -> Maybe Ty
lookupTmVar EEmpty _ = Nothing
lookupTmVar (ETrm x ty env) y = case x == y of
  True -> Just ty
  False -> lookupTmVar env y
lookupTmVar (EUvar _ env) y = lookupTmVar env y
lookupTmVar (EEvar _ env) y = lookupTmVar env y
lookupTmVar (ESvar _ _ env) y = lookupTmVar env y

data TyVars = Uvar | Evar | Svar Ty 

lookupTyVar :: Env -> TyName -> Maybe TyVars
lookupTyVar EEmpty _ = Nothing
lookupTyVar (ETrm _ _ env) a = lookupTyVar env a
lookupTyVar (EUvar a env) b = case a == b of
  True -> Just Uvar
  False -> lookupTyVar env b
lookupTyVar (EEvar a env) b = case a == b of
  True -> Just Evar
  False -> lookupTyVar env b
lookupTyVar (ESvar a ty env) b = case a == b of
  True -> Just (Svar ty)
  False -> lookupTyVar env b

isEvar :: Env -> TyName -> Bool
isEvar env a = case lookupTyVar env a of
  Just Evar -> True
  _ -> False

isUvar :: Env -> TyName -> Bool
isUvar env a = case lookupTyVar env a of
  Just Uvar -> True
  _ -> False

isSvar :: Env -> TyName -> Bool
isSvar env a = case lookupTyVar env a of
  Just (Svar _) -> True
  _ -> False
  
closed :: (Fresh m, Alternative m) => Env -> Ty -> m ()
closed env ty | trace ("closed " ++ " |- " ++ show ty) False = undefined
closed _ TInt = return ()
closed _ TBool = return ()
closed senv (TVar a) = if isEvar senv a then empty else return ()
closed senv (TArr t1 t2) = (closed senv t1) >> (closed senv t2)
closed senv (TForall b) = do
  (a, ty) <- unbind b
  closed (EUvar a senv) ty
closed senv (TUncurry ts t) = mapM (closed senv) ts >> closed senv t
closed senv (TList t) = closed senv t
closed senv (TProd t1 t2) = (closed senv t1) >> (closed senv t2)
closed senv (TST t1 t2) = (closed senv t1) >> (closed senv t2)

isOpen :: (Fresh m, Alternative m) => Env -> Ty -> m ()
open env ty | trace ("open " ++ " |- " ++ show ty) False = undefined
isOpen senv ty = closed senv ty *> empty <|> return ()

data Polar = Pos | Neg deriving (Show, Eq)  

flipPolar :: Polar -> Polar
flipPolar Pos = Neg
flipPolar Neg = Pos

inst :: Env -> TyName -> Ty -> Maybe Env
-- inst env k a | trace ("inst " ++ show env ++ " " ++ show k ++ " " ++ show a) False = undefined
inst EEmpty _ _ = Nothing
inst (ETrm x ty env) a tyA = do
  env' <- inst env a tyA
  return $ ETrm x ty env'
inst (EUvar a env) b tyA = do
  env' <- inst env b tyA
  return $ EUvar a env'
inst (EEvar a env) b tyA = if a == b 
  then Just $ ESvar a tyA env
  else do
    env' <- inst env b tyA
    return $ EEvar a env'
inst (ESvar ty a env) b tyA = do
  env' <- inst env b tyA
  return $ ESvar ty a env'