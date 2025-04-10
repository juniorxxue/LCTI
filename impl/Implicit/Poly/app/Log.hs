{-# LANGUAGE MultiWayIf, LambdaCase, RankNTypes, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant multi-way if" #-}
module Log where
import Control.Monad.Writer
import Control.Monad (forM_)

import Syntax
import Counter
import DeBruijn

logSub :: Env -> Typ -> Context -> String
logSub senv ty ctx = show senv ++ " ⊢ " ++ show ty ++ " <: " ++ show ctx ++ " ⊣ "

logSubFull :: (Env, Env) -> Typ -> Context -> Env -> Typ -> String
logSubFull (env, senv) ty ctx envout ty' = show env ++ "; " ++ show senv ++ " ⊢ " ++ show ty ++ " <: " ++ show ctx ++ " ⊣ " ++ show envout ++ " ⇝ " ++ show ty'

logSSubFull :: (Env, Env) -> Typ -> Typ -> Env -> String
logSSubFull (env, senv) ty1 ty2 envout = show env ++ "; " ++ show senv ++ " ⊢ " ++ show ty1 ++ " <: " ++ show ty2 ++ " ⊣ " ++ show envout

logInfer :: Env -> Context -> Trm -> String
logInfer env ctx tm = show env ++ " ⊢ " ++ show ctx ++ " ⇒ " ++ show tm ++ " ⇒ "

logInferFull :: Env -> Context -> Trm -> Typ -> String
logInferFull env ctx tm ty = show env ++ " ⊢ " ++ show ctx ++ " ⇒ " ++ show tm ++ " ⇒ " ++ show ty

indentAll :: [String] -> [String]
indentAll = map ("  "++)

peek :: forall w m a. MonadWriter w m => m a -> m (a, w)
peek = censor (const mempty) . listen
