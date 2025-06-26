{-# LANGUAGE MultiWayIf, LambdaCase, RankNTypes, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant multi-way if" #-}
module Log where
import Control.Monad.Writer

import Syntax

grey, red, bold, blue, reset :: String
grey  = "\ESC[90m"   -- Grey color (bright black)
red   = "\ESC[31m"   -- Red color
bold  = "\ESC[1m"    -- Bold text
blue  = "\ESC[34m"   -- Blue color
reset = "\ESC[0m"    -- Reset to default

logSub :: Env -> Typ -> Context -> String
logSub senv ty ctx = show senv ++ " ⊢ " ++ show ty ++ " <: " ++ show ctx ++ " ⊣ "

-- logSubFull :: (Env, Env) -> Typ -> Context -> Env -> Typ -> String
-- logSubFull (env, senv) ty ctx envout ty' = show env ++ "; " ++ show senv ++ " ⊢ " ++ show ty ++ " <: " ++ show ctx ++ " ⊣ " ++ show envout ++ " ⇝ " ++ show ty'

logSubFull :: (Env, Env) -> Typ -> Context -> Env -> Typ -> String
logSubFull (env, senv) ty ctx envout ty' =
  grey  ++ show env  ++ "; " ++ reset ++
  blue ++ show senv ++ reset ++ " ⊢ " ++
  show ty ++ " <: " ++
  show ctx ++ " ⊣ " ++
  red   ++ show envout ++ reset ++ " ⇝ " ++
  bold  ++ show ty' ++ reset

logSSubFull :: (Env, Env) -> Typ -> Typ -> Env -> String
logSSubFull (env, senv) ty1 ty2 envout = 
    grey ++ show env ++ "; " ++ reset ++ 
    blue ++ show senv ++ reset ++ " ⊢ " ++ 
    show ty1 ++ " <: " ++ 
    show ty2 ++ " ⊣ " ++ 
    red ++ show envout ++ reset

logInfers :: Env -> Context -> String
logInfers env ctx = show env ++ " ⊢ " ++ show ctx ++ " ⇒ "

logInfersFull :: Env -> Context -> Typ -> String
logInfersFull env ctx ty = 
  grey ++ show env ++ " ⊢ " ++ reset ++
  show ctx ++ " ⇒ " ++
  bold ++ show ty ++ reset

logInfer :: Env -> Context -> Trm -> String
logInfer env ctx tm = show env ++ " ⊢ " ++ show ctx ++ " ⇒ " ++ show tm ++ " ⇒ "

logInferFull :: Env -> Context -> Trm -> Typ -> String
logInferFull env ctx tm ty = show env ++ " ⊢ " ++ show ctx ++ " ⇒ " ++ show tm ++ " ⇒ " ++ 
  bold ++ show ty ++ reset

indentAll :: [String] -> [String]
indentAll = map ("  "++)

peek :: forall w m a. MonadWriter w m => m a -> m (a, w)
peek = censor (const mempty) . listen
