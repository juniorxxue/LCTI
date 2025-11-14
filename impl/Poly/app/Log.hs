{-# LANGUAGE RankNTypes #-}

module Log where

import Control.Monad.Writer
import Syntax

escGrey, escRed, escBold, escBlue, escReset, escYellow :: String
escGrey = "\ESC[90m" -- Grey color (bright black)
escRed = "\ESC[31m" -- Red color
escBold = "\ESC[1m" -- Bold text
escBlue = "\ESC[34m" -- Blue color
escReset = "\ESC[0m" -- Reset to default
escYellow = "\ESC[33m" -- Yellow color

grey, red, bold, blue, yellow :: String -> String
grey s = escGrey ++ s ++ escReset
red s = escRed ++ s ++ escReset
bold s = escBold ++ s ++ escReset
blue s = escBlue ++ s ++ escReset
yellow s = escYellow ++ s ++ escReset

logSub :: Env -> Ty -> Context -> String
logSub senv ty ctx = show senv ++ " ⊢ " ++ show ty ++ " <: " ++ show ctx ++ " ⊣ "

logInferUncurry :: (Env, Env) -> Ty -> Tm -> Ty -> Env -> String
logInferUncurry (_, senv) tyA e tyA' envout =
  grey "; "
    ++ blue (show senv)
    ++ " ⊢ "
    ++ show tyA
    ++ " ⇉ "
    ++ show e
    ++ " ⇉ "
    ++ bold (show tyA')
    ++ " ⊣ "
    ++ red (show envout)

logSubFull :: (Env, Env) -> Ty -> Context -> Env -> Ty -> String
logSubFull (_, senv) ty ctx envout ty' =
  grey "; "
    ++ blue (show senv)
    ++ " ⊢ "
    ++ show ty
    ++ " <: "
    ++ show ctx
    ++ " ⊣ "
    ++ red (show envout)
    ++ " ⇝ "
    ++ bold (show ty')

logSSubFull :: (Env, Env) -> Ty -> Polar -> Ty -> Env -> String
logSSubFull (_, senv) ty1 p ty2 envout =
  grey "; "
    ++ blue (show senv)
    ++ " ⊢ "
    ++ show ty1
    ++ " "
    ++ show p
    ++ " "
    ++ show ty2
    ++ " ⊣ "
    ++ red (show envout)

logInfers :: Env -> Context -> String
logInfers env ctx = show env ++ " ⊢ " ++ show ctx ++ " ⇒ "

logInfersFull :: Env -> Context -> Ty -> String
logInfersFull _ ctx ty =
  grey " ⊢ "
    ++ show ctx
    ++ " ⇒ "
    ++ bold (show ty)

logInfer :: Env -> Context -> Tm -> String
logInfer env ctx tm = show env ++ " ⊢ " ++ show ctx ++ " ⇒ " ++ show tm ++ " ⇒ "

logInferFull :: Env -> Context -> Tm -> Ty -> String
logInferFull _ ctx tm ty =
  " ⊢ "
    ++ show ctx
    ++ " ⇒ "
    ++ show tm
    ++ " ⇒ "
    ++ bold (show ty)

indentAll :: [String] -> [String]
indentAll = map ("  " ++)

peek :: forall w m a. (MonadWriter w m) => m a -> m (a, w)
peek = censor (const mempty) . listen

formatError :: String -> [(String, String)] -> String
formatError msg context = 
  bold (red "ERROR: ") ++ bold msg ++ "\n" ++
  concatMap (\(label, value) -> "  " ++ yellow label ++ ": " ++ value ++ "\n") context