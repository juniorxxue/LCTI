module Need where

import Syntax
import qualified Data.Map.Strict as M
import           Control.Monad (forM_)

data Counter = Z | I Counter | C Counter | Infinity

instance Show Counter where
    show Z = "0"
    show (I n) = "I " ++ show n
    show (C n) = "C " ++ show n
    show Infinity = "∞"

need :: Env -> Trm -> Counter
need _ (Lit _) = Z
need _ (Var _) = Z
need (env, senv) (Lam x e) = I (need ((x, TInt) : env, senv) e)
need (env, senv) (App e1 e2) = case needFun (env, senv) e1 of
    I n -> n
    C n -> n
    _ -> error "need: non-counter result"

envlook :: TEnv -> String -> Typ
envlook [] _ = error "envlook: unbound variable"
envlook ((x, t) : env) y | x == y = t
                        | otherwise = envlook env y

senvlook :: SEnv -> String -> Bool
senvlook [] _ = error "senvlook: unbound variable"
senvlook ((x, b) : senv) y | x == y = b
                          | otherwise = senvlook senv y

closed :: SEnv -> Typ -> Bool
closed senv TInt = True
closed senv (TVar x) = senvlook senv x
closed senv (TArr t1 t2) = closed senv t1 && closed senv t2
closed senv (TForall a ty) = closed ((a, True) : senv) ty

-- all free variables in type,
free :: Typ -> [String]
free TInt = []
free (TVar x) = [x]
free (TArr t1 t2) = free t1 ++ free t2
free (TForall a ty) = free ty

-- 1. take all free variables from type
-- 2. find & replace all free variables with True in senv
inst :: SEnv -> Typ -> SEnv
inst senv ty = map (\(x, b) -> (x, b || elem x (free ty))) senv

needFunType :: SEnv -> Typ -> Counter
needFunType senv TInt = Z
needFunType senv (TVar x) = if senvlook senv x then Z else Infinity
needFunType senv (TArr t1 t2) = if closed senv t1
                                then C (needFunType senv t2)
                                else I (needFunType (inst senv t1) t2)
needFunType senv (TForall a ty) = needFunType ((a, False) : senv) ty

needFun :: Env -> Trm -> Counter
needFun _ (Lit _) = error "needFun: literal"
needFun (env, senv) (Var x) = needFunType senv tyA
  where tyA = envlook env x
needFun (env, senv) (Lam x e) = I (needFun ((x, TInt) : env, senv) e)
needFun (env, senv) (App e1 e2) = case needFun (env, senv) e1 of
                                    I n -> n
                                    C n -> n
                                    _ -> error "needFun: bad function"


runExamples
  :: Int                   -- ^ how many examples to run (1…n)
  -> TEnv                  -- ^ your typing environment
  -> M.Map String Trm     -- ^ map of named terms ("ex1", "ex2", …)
  -> IO ()
runExamples n env tm = forM_ [1..n] $ \i -> do
  let key  = "ex" ++ show i
      term = tm M.! key
  putStr $ "needFun: "
  putStr $ ppTrm term
  putStr " ===> "
  print    (needFun (env, []) term)
  putStr $ "need: "
  putStr $ ppTrm term
  putStr " ===> "
  print    (need (env, []) term)

main :: IO ()
main = do
  putStrLn "------- env -----------"
  putStrLn $ ppTEnv bigEnv
  runExamples 4 bigEnv termMap
