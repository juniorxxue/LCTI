module Main where
import Parser (parseTyp, parseTerm)
import Control.Monad.Except
import Control.Monad.IO.Class (liftIO)
import Examples (examplesList, Example(exampleName, exampleString), preEnvStrings)
import Infer
import Derivation (Derived(..), showDerivation)
import Syntax
import System.Console.Haskeline
import Data.Char (isSpace)
import Data.List (isInfixOf)
import Unbound.Generics.LocallyNameless.Name (s2n)
import Unbound.Generics.LocallyNameless (runFreshMT, FreshMT)
import Control.Exception (catch, SomeException, evaluate)

preEnv :: Env
preEnv = foldr (\(name, tyStr) env -> ETrm (s2n name) (parseTyp tyStr) env) EEmpty preEnvStrings

main :: IO ()
main = do
  putStrLn "Welcome to the type inference REPL of Fc. Type :q to quit."
  putStrLn "Available commands: :tree, :env, :examples, :tests, :define <name> : <type>"
  runInputT defaultSettings (repl preEnv preEnv)

repl :: Env -> Env -> InputT IO ()
repl envNamed env = do
  minput <- getInputLine "> "
  case minput of
    Nothing     -> liftIO $ putStrLn "Bye."
    Just ":q"   -> liftIO $ putStrLn "Bye."
    Just input
      | all isSpace input -> repl envNamed env  -- Skip empty/whitespace input
      | Just rest <- stripPrefix ":tree " input     -> liftIO (showTree envNamed env rest) >> repl envNamed env
      | Just _    <- stripPrefix ":env" input       -> liftIO (showEnvNamed envNamed) >> repl envNamed env
      | Just _    <- stripPrefix ":examples" input  -> liftIO showExamples >> repl envNamed env
      | Just _    <- stripPrefix ":tests" input     -> liftIO (runTests envNamed env) >> repl envNamed env
      | Just rest <- stripPrefix ":define " input   -> do
          let mDef = parseDefine rest
          case mDef of
            Left err -> outputStrLn err >> repl envNamed env
            Right (name, tyStr) -> do
              mty <- liftIO $ handleParseError (evaluate (parseTyp tyStr))
              case mty of
                Left err -> outputStrLn ("Error: " ++ err) >> repl envNamed env
                Right tyNamed -> do
                  let env' = ETrm (s2n name) tyNamed envNamed
                  -- Echo the defined type for convenience
                  outputStrLn (show tyNamed)
                  repl env' env'
      | otherwise                                 -> liftIO (showInfer envNamed env input) >> repl envNamed env

showInfer :: Env -> Env -> String -> IO ()
showInfer envNamed _env src = do
  mterm <- handleParseError (evaluate (parseTerm src))
  case mterm of
    Left err -> putStrLn $ "Error: " ++ err
    Right term -> do
      let results = runFreshMT $ runExceptT (infer envNamed CEmpty term :: ExceptT String (FreshMT []) (Derived Ty))
      case results of
        [] -> putStrLn "Error: No solution found"
        (res:_) -> case res of
          Right (Derived ty _) -> putStrLn (show ty)
          Left err             -> putStrLn $ "Error: " ++ err

showTree :: Env -> Env -> String -> IO ()
showTree envNamed _env src = do
  mterm <- handleParseError (evaluate (parseTerm src))
  case mterm of
    Left err -> putStrLn $ "Error: " ++ err
    Right term -> do
      let results = runFreshMT $ runExceptT (infer envNamed CEmpty term :: ExceptT String (FreshMT []) (Derived Ty))
      case results of
        [] -> putStrLn "Error: No solution found"
        (res:_) -> case res of
          Right (Derived _ d) -> putStr (showDerivation d)
          Left err            -> putStrLn $ "Error: " ++ err

showEnvNamed :: Env -> IO ()
showEnvNamed envNamed = putStrLn (show envNamed)


stripPrefix :: String -> String -> Maybe String
stripPrefix pre s =
  if take (length pre) s == pre then Just (drop (length pre) s) else Nothing

showExamples :: IO ()
showExamples =
  mapM_ (\example -> putStrLn (exampleName example ++ ":\n " ++ exampleString example ++ "\n")) examplesList

-- Run all examples and show type inference results
runTests :: Env -> Env -> IO ()
runTests envNamed _env = do
  putStrLn "=== Running all examples ===\n"
  let results = map (testExample envNamed) examplesList
  mapM_ printResult results
  putStrLn $ "\n=== Summary ==="
  let total = length results
      passed = length $ filter (\(_, _, success, _) -> success) results
      failed = total - passed
  putStrLn $ "Total: " ++ show total
  putStrLn $ "Passed: " ++ show passed
  putStrLn $ "Failed: " ++ show failed

testExample :: Env -> Example -> (String, String, Bool, String)
testExample envNamed example =
  let expr = exampleString example
      name = exampleName example
  in case parseAndInfer envNamed expr of
    Right ty -> (name, expr, True, show ty)
    Left err -> (name, expr, False, err)

parseAndInfer :: Env -> String -> Either String Ty
parseAndInfer envNamed src =
  let term = parseTerm src
      results = runFreshMT $ runExceptT (infer envNamed CEmpty term :: ExceptT String (FreshMT []) (Derived Ty))
  in case results of
    [] -> Left "No solution found"
    (res:_) -> case res of
      Right (Derived ty _) -> Right ty
      Left err -> Left err

printResult :: (String, String, Bool, String) -> IO ()
printResult (name, expr, success, res) = do
  let status = if success then "✓" else "✗"
  putStrLn $ status ++ " " ++ name
  putStrLn $ "  Expression: " ++ expr
  if success
    then putStrLn $ "  Type: " ++ res
    else putStrLn $ "  Error: " ++ res
  putStrLn ""

-- Handle parse errors by catching exceptions (including lexical errors)
handleParseError :: IO a -> IO (Either String a)
handleParseError action = catch (Right <$> action) handler
  where
    handler :: SomeException -> IO (Either String a)
    handler e = return (Left (extractErrorMessage e))

-- Extract a cleaner error message from exceptions
extractErrorMessage :: SomeException -> String
extractErrorMessage e =
  let msg = show e
  in if "lexical error" `isInfixOf` msg
     then "lexical error"
     else if "parse error" `isInfixOf` msg
          then "parse error"
          else msg

-- Parse a definition line of the form "<name> : <type>"
parseDefine :: String -> Either String (String, String)
parseDefine s =
  case break (== ':') s of
    (lhs, ':' : rhs) ->
      let name  = trim lhs
          tyStr = trim rhs
      in if null name || null tyStr
           then Left "Usage: :define <name> : <type>"
           else Right (name, tyStr)
    _ -> Left "Usage: :define <name> : <type>"
  where
    trim = f . f
      where f = reverse . dropWhile isSpace
