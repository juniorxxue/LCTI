module Main where
import Parser (parseTyp, parseTerm)
import Control.Monad.Writer
import Examples (examplesList, Example(exampleName, exampleString), preEnvStrings)
import Infer
import Syntax
import System.Console.Haskeline
import Data.Char (isSpace)
import Unbound.Generics.LocallyNameless.Name (s2n)
import Unbound.Generics.LocallyNameless (runFreshMT, FreshMT)

preEnv :: Env
preEnv = foldr (\(name, tyStr) env -> ETrm (s2n name) (parseTyp tyStr) env) EEmpty preEnvStrings

main :: IO ()
main = do
  putStrLn "Welcome to the type inference REPL of Fc. Type :q to quit."
  putStrLn "Available commands: :tree, :env, :examples, :define <name> : <type>"
  runInputT defaultSettings (repl preEnv preEnv)
-- The REPL maintains a current named environment and its de Bruijn-converted form
repl :: Env -> Env -> InputT IO ()
repl envNamed env = do
  minput <- getInputLine "> "
  case minput of
    Nothing     -> liftIO $ putStrLn "Bye."
    Just ":q"   -> liftIO $ putStrLn "Bye."
    Just input
      | Just rest <- stripPrefix ":tree " input     -> liftIO (showTree envNamed env rest) >> repl envNamed env
      | Just _    <- stripPrefix ":env" input       -> liftIO (showEnvNamed envNamed) >> repl envNamed env
      | Just _    <- stripPrefix ":examples" input  -> liftIO showExamples >> repl envNamed env
      | Just rest <- stripPrefix ":define " input   -> do
          let mDef = parseDefine rest
          case mDef of
            Left err -> outputStrLn err >> repl envNamed env
            Right (name, tyNamed) -> do
              let env' = ETrm (s2n name) tyNamed envNamed                  
              -- Echo the defined type for convenience
              outputStrLn (show tyNamed)
              repl env' env'
      | otherwise                                 -> liftIO (showInfer envNamed env input) >> repl envNamed env

showInfer :: Env -> Env -> String -> IO ()
showInfer envNamed _env src = do
  let term = parseTerm src
      results = runFreshMT $ runWriterT (infer envNamed CEmpty term :: WriterT Log (FreshMT []) Ty)
  case results of
    ((ty, _):_) -> putStrLn (show ty)
    []          -> putStrLn "failure"

showTree :: Env -> Env -> String -> IO ()
showTree envNamed _env src = do
  let term = parseTerm src
      results = runFreshMT $ runWriterT (infer envNamed CEmpty term :: WriterT Log (FreshMT []) Ty)
  case results of
    ((_, logs):_) -> putStr (unlines logs)
    []            -> putStrLn "failure"

showEnvNamed :: Env -> IO ()
showEnvNamed envNamed = putStrLn (show envNamed)


stripPrefix :: String -> String -> Maybe String
stripPrefix pre s =
  if take (length pre) s == pre then Just (drop (length pre) s) else Nothing

showExamples :: IO ()
showExamples =
  mapM_ (\example -> putStrLn (exampleName example ++ ":\n " ++ exampleString example ++ "\n")) examplesList

-- Parse a definition line of the form "<name> : <type>"
parseDefine :: String -> Either String (String, Ty)
parseDefine s =
  case break (== ':') s of
    (lhs, ':' : rhs) ->
      let name  = trim lhs
          tyStr = trim rhs
      in if null name || null tyStr
           then Left "Usage: :define <name> : <type>"
           else Right (name, parseTyp tyStr)
    _ -> Left "Usage: :define <name> : <type>"
  where
    trim = f . f
      where f = reverse . dropWhile isSpace