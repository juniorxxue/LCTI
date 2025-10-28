module Main where
import Parser (parseTyp, parseTerm)
import Control.Monad.Writer
import Examples (examplesList, Example(exampleName, exampleString), preEnvStrings)
import Convert (convertNamedTerm, convertNamedEnv)
import AST (NamedEnv(..))
import Infer
import qualified Syntax as S
import System.Console.Haskeline
import qualified Data.Text as T

preEnvNamed :: NamedEnv
preEnvNamed = foldr (\(name, tyStr) env -> ETrm name (parseTyp tyStr) env) EEmpty preEnvStrings

preEnv :: S.Env
preEnv = Convert.convertNamedEnv preEnvNamed


main :: IO ()
main = do
  putStrLn "Welcome to the type inference REPL of Fc. Type :q to quit."
  putStrLn "Available commands: :tree, :env, :examples"
  runInputT defaultSettings repl

repl :: InputT IO ()
repl = do
  minput <- getInputLine "> "
  case minput of
    Nothing   -> liftIO $ putStrLn "Bye."
    Just ":q" -> liftIO $ putStrLn "Bye."
    Just input
      | Just rest <- stripPrefix ":tree " input -> liftIO (showTree rest) >> repl
      | Just rest <- stripPrefix ":env" input   -> liftIO showEnvNamed >> repl
      | Just rest <- stripPrefix ":examples" input -> liftIO showExamples >> repl
      | otherwise                               -> liftIO (showInfer input) >> repl

showInfer :: String -> IO ()
showInfer src = do
  let term = convertNamedTerm preEnvNamed (parseTerm src)
  case runWriterT $ infer preEnv S.CEmpty term of
    Just (ty, _) -> putStrLn (show ty)
    Nothing      -> putStrLn "failure"

showTree :: String -> IO ()
showTree src = do
  let term = convertNamedTerm preEnvNamed (parseTerm src)
  case runWriterT $ infer preEnv S.CEmpty term of
    Just (_, logs) -> putStr (unlines logs)
    Nothing        -> putStrLn "failure"

showEnvNamed :: IO ()
showEnvNamed = putStrLn (show preEnvNamed)


stripPrefix :: String -> String -> Maybe String
stripPrefix pre s =
  if take (length pre) s == pre then Just (drop (length pre) s) else Nothing

showExamples :: IO ()
showExamples =
  mapM_ (\example -> putStrLn (exampleName example ++ ":\n " ++ exampleString example ++ "\n")) examplesList