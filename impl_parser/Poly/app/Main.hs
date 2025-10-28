module Main where
import Parser (parseTyp, parseTerm)
import Control.Monad.Writer
import Examples (examplesList, Example(exampleName, exampleString), preEnvStrings)
import Convert (convertNamedTerm, convertNamedEnv)
import AST (NamedEnv(..))
import qualified AST as AST
import Infer
import qualified Syntax as S
import System.Console.Haskeline
import Data.Char (isSpace)

preEnvNamed :: NamedEnv
preEnvNamed = foldr (\(name, tyStr) env -> ETrm name (parseTyp tyStr) env) EEmpty preEnvStrings

preEnv :: S.Env
preEnv = Convert.convertNamedEnv preEnvNamed


main :: IO ()
main = do
  putStrLn "Welcome to the type inference REPL of Fc. Type :q to quit."
  putStrLn "Available commands: :tree, :env, :examples, :define <name> : <type>"
  runInputT defaultSettings (repl preEnvNamed preEnv)
-- The REPL maintains a current named environment and its de Bruijn-converted form
repl :: NamedEnv -> S.Env -> InputT IO ()
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
              let envNamed' = ETrm name tyNamed envNamed
                  env' = convertNamedEnv envNamed'
              -- Echo the defined type for convenience
              outputStrLn (show tyNamed)
              repl envNamed' env'
      | otherwise                                 -> liftIO (showInfer envNamed env input) >> repl envNamed env

showInfer :: NamedEnv -> S.Env -> String -> IO ()
showInfer envNamed env src = do
  let term = convertNamedTerm envNamed (parseTerm src)
  case runWriterT $ infer env S.CEmpty term of
    Just (ty, _) -> putStrLn (show ty)
    Nothing      -> putStrLn "failure"

showTree :: NamedEnv -> S.Env -> String -> IO ()
showTree envNamed env src = do
  let term = convertNamedTerm envNamed (parseTerm src)
  case runWriterT $ infer env S.CEmpty term of
    Just (_, logs) -> putStr (unlines logs)
    Nothing        -> putStrLn "failure"

showEnvNamed :: NamedEnv -> IO ()
showEnvNamed envNamed = putStrLn (show envNamed)


stripPrefix :: String -> String -> Maybe String
stripPrefix pre s =
  if take (length pre) s == pre then Just (drop (length pre) s) else Nothing

showExamples :: IO ()
showExamples =
  mapM_ (\example -> putStrLn (exampleName example ++ ":\n " ++ exampleString example ++ "\n")) examplesList

-- Parse a definition line of the form "<name> : <type>"
parseDefine :: String -> Either String (String, AST.NamedTyp)
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