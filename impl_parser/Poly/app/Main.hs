module Main where
import Parser (parseTyp, parseTerm)
import Control.Monad.Writer
import Examples (examplesList, Example(exampleName, exampleString), preEnvStrings)
import Convert (convertNamedTerm, convertNamedEnv)
import AST (NamedEnv(..))
import Infer
import qualified Syntax as S

preEnvNamed :: NamedEnv
preEnvNamed = foldr (\(name, tyStr) env -> ETrm name (parseTyp tyStr) env) EEmpty preEnvStrings

preEnv :: S.Env
preEnv = Convert.convertNamedEnv preEnvNamed

main :: IO ()
main = do
  -- print $ parseTerm "(lambda {x}. x {x}) : ({forall a. {a} -> a}) -> (forall a. {a} -> a)"
  -- print preEnv
  mapM_ (\example -> do
    putStrLn $ "Infering: " ++ exampleName example ++ ": " ++ exampleString example
    let _exp = convertNamedTerm preEnvNamed (parseTerm . exampleString $ example)
    putStrLn $ "Parsed term: " ++ show _exp
    case runWriterT $ infer preEnv S.CEmpty _exp of
      Just (tyA, logs) -> do
        putStrLn $ "[✓] Typing result: " ++ show tyA
      Nothing -> do
        putStrLn "[x] Typing failed"
    putStrLn "==============================="

    ) examplesList