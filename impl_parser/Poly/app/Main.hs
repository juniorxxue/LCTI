module Main where
import Parser (parseTyp, parseTerm)
import Examples (examplesList, Example(exampleName, exampleString))



main :: IO ()
main = do
  -- print $ parseTerm "(lambda {x}. x {x}) : ({forall a. {a} -> a}) -> (forall a. {a} -> a)"
  mapM_ (\example -> do
    putStrLn $ "Parsing: " ++ exampleName example
    print $ parseTerm (exampleString example)) examplesList