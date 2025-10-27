module Main where
import System.Environment (getArgs)
import GHC.IO.Handle (hGetContents)
import GHC.IO.FD (stdin)
import Parser (parseTyp)

main :: IO ()
main = do
  let example1 = "forall a. a -> a"
  print (parseTyp example1)
  let example2 = "int"
  print (parseTyp example2)
  let example3 = "bool"
  print (parseTyp example3)
  let example4 = "ST int int"
  print (parseTyp example4)
  let example5 = "ST int bool"
  print (parseTyp example5)
  let example6 = "ST bool int"
  print (parseTyp example6)
  let example7 = "forall a. forall b. (a -> b) -> [a] -> [b]"
  print (parseTyp example7)
