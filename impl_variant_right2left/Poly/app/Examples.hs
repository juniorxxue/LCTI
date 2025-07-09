{-# LANGUAGE RankNTypes #-}

module Examples where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Syntax

data Example = Example
  { exampleName :: String,
    exampleEnv :: Env,
    exampleTerm :: Trm,
    exampleDescription :: String
  }

exampleGroups :: Map String [String]
exampleGroups =
  Map.fromList [ ("Pair", ["Pair"])]

getExamplesInGroup :: String -> [Example]
getExamplesInGroup groupName = case Map.lookup groupName exampleGroups of
  Just names -> mapMaybe getExample names
  Nothing -> []

groupNames :: [String]
groupNames = Map.keys exampleGroups

idTyp :: Typ
idTyp = TForall (TArr (TVar 0) (TVar 0))

idTrm :: Trm
idTrm = TAbs (Ann (Abs (Var 0)) (TArr (TVar 0) (TVar 0)))

chooseTyp :: Typ
chooseTyp = TForall $ TArr (TVar 0) $ TArr (TVar 0) (TVar 0)

autoTyp :: Typ
autoTyp = idTyp `TArr` idTyp

auto'Typ :: Typ
auto'Typ = TForall $ TArr idTyp $ TArr (TVar 0) (TVar 0)

polyTyp :: Typ
polyTyp = idTyp `TArr` TProd TInt TBool

headTyp :: Typ
headTyp = TForall $ TArr (TList (TVar 0)) (TVar 0)

tailTyp :: Typ
tailTyp = TForall $ TArr (TList (TVar 0)) (TList (TVar 0))

lengthTyp :: Typ
lengthTyp = TForall $ TArr (TList (TVar 0)) TInt

singleTyp :: Typ
singleTyp = TForall $ TArr (TVar 0) (TList (TVar 0))

appendTyp :: Typ
appendTyp = TForall $ TArr (TList (TVar 0)) $ TArr (TList (TVar 0)) (TList (TVar 0))

incTyp :: Typ
incTyp = TArr TInt TInt

mapTyp :: Typ
mapTyp = TForall $ TForall $ TArr (TArr (TVar 1) (TVar 0)) $ TArr (TList (TVar 1)) (TList (TVar 0))

appTyp :: Typ
appTyp = TForall $ TForall $ TArr (TArr (TVar 1) (TVar 0)) $ TArr (TVar 1) (TVar 0)

revappTyp :: Typ
revappTyp = TForall $ TForall $ TArr (TVar 1) $ TArr (TArr (TVar 1) (TVar 0)) (TVar 0)

runSTTyp :: Typ
runSTTyp = TForall $ TArr (TForall $ TST (TVar 0) (TVar 1)) (TVar 0)

argSTTyp :: Typ
argSTTyp = TForall $ TST (TVar 0) TInt

fTyp :: Typ
fTyp = TForall $ TArr (TArr (TVar 0) (TVar 0)) $ TArr (TList (TVar 0)) (TVar 0)

hTyp :: Typ
hTyp = TArr TInt idTyp

kTyp :: Typ
kTyp = TForall $ TArr (TVar 0) $ TArr (TList (TVar 0)) (TVar 0)

lstTyp :: Typ
lstTyp = TList $ TForall $ TArr TInt $ TArr (TVar 0) (TVar 0)

rTyp :: Typ
rTyp = TArr (TForall (TArr (TVar 0) idTyp)) TInt

examplesMap :: Map String Example
examplesMap = Map.fromList [(exampleName ex, ex) | ex <- examplesList]

exampleNames :: [String]
exampleNames = Map.keys examplesMap

getExample :: String -> Maybe Example
getExample name = Map.lookup name examplesMap

examples :: [Example]
examples = examplesList

examplesList :: [Example]
examplesList =
  [ Example
      "Pair"
      EEmpty
      ((Pair `App` Abs (Var 0) `App` LitInt 1) `Ann` ((TInt `TArr` TInt) `TProd` TInt))
      "(Pair (λx. x) 1) : (Int → Int) × Int"
  ]
