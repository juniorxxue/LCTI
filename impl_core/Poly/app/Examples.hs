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
  Map.fromList
    [ ("A1", ["A1", "A1 (Fc translation 1)", "A1 (Fc translation 2)", "A1 (uncurried)", "A1 (Fc translation 1, uncurried)", "A1 (Fc translation 2, uncurried)"]),
      ("A2", ["A2", "A2 (uncurried)"]),
      ("A3", ["A3", "A3 (Fc translation)", "A3 (uncurried)", "A3 (Fc translation, uncurried)"]),
      ("A4", ["A4", "A4 (Fc translation 1)", "A4 (Fc translation 2)", "A4 (uncurried)", "A4 (Fc translation 1, uncurried)", "A4 (Fc translation 2, uncurried)"]),
      ("A5", ["A5", "A5 (uncurried)"]),
      ("A6", ["A6", "A6 (uncurried)"]),
      ("A7", ["A7", "A7 (Fc translation)", "A7 (uncurried)", "A7 (Fc translation, uncurried)"]),
      ("A8", ["A8", "A8 (Fc translation 1)", "A8 (Fc translation 2)", "A8 (Fc translation 3)", "A8 (uncurried)", "A8 (Fc translation 1, uncurried)", "A8 (Fc translation 2, uncurried)", "A8 (Fc translation 3, uncurried)"]),
      ("A9", ["A9"]),
      ("A10", ["A10", "A10 (uncurried)"]),
      ("A11", ["A11", "A11 (Fc translation)", "A11 (uncurried)", "A11 (Fc translation, uncurried)"]),
      ("A12", ["A12", "A12 (Fc translation)", "A12 (uncurried)", "A12 (Fc translation, uncurried)"]),
      ("B1", ["B1", "B1 (Fc translation 1)", "B1 (Fc translation 2)", "B1 (uncurried)", "B1 (Fc translation 1, uncurried)", "B1 (Fc translation 2, uncurried)"]),
      ("B2", ["B2", "B2 (Fc translation 1)", "B2 (Fc translation 2)", "B2 (uncurried)", "B2 (Fc translation 1, uncurried)", "B2 (Fc translation 2, uncurried)"]),
      ("C1", ["C1", "C1 (uncurried)"]),
      ("C2", ["C2", "C2 (uncurried)"]),
      ("C3", ["C3", "C3 (uncurried)"]),
      ("C4", ["C4", "C4 (uncurried)"]),
      ("C5", ["C5", "C5 (uncurried)"]),
      ("C6", ["C6", "C6 (Fc translation 1)", "C6 (Fc translation 2)", "C6 (uncurried)", "C6 (Fc translation 1, uncurried)", "C6 (Fc translation 2, uncurried)"]),
      ("C7", ["C7", "C7 (Fc translation)", "C7 (uncurried)", "C7 (Fc translation, uncurried)"]),
      ("C8", ["C8", "C8 (uncurried)"]),
      ("C9", ["C9", "C9 (uncurried)"]),
      ("C10", ["C10", "C10 (Fc translation)", "C10 (uncurried)", "C10 (Fc translation, uncurried)"]),
      ("D1", ["D1", "D1 (uncurried)"]),
      ("D2", ["D2", "D2 (uncurried)"]),
      ("D3", ["D3", "D3 (uncurried)"]),
      ("D4", ["D4", "D4 (Fc translation 1)", "D4 (Fc translation 2)", "D4 (Fc translation 3)", "D4 (uncurried)", "D4 (Fc translation 1, uncurried)", "D4 (Fc translation 2, uncurried)", "D4 (Fc translation 3, uncurried)"]),
      ("D5", ["D5", "D5 (Fc translation 1)", "D5 (Fc translation 2)", "D5 (uncurried)", "D5 (Fc translation 1, uncurried)", "D5 (Fc translation 2, uncurried)"]),
      ("E1", ["E1", "E1 (uncurried)"]),
      ("E2", ["E2", "E2 (Fc translation 1)", "E2 (Fc translation 2)", "E2 (uncurried)", "E2 (Fc translation 1, uncurried)", "E2 (Fc translation 2, uncurried)"]),
      ("E3", ["E3", "E3 (Fc translation 1)", "E3 (Fc translation 2)", "E3 (uncurried)", "E3 (Fc translation 1, uncurried)", "E3 (Fc translation 2, uncurried)"]),
      ("F5", ["F5", "F5 (uncurried)"]),
      ("F6", ["F6", "F6 (uncurried)"]),
      ("F7", ["F7", "F7 (uncurried)"]),
      ("F8", ["F8"]),
      ("Pair", ["Pair", "Pair (Fc translation 1)", "Pair (Fc translation 2)", "Pair (uncurried)", "Pair (Fc translation 1, uncurried)", "Pair (Fc translation 2, uncurried)"]),
      ("Const", ["Const", "Const (uncurried)"]),
      ( "Uncurry",
        [ "A1 (uncurried)",
          "A1 (Fc translation 1, uncurried)",
          "A1 (Fc translation 2, uncurried)",
          "A2 (uncurried)",
          "A3 (uncurried)",
          "A3 (Fc translation, uncurried)",
          "A4 (uncurried)",
          "A4 (Fc translation 1, uncurried)",
          "A4 (Fc translation 2, uncurried)",
          "A5 (uncurried)",
          "A6 (uncurried)",
          "A7 (uncurried)",
          "A7 (Fc translation, uncurried)",
          "A8 (uncurried)",
          "A8 (Fc translation 1, uncurried)",
          "A8 (Fc translation 2, uncurried)",
          "A8 (Fc translation 3, uncurried)",
          "A9 (uncurried)",
          "A10 (uncurried)",
          "A11 (uncurried)",
          "A11 (Fc translation, uncurried)",
          "A12 (uncurried)",
          "A12 (Fc translation, uncurried)",
          "B1 (uncurried)",
          "B1 (Fc translation 1, uncurried)",
          "B1 (Fc translation 2, uncurried)",
          "B2 (uncurried)",
          "B2 (Fc translation 1, uncurried)",
          "B2 (Fc translation 2, uncurried)",
          "C1 (uncurried)",
          "C2 (uncurried)",
          "C3 (uncurried)",
          "C4 (uncurried)",
          "C5 (uncurried)",
          "C6 (uncurried)",
          "C6 (Fc translation 1, uncurried)",
          "C6 (Fc translation 2, uncurried)",
          "C7 (uncurried)",
          "C7 (Fc translation, uncurried)",
          "C8 (uncurried)",
          "C9 (uncurried)",
          "C10 (uncurried)",
          "C10 (Fc translation, uncurried)",
          "D1 (uncurried)",
          "D2 (uncurried)",
          "D3 (uncurried)",
          "D4 (uncurried)",
          "D4 (Fc translation 1, uncurried)",
          "D4 (Fc translation 2, uncurried)",
          "D4 (Fc translation 3, uncurried)",
          "D5 (uncurried)",
          "D5 (Fc translation 1, uncurried)",
          "D5 (Fc translation 2, uncurried)",
          "E1 (uncurried)",
          "E2 (uncurried)",
          "E2 (Fc translation 1, uncurried)",
          "E2 (Fc translation 2, uncurried)",
          "E3 (uncurried)",
          "E3 (Fc translation 1, uncurried)",
          "E3 (Fc translation 2, uncurried)",
          "F5 (uncurried)",
          "F6 (uncurried)",
          "F7 (uncurried)",
          "F8 (uncurried)",
          "Pair (uncurried)",
          "Pair (Fc translation 1, uncurried)",
          "Pair (Fc translation 2, uncurried)",
          "Const (uncurried)"
        ]
      )
    ]

getExamplesInGroup :: String -> [Example]
getExamplesInGroup groupName = case Map.lookup groupName exampleGroups of
  Just names -> mapMaybe getExample names
  Nothing -> []

groupNames :: [String]
groupNames = Map.keys exampleGroups

idTyp :: Typ
idTyp = TForall (TArr (TVar 0) (TVar 0))

idTypUncurry :: Typ
idTypUncurry = TForall $ TUncurry [TVar 0] (TVar 0)

idTrm :: Trm
idTrm = TAbs (Ann (Abs (Var 0)) (TArr (TVar 0) (TVar 0)))

idTrmUncurry :: Trm
idTrmUncurry = TAbs (Ann (AbsUncurry 1 (Var 0)) (TUncurry [TVar 0] (TVar 0)))

chooseTyp :: Typ
chooseTyp = TForall $ TArr (TVar 0) $ TArr (TVar 0) (TVar 0)

chooseTypUncurry :: Typ
chooseTypUncurry = TForall $ TUncurry [TVar 0, TVar 0] (TVar 0)

autoTyp :: Typ
autoTyp = idTyp `TArr` idTyp

autoTypUncurry :: Typ
autoTypUncurry = TUncurry [idTypUncurry] idTypUncurry

auto'Typ :: Typ
auto'Typ = TForall $ TArr idTyp $ TArr (TVar 0) (TVar 0)

auto'TypUncurry :: Typ
auto'TypUncurry = TForall $ TUncurry [idTypUncurry] (TUncurry [TVar 0] (TVar 0))

polyTyp :: Typ
polyTyp = idTyp `TArr` TProd TInt TBool

polyTypUncurry :: Typ
polyTypUncurry = TUncurry [idTypUncurry] (TProd TInt TBool)

headTyp :: Typ
headTyp = TForall $ TArr (TList (TVar 0)) (TVar 0)

headTypUncurry :: Typ
headTypUncurry = TForall $ TUncurry [TList (TVar 0)] (TVar 0)

tailTyp :: Typ
tailTyp = TForall $ TArr (TList (TVar 0)) (TList (TVar 0))

tailTypUncurry :: Typ
tailTypUncurry = TForall $ TUncurry [TList (TVar 0)] (TList (TVar 0))

lengthTyp :: Typ
lengthTyp = TForall $ TArr (TList (TVar 0)) TInt

lengthTypUncurry :: Typ
lengthTypUncurry = TForall $ TUncurry [TList (TVar 0)] TInt

singleTyp :: Typ
singleTyp = TForall $ TArr (TVar 0) (TList (TVar 0))

singleTypUncurry :: Typ
singleTypUncurry = TForall $ TUncurry [TVar 0] (TList (TVar 0))

appendTyp :: Typ
appendTyp = TForall $ TArr (TList (TVar 0)) $ TArr (TList (TVar 0)) (TList (TVar 0))

appendTypUncurry :: Typ
appendTypUncurry = TForall $ TUncurry [TList (TVar 0), TList (TVar 0)] (TList (TVar 0))

incTyp :: Typ
incTyp = TArr TInt TInt

incTypUncurry :: Typ
incTypUncurry = TUncurry [TInt] TInt

mapTyp :: Typ
mapTyp = TForall $ TForall $ TArr (TArr (TVar 1) (TVar 0)) $ TArr (TList (TVar 1)) (TList (TVar 0))

mapTypUncurry :: Typ
mapTypUncurry = TForall $ TForall $ TUncurry [TUncurry [TVar 1] (TVar 0), TList (TVar 1)] (TList (TVar 0))

appTyp :: Typ
appTyp = TForall $ TForall $ TArr (TArr (TVar 1) (TVar 0)) $ TArr (TVar 1) (TVar 0)

appTypUncurry :: Typ
appTypUncurry = TForall $ TForall $ TUncurry [TUncurry [TVar 1] (TVar 0), TVar 1] (TVar 0)

revappTyp :: Typ
revappTyp = TForall $ TForall $ TArr (TVar 1) $ TArr (TArr (TVar 1) (TVar 0)) (TVar 0)

revappTypUncurry :: Typ
revappTypUncurry = TForall $ TForall $ TUncurry [TVar 1, TUncurry [TVar 1] (TVar 0)] (TVar 0)

runSTTyp :: Typ
runSTTyp = TForall $ TArr (TForall $ TST (TVar 0) (TVar 1)) (TVar 0)

runSTTypUncurry :: Typ
runSTTypUncurry = TForall $ TUncurry [TForall $ TST (TVar 0) (TVar 1)] (TVar 0)

argSTTyp :: Typ
argSTTyp = TForall $ TST (TVar 0) TInt

fTyp :: Typ
fTyp = TForall $ TArr (TArr (TVar 0) (TVar 0)) $ TArr (TList (TVar 0)) (TVar 0)

fTypUncurry :: Typ
fTypUncurry = TForall $ TUncurry [TUncurry [TVar 0] (TVar 0), TList (TVar 0)] (TVar 0)

hTyp :: Typ
hTyp = TArr TInt idTyp

hTypUncurry :: Typ
hTypUncurry = TUncurry [TInt] idTypUncurry

kTyp :: Typ
kTyp = TForall $ TArr (TVar 0) $ TArr (TList (TVar 0)) (TVar 0)

kTypUncurry :: Typ
kTypUncurry = TForall $ TUncurry [TVar 0] $ TUncurry [TList (TVar 0)] (TVar 0)

lstTyp :: Typ
lstTyp = TList $ TForall $ TArr TInt $ TArr (TVar 0) (TVar 0)

lstTypUncurry :: Typ
lstTypUncurry = TList $ TForall $ TUncurry [TInt] $ TUncurry [TVar 0] (TVar 0)

rTyp :: Typ
rTyp = TArr (TForall (TArr (TVar 0) idTyp)) TInt

rTypUncurry :: Typ
rTypUncurry = TUncurry [TForall $ TUncurry [TVar 0] idTypUncurry] TInt

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
      "A1"
      EEmpty
      (Abs (Abs (Var 0)))
      "λx. λy. y",
    Example
      "A1 (Fc translation 1)"
      EEmpty
      (TAbs $ TAbs $ Ann (Abs (Abs (Var 0))) (TArr (TVar 1) (TArr (TVar 0) (TVar 0))))
      "Λa. Λb. (λx. λy. y) : a → b → b",
    Example
      "A1 (Fc translation 1, uncurried)"
      EEmpty
      (TAbs $ TAbs $ Ann (AbsUncurry 2 (Var 0)) (TUncurry [TVar 1, TVar 0] (TVar 0)))
      "Λa. Λb. (λ(x, y). y) : (a, b) → b",
    Example
      "A1 (Fc translation 2)"
      EEmpty
      (TAbs $ TAbs $ AbsAnn (TVar 1) $ AbsAnn (TVar 0) $ Var 0)
      "Λa. Λb. λx : a. λy : b. y",
    Example
      "A1 (Fc translation 2, uncurried)"
      EEmpty
      (TAbs $ TAbs $ AbsUncurryAnn [TVar 1, TVar 0] $ Var 0)
      "Λa. Λb. λ(x : a, y : b). y",
    Example
      "A2"
      (ETrm idTyp (ETrm chooseTyp EEmpty))
      (Var 1 `App` Var 0)
      "choose id",
    Example
      "A3"
      (ETrm (TList idTyp) (ETrm chooseTyp EEmpty))
      (Var 1 `App` Nil `App` Var 0)
      "choose Nil ids",
    Example
      "A3 (Fc translation)"
      (ETrm (TList idTyp) (ETrm chooseTyp EEmpty))
      (Var 1 `App` (Nil `Ann` TList idTyp) `App` Var 0)
      "choose (Nil : [∀a. a → a]) ids",
    Example
      "A3 (uncurried)"
      (ETrm (TList idTypUncurry) (ETrm chooseTypUncurry EEmpty))
      (Var 1 `AppUncurry` [Nil, Var 0])
      "choose(Nil, ids)",
    Example
      "A3 (Fc translation, uncurried)"
      (ETrm (TList idTypUncurry) (ETrm chooseTypUncurry EEmpty))
      (Var 1 `AppUncurry` [Nil `Ann` TList idTypUncurry, Var 0])
      "choose(Nil : [∀a. (a) → a], ids)",
    Example
      "A4"
      EEmpty
      (Abs (App (Var 0) (Var 0)))
      "λx. x x",
    Example
      "A4 (Fc translation 1)"
      EEmpty
      (Abs (App (Var 0) (Var 0)) `Ann` autoTyp)
      "(λx. x x) : (∀a. a → a) → (∀a. a → a)",
    Example
      "A4 (Fc translation 2)"
      EEmpty
      (AbsAnn idTyp (App (Var 0) (Var 0)))
      "λx : (∀a. a → a). x x",
    Example
      "A4 (uncurried)"
      EEmpty
      (AbsUncurry 1 (App (Var 0) (Var 0)))
      "λ(x). x x",
    Example
      "A4 (Fc translation 1, uncurried)"
      EEmpty
      (AbsUncurry 1 (AppUncurry (Var 0) [Var 0]) `Ann` autoTypUncurry)
      "(λ(x). x(x)) : (∀a. (a) → a) → (∀a. (a) → a)",
    Example
      "A4 (Fc translation 2, uncurried)"
      EEmpty
      (AbsUncurryAnn [idTypUncurry] (AppUncurry (Var 0) [Var 0]))
      "λ(x : ∀a. (a) → a). x(x)",
    Example
      "A5"
      (ETrm idTyp (ETrm autoTyp EEmpty))
      (Var 0 `App` Var 1)
      "id auto",
    Example
      "A5 (uncurried)"
      (ETrm idTypUncurry (ETrm autoTypUncurry EEmpty))
      (Var 0 `AppUncurry` [Var 1])
      "id(auto)",
    Example
      "A6"
      (ETrm idTyp (ETrm auto'Typ EEmpty))
      (Var 0 `App` Var 1)
      "id auto'",
    Example
      "A6 (uncurried)"
      (ETrm idTypUncurry (ETrm auto'TypUncurry EEmpty))
      (Var 0 `AppUncurry` [Var 1])
      "id(auto')",
    Example
      "A7"
      (ETrm chooseTyp (ETrm idTyp (ETrm autoTyp EEmpty)))
      (Var 0 `App` Var 1 `App` Var 2)
      "choose id auto",
    Example
      "A7 (Fc translation)"
      (ETrm chooseTyp (ETrm idTyp (ETrm autoTyp EEmpty)))
      (Var 0 `App` (Var 1 `TApp` idTyp) `App` Var 2)
      "choose (id @ (∀a. a → a)) auto",
    Example
      "A7 (uncurried)"
      (ETrm chooseTypUncurry (ETrm idTypUncurry (ETrm autoTypUncurry EEmpty)))
      (Var 0 `AppUncurry` [Var 1, Var 2])
      "choose(id, auto)",
    Example
      "A7 (Fc translation, uncurried)"
      (ETrm chooseTypUncurry (ETrm idTypUncurry (ETrm autoTypUncurry EEmpty)))
      (Var 0 `AppUncurry` [Var 1 `TApp` idTypUncurry, Var 2])
      "choose(id @ (∀a. (a) → a), auto)",
    Example
      "A8"
      (ETrm chooseTyp (ETrm idTyp (ETrm auto'Typ EEmpty)))
      (Var 0 `App` Var 1 `App` Var 2)
      "choose id auto'",
    Example
      "A8 (Fc translation 1)"
      (ETrm chooseTyp (ETrm idTyp (ETrm auto'Typ EEmpty)))
      (Var 0 `App` TAbs (Abs (Var 2 `App` (Var 0 `TApp` TVar 0)) `Ann` TArr idTyp (TArr (TVar 0) (TVar 0))) `App` Var 2)
      "choose (Λa. λf. id f @a : (∀b. b → b) → a → a) auto'",
    Example
      "A8 (Fc translation 2)"
      (ETrm chooseTyp (ETrm idTyp (ETrm auto'Typ EEmpty)))
      (Var 0 `App` TAbs (Abs (Abs (Var 3 `App` Var 1 `App` Var 0)) `Ann` TArr idTyp (TArr (TVar 0) (TVar 0))) `App` Var 2)
      "choose (Λa. λf. λx. id f x : (∀b. b → b) → a → a) auto'",
    Example
      "A8 (Fc translation 3)"
      (ETrm chooseTyp (ETrm idTyp (ETrm auto'Typ EEmpty)))
      (Var 0 `App` TAbs (AbsAnn idTyp (Var 2 `App` (Var 0 `TApp` TVar 0)) `Ann` TArr idTyp (TArr (TVar 0) (TVar 0))) `App` Var 2)
      "choose (Λa. λf : ∀b. b → b. id f @a) auto'",
    Example
      "A8 (uncurried)"
      (ETrm chooseTypUncurry (ETrm idTypUncurry (ETrm auto'TypUncurry EEmpty)))
      (Var 0 `AppUncurry` [Var 1, Var 2])
      "choose(id, auto')",
    Example
      "A8 (Fc translation 1, uncurried)"
      (ETrm chooseTypUncurry (ETrm idTypUncurry (ETrm auto'TypUncurry EEmpty)))
      (Var 0 `AppUncurry` [TAbs (AbsUncurry 1 (Var 2 `AppUncurry` [Var 0 `TApp` TVar 0]) `Ann` TUncurry [idTypUncurry] (TUncurry [TVar 0] (TVar 0))), Var 2])
      "choose(Λa. λ(f). id(f @a) : (∀b. (b) → b) → (a) → a, auto')",
    Example
      "A8 (Fc translation 2, uncurried)"
      (ETrm chooseTypUncurry (ETrm idTypUncurry (ETrm auto'TypUncurry EEmpty)))
      (Var 0 `AppUncurry` [TAbs (AbsUncurry 1 (AbsUncurry 1 (Var 3 `AppUncurry` [Var 1 `AppUncurry` [Var 0]])) `Ann` TUncurry [idTypUncurry] (TUncurry [TVar 0] (TVar 0))), Var 2])
      "choose(Λa. λ(f). λ(x). id(f)(x) : (∀b. (b) → b) → (a) → a, auto')",
    Example
      "A8 (Fc translation 3, uncurried)"
      (ETrm chooseTypUncurry (ETrm idTypUncurry (ETrm auto'TypUncurry EEmpty)))
      (Var 0 `AppUncurry` [TAbs (AbsUncurryAnn [idTypUncurry] (Var 2 `AppUncurry` [Var 0 `TApp` TVar 0])), Var 2])
      "choose(Λa. λ(f : ∀b. (b) → b). id(f @a), auto')",
    Example
      "A9"
      (ETrm (TForall $ TArr (TArr (TVar 0) (TVar 0)) $ TArr (TList (TVar 0)) (TVar 0)) (ETrm chooseTyp (ETrm idTyp (ETrm (TList idTyp) EEmpty))))
      (Var 0 `App` (Var 1 `App` Var 2) `App` Var 3)
      "f (choose id) ids where f : ∀a. (a → a) → [a] → a",
    Example
      "A10"
      (ETrm polyTyp (ETrm idTyp EEmpty))
      (Var 0 `App` Var 1)
      "poly id",
    Example
      "A10 (uncurried)"
      (ETrm polyTypUncurry (ETrm idTypUncurry EEmpty))
      (Var 0 `AppUncurry` [Var 1])
      "poly(id)",
    Example
      "A11"
      (ETrm polyTyp EEmpty)
      (Var 0 `App` Abs (Var 0))
      "poly (λx. x)",
    Example
      "A11 (Fc translation)"
      (ETrm polyTyp EEmpty)
      (Var 0 `App` TAbs (Abs (Var 0)))
      "poly (Λa. λx. x)",
    Example
      "A11 (uncurried)"
      (ETrm polyTypUncurry EEmpty)
      (Var 0 `AppUncurry` [AbsUncurry 1 (Var 0)])
      "poly(λ(x). x)",
    Example
      "A11 (Fc translation, uncurried)"
      (ETrm polyTypUncurry EEmpty)
      (Var 0 `AppUncurry` [TAbs (AbsUncurry 1 (Var 0))])
      "poly(Λa. λx. x)",
    Example
      "A12"
      (ETrm idTyp (ETrm polyTyp EEmpty))
      (Var 0 `App` Var 1 `App` Abs (Var 0))
      "id poly (λx. x)",
    Example
      "A12 (Fc translation)"
      (ETrm idTyp (ETrm polyTyp EEmpty))
      (Var 0 `App` Var 1 `App` TAbs (Abs (Var 0)))
      "id poly (Λa. λx. x)",
    Example
      "A12 (uncurried)"
      (ETrm idTypUncurry (ETrm polyTypUncurry EEmpty))
      (Var 0 `AppUncurry` [Var 1] `AppUncurry` [Abs (Var 0)])
      "id(poly)(λ(x). x)",
    Example
      "A12 (Fc translation, uncurried)"
      (ETrm idTypUncurry (ETrm polyTypUncurry EEmpty))
      (Var 0 `AppUncurry` [Var 1] `AppUncurry` [TAbs (AbsUncurry 1 (Var 0))])
      "id(poly)(Λa. λ(x). x)",
    Example
      "B1"
      EEmpty
      (Abs (Pair `App` (Var 0 `App` LitInt 1) `App` (Var 0 `App` LitBool True)))
      "λf. (f 1, f True)",
    Example
      "B1 (Fc translation 1)"
      EEmpty
      (Abs (Pair `App` (Var 0 `App` LitInt 1) `App` (Var 0 `App` LitBool True)) `Ann` (idTyp `TArr` TProd TInt TBool))
      "(λf. (f 1, f True)) : (∀a. a → a) → Int × Bool",
    Example
      "B1 (Fc translation 2)"
      EEmpty
      (AbsAnn idTyp (Pair `App` (Var 0 `App` LitInt 1) `App` (Var 0 `App` LitBool True)))
      "λf : ∀a. a → a. (f 1, f True)",
    Example
      "B1 (uncurried)"
      EEmpty
      (AbsUncurry 1 (PairUncurry `AppUncurry` [Var 0 `AppUncurry` [LitInt 1], Var 0 `AppUncurry` [LitBool True]]))
      "λ(f). (f(1), f(True))",
    Example
      "B1 (Fc translation 1, uncurried)"
      EEmpty
      (AbsUncurry 1 (PairUncurry `AppUncurry` [Var 0 `AppUncurry` [LitInt 1], Var 0 `AppUncurry` [LitBool True]]) `Ann` TUncurry [idTypUncurry] (TProd TInt TBool))
      "(λ(f). (f(1), f(True))) : (∀a. (a) → a) → Int × Bool",
    Example
      "B1 (Fc translation 2, uncurried)"
      EEmpty
      (AbsUncurryAnn [idTypUncurry] (PairUncurry `AppUncurry` [Var 0 `AppUncurry` [LitInt 1], Var 0 `AppUncurry` [LitBool True]]))
      "λ(f : ∀a. (a) → a). (f(1), f(True))",
    Example
      "B2"
      (ETrm polyTyp (ETrm headTyp EEmpty))
      (Abs (Var 1 `App` (Var 2 `App` Var 0)))
      "λxs. poly (head xs)",
    Example
      "B2 (Fc translation 1)"
      (ETrm polyTyp (ETrm headTyp EEmpty))
      (Abs (Var 1 `App` (Var 2 `App` Var 0)) `Ann` (TList idTyp `TArr` TProd TInt TBool))
      "(λxs. poly (head xs)) : [∀a. a → a] → Int × Bool",
    Example
      "B2 (Fc translation 2)"
      (ETrm polyTyp (ETrm headTyp EEmpty))
      (AbsAnn (TList idTyp) (Var 1 `App` (Var 2 `App` Var 0)))
      "λxs : [∀a. a → a]. poly (head xs)",
    Example
      "B2 (uncurried)"
      (ETrm polyTypUncurry (ETrm headTypUncurry EEmpty))
      (AbsUncurry 1 (Var 1 `AppUncurry` [Var 2 `AppUncurry` [Var 0]]))
      "λ(xs). poly(head(xs))",
    Example
      "B2 (Fc translation 1, uncurried)"
      (ETrm polyTypUncurry (ETrm headTypUncurry EEmpty))
      (AbsUncurry 1 (Var 1 `AppUncurry` [Var 2 `AppUncurry` [Var 0]]) `Ann` ([TList idTypUncurry] `TUncurry` TProd TInt TBool))
      "(λ(xs). poly(head(xs))) : [∀a. (a) → a] → Int × Bool",
    Example
      "B2 (Fc translation 2, uncurried)"
      (ETrm polyTypUncurry (ETrm headTypUncurry EEmpty))
      (AbsUncurryAnn [TList idTypUncurry] (Var 1 `AppUncurry` [Var 2 `AppUncurry` [Var 0]]))
      "λ(xs : [∀a. (a) → a]). poly(head(xs))",
    Example
      "C1"
      (ETrm lengthTyp (ETrm (TList idTyp) EEmpty))
      (Var 0 `App` Var 1)
      "length ids",
    Example
      "C1 (uncurried)"
      (ETrm lengthTypUncurry (ETrm (TList idTypUncurry) EEmpty))
      (Var 0 `AppUncurry` [Var 1])
      "length(ids)",
    Example
      "C2"
      (ETrm tailTyp (ETrm (TList idTyp) EEmpty))
      (Var 0 `App` Var 1)
      "tail ids",
    Example
      "C2 (uncurried)"
      (ETrm tailTypUncurry (ETrm (TList idTypUncurry) EEmpty))
      (Var 0 `AppUncurry` [Var 1])
      "tail(ids)",
    Example
      "C3"
      (ETrm headTyp (ETrm (TList idTyp) EEmpty))
      (Var 0 `App` Var 1)
      "head ids",
    Example
      "C3 (uncurried)"
      (ETrm headTypUncurry (ETrm (TList idTypUncurry) EEmpty))
      (Var 0 `AppUncurry` [Var 1])
      "head(ids)",
    Example
      "C4"
      (ETrm singleTyp (ETrm idTyp EEmpty))
      (Var 0 `App` Var 1)
      "single id",
    Example
      "C4 (uncurried)"
      (ETrm singleTypUncurry (ETrm idTyp EEmpty))
      (Var 0 `AppUncurry` [Var 1])
      "single(id)",
    Example
      "C5"
      (ETrm idTyp (ETrm (TList idTyp) EEmpty))
      (Cons `App` Var 0 `App` Var 1)
      "cons id ids",
    Example
      "C5 (uncurried)"
      (ETrm idTypUncurry (ETrm (TList idTypUncurry) EEmpty))
      (ConsUncurry `AppUncurry` [Var 0, Var 1])
      "cons(id, ids)",
    Example
      "C6"
      (ETrm (TList idTyp) EEmpty)
      (Cons `App` Abs (Var 0) `App` Var 0)
      "cons (λx. x) ids",
    Example
      "C6 (Fc translation 1)"
      (ETrm (TList idTyp) EEmpty)
      (Cons `App` idTrm `App` Var 0)
      "cons (Λa. λx. x : a → a) ids",
    Example
      "C6 (Fc translation 2)"
      (ETrm (TList idTyp) EEmpty)
      (Cons `App` TAbs (AbsAnn (TVar 0) (Var 0)) `App` Var 0)
      "cons (Λa. λx : a. x) ids",
    Example
      "C6 (uncurried)"
      (ETrm (TList idTypUncurry) EEmpty)
      (ConsUncurry `AppUncurry` [AbsUncurry 1 (Var 0), Var 0])
      "cons(λ(x). x, ids)",
    Example
      "C6 (Fc translation 1, uncurried)"
      (ETrm (TList idTypUncurry) EEmpty)
      (ConsUncurry `AppUncurry` [idTrmUncurry, Var 0])
      "cons(Λa. λ(x). x : (a) → a, ids)",
    Example
      "C6 (Fc translation 2, uncurried)"
      (ETrm (TList idTypUncurry) EEmpty)
      (ConsUncurry `AppUncurry` [TAbs (AbsUncurryAnn [TVar 0] (Var 0)), Var 0])
      "cons(Λa. λ(x : a). x, ids)",
    Example
      "C7"
      (ETrm appendTyp (ETrm singleTyp (ETrm incTyp (ETrm idTyp EEmpty))))
      (Var 0 `App` (Var 1 `App` Var 2) `App` (Var 1 `App` Var 3))
      "append (single inc) (single id)",
    Example
      "C7 (Fc translation)"
      (ETrm appendTyp (ETrm singleTyp (ETrm incTyp (ETrm idTyp EEmpty))))
      (Var 0 `App` (Var 1 `App` Var 2) `App` (Var 1 `App` (Var 3 `TApp` TInt)))
      "append (single inc) (single (id @ Int))",
    Example
      "C7 (uncurried)"
      (ETrm appendTypUncurry (ETrm singleTypUncurry (ETrm incTypUncurry (ETrm idTypUncurry EEmpty))))
      (Var 0 `AppUncurry` [Var 1 `AppUncurry` [Var 2], Var 1 `AppUncurry` [Var 3]])
      "append(single(inc), single(id))",
    Example
      "C7 (Fc translation, uncurried)"
      (ETrm appendTypUncurry (ETrm singleTypUncurry (ETrm incTypUncurry (ETrm idTypUncurry EEmpty))))
      (Var 0 `AppUncurry` [Var 1 `AppUncurry` [Var 2], Var 1 `AppUncurry` [Var 3 `TApp` TInt]])
      "append(single(inc), single(id @ Int))",
    Example
      "C8"
      (ETrm appendTyp (ETrm singleTyp (ETrm idTyp (ETrm (TList idTyp) EEmpty))))
      (Var 0 `App` (Var 1 `App` Var 2) `App` Var 3)
      "append (single id) ids",
    Example
      "C8 (uncurried)"
      (ETrm appendTypUncurry (ETrm singleTypUncurry (ETrm idTypUncurry (ETrm (TList idTypUncurry) EEmpty))))
      (Var 0 `AppUncurry` [Var 1 `AppUncurry` [Var 2], Var 3])
      "append(single(id), ids)",
    Example
      "C9"
      (ETrm mapTyp (ETrm polyTyp (ETrm singleTyp (ETrm idTyp EEmpty))))
      (Var 0 `App` Var 1 `App` (Var 2 `App` Var 3))
      "map poly (single id)",
    Example
      "C9 (uncurried)"
      (ETrm mapTypUncurry (ETrm polyTypUncurry (ETrm singleTypUncurry (ETrm idTypUncurry EEmpty))))
      (Var 0 `AppUncurry` [Var 1, Var 2 `AppUncurry` [Var 3]])
      "map(poly, single(id))",
    Example
      "C10"
      (ETrm mapTyp (ETrm headTyp (ETrm singleTyp (ETrm (TList idTyp) EEmpty))))
      (Var 0 `App` Var 1 `App` (Var 2 `App` Var 3))
      "map head (single ids)",
    Example
      "C10 (Fc translation)"
      (ETrm mapTyp (ETrm headTyp (ETrm singleTyp (ETrm (TList idTyp) EEmpty))))
      (Var 0 `App` (Var 1 `TApp` idTyp) `App` (Var 2 `App` Var 3))
      "map (head @ (∀a. a → a)) (single ids)",
    Example
      "C10 (uncurried)"
      (ETrm mapTypUncurry (ETrm headTypUncurry (ETrm singleTypUncurry (ETrm (TList idTypUncurry) EEmpty))))
      (Var 0 `AppUncurry` [Var 1, Var 2 `AppUncurry` [Var 3]])
      "map(head, single(ids))",
    Example
      "C10 (Fc translation, uncurried)"
      (ETrm mapTypUncurry (ETrm headTypUncurry (ETrm singleTypUncurry (ETrm (TList idTypUncurry) EEmpty))))
      (Var 0 `AppUncurry` [Var 1 `TApp` idTypUncurry, Var 2 `AppUncurry` [Var 3]])
      "map(head @ (∀a. a → a), single(ids))",
    Example
      "D1"
      (ETrm appTyp (ETrm polyTyp (ETrm idTyp EEmpty)))
      (Var 0 `App` Var 1 `App` Var 2)
      "app poly id",
    Example
      "D1 (uncurried)"
      (ETrm appTypUncurry (ETrm polyTypUncurry (ETrm idTypUncurry EEmpty)))
      (Var 0 `AppUncurry` [Var 1, Var 2])
      "app(poly, id)",
    Example
      "D2"
      (ETrm revappTyp (ETrm idTyp (ETrm polyTyp EEmpty)))
      (Var 0 `App` Var 1 `App` Var 2)
      "revapp id poly",
    Example
      "D2 (uncurried)"
      (ETrm revappTypUncurry (ETrm idTypUncurry (ETrm polyTypUncurry EEmpty)))
      (Var 0 `AppUncurry` [Var 1, Var 2])
      "revapp(id, poly)",
    Example
      "D3"
      (ETrm runSTTyp (ETrm argSTTyp EEmpty))
      (Var 0 `App` Var 1)
      "runST argST",
    Example
      "D3 (uncurried)"
      (ETrm runSTTypUncurry (ETrm argSTTyp EEmpty))
      (Var 0 `AppUncurry` [Var 1])
      "runST(argST)",
    Example
      "D4"
      (ETrm appTyp (ETrm runSTTyp (ETrm argSTTyp EEmpty)))
      (Var 0 `App` Var 1 `App` Var 2)
      "app runST argST",
    Example
      "D4 (Fc translation 1)"
      (ETrm appTyp (ETrm runSTTyp (ETrm argSTTyp EEmpty)))
      (Var 0 `App` (Abs (Var 2 `App` TAbs (Var 0 `TApp` TVar 0)) `Ann` TArr argSTTyp TInt) `App` Var 2)
      "app (λx. runST (Λa. x @a) : (∀a. ST a Int) → Int) argST",
    Example
      "D4 (Fc translation 2)"
      (ETrm appTyp (ETrm runSTTyp (ETrm argSTTyp EEmpty)))
      (Var 0 `App` AbsAnn argSTTyp (Var 2 `App` TAbs (Var 0 `TApp` TVar 0)) `App` Var 2)
      "app (λx : ∀a. ST a Int. runST (Λa. x @a)) argST",
    Example
      "D4 (Fc translation 3)"
      (ETrm appTyp (ETrm runSTTyp (ETrm argSTTyp EEmpty)))
      (Var 0 `App` (Var 1 `TApp` TInt) `App` Var 2)
      "app (runST @Int) argST",
    Example
      "D4 (uncurried)"
      (ETrm appTypUncurry (ETrm runSTTypUncurry (ETrm argSTTyp EEmpty)))
      (Var 0 `AppUncurry` [Var 1, Var 2])
      "app(runST, argST)",
    Example
      "D4 (Fc translation 1, uncurried)"
      (ETrm appTypUncurry (ETrm runSTTypUncurry (ETrm argSTTyp EEmpty)))
      (Var 0 `AppUncurry` [AbsUncurry 1 (Var 2 `AppUncurry` [TAbs (Var 0 `TApp` TVar 0)]) `Ann` TUncurry [argSTTyp] TInt, Var 2])
      "app(λ(x). runST(Λa. x @a) : (∀a. ST a Int) → Int, argST)",
    Example
      "D4 (Fc translation 2, uncurried)"
      (ETrm appTypUncurry (ETrm runSTTypUncurry (ETrm argSTTyp EEmpty)))
      (Var 0 `AppUncurry` [AbsUncurryAnn [argSTTyp] (Var 2 `AppUncurry` [TAbs (Var 0 `TApp` TVar 0)]), Var 2])
      "app(λ(x : ∀a. ST a Int). runST(Λa. x @a), argST)",
    Example
      "D4 (Fc translation 3, uncurried)"
      (ETrm appTypUncurry (ETrm runSTTypUncurry (ETrm argSTTyp EEmpty)))
      (Var 0 `AppUncurry` [Var 1 `TApp` TInt, Var 2])
      "app(runST @Int, argST)",
    Example
      "D5"
      (ETrm revappTyp (ETrm argSTTyp (ETrm runSTTyp EEmpty)))
      (Var 0 `App` Var 1 `App` Var 2)
      "revapp argST runST",
    Example
      "D5 (Fc translation 1)"
      (ETrm revappTyp (ETrm argSTTyp (ETrm runSTTyp EEmpty)))
      (Var 0 `App` Var 1 `App` (Var 2 `TApp` TInt))
      "revapp argST (runST @Int)",
    Example
      "D5 (Fc translation 2)"
      (ETrm revappTyp (ETrm argSTTyp (ETrm runSTTyp EEmpty)))
      (Var 0 `App` Var 1 `App` (Abs (Var 3 `App` TAbs (Var 0 `TApp` TVar 0)) `Ann` TArr argSTTyp TInt))
      "revapp argST (λx. runST (Λa. x @a) : (∀a. ST a Int) → Int)",
    Example
      "D5 (uncurried)"
      (ETrm revappTypUncurry (ETrm argSTTyp (ETrm runSTTypUncurry EEmpty)))
      (Var 0 `AppUncurry` [Var 1, Var 2])
      "revapp(argST, runST)",
    Example
      "D5 (Fc translation 1, uncurried)"
      (ETrm revappTypUncurry (ETrm argSTTyp (ETrm runSTTypUncurry EEmpty)))
      (Var 0 `AppUncurry` [Var 1, Var 2 `TApp` TInt])
      "revapp(argST, runST @Int)",
    Example
      "D5 (Fc translation 2, uncurried)"
      (ETrm revappTypUncurry (ETrm argSTTyp (ETrm runSTTypUncurry EEmpty)))
      (Var 0 `AppUncurry` [Var 1, AbsUncurry 1 (Var 3 `AppUncurry` [TAbs (Var 0 `TApp` TVar 0)]) `Ann` TUncurry [argSTTyp] TInt])
      "revapp(argST, λ(x). runST(Λa. x @a) : (∀a. ST a Int) → Int)",
    Example
      "E1"
      (ETrm kTyp (ETrm hTyp (ETrm lstTyp EEmpty)))
      (Var 0 `App` Var 1 `App` Var 2)
      "k h lst",
    Example
      "E1 (uncurried)"
      (ETrm kTypUncurry (ETrm hTypUncurry (ETrm lstTypUncurry EEmpty)))
      (Var 0 `AppUncurry` [Var 1] `AppUncurry` [Var 2])
      "k(h)(lst)",
    Example
      "E2"
      (ETrm kTyp (ETrm hTyp (ETrm lstTyp EEmpty)))
      (Var 0 `App` Abs (Var 2 `App` Var 0) `App` Var 2)
      "k (λx. h x) lst",
    Example
      "E2 (Fc translation 1)"
      (ETrm kTyp (ETrm hTyp (ETrm lstTyp EEmpty)))
      (Var 0 `App` TAbs (Abs (Var 2 `App` Var 0 `TApp` TVar 0) `Ann` TArr TInt (TArr (TVar 0) (TVar 0))) `App` Var 2)
      "k (Λa. λx. h x @ a : Int → a → a) lst",
    Example
      "E2 (Fc translation 2)"
      (ETrm kTyp (ETrm hTyp (ETrm lstTyp EEmpty)))
      (Var 0 `App` TAbs (AbsAnn TInt (Var 2 `App` Var 0 `TApp` TVar 0)) `App` Var 2)
      "k (Λa. λx : Int. h x @ a) lst",
    Example
      "E2 (uncurried)"
      (ETrm kTypUncurry (ETrm hTypUncurry (ETrm lstTypUncurry EEmpty)))
      (Var 0 `AppUncurry` [AbsUncurry 1 (Var 2 `AppUncurry` [Var 0])] `AppUncurry` [Var 2])
      "k(λ(x). h(x))(lst)",
    Example
      "E2 (Fc translation 1, uncurried)"
      (ETrm kTypUncurry (ETrm hTypUncurry (ETrm lstTypUncurry EEmpty)))
      (Var 0 `AppUncurry` [TAbs (AbsUncurry 1 (Var 2 `AppUncurry` [Var 0] `TApp` TVar 0) `Ann` TUncurry [TInt] (TUncurry [TVar 0] (TVar 0)))] `AppUncurry` [Var 2])
      "k(Λa. λ(x). h(x) @ a : (Int) → (a) → a)(lst)",
    Example
      "E2 (Fc translation 2, uncurried)"
      (ETrm kTypUncurry (ETrm hTypUncurry (ETrm lstTypUncurry EEmpty)))
      (Var 0 `AppUncurry` [TAbs (AbsUncurryAnn [TInt] (Var 2 `AppUncurry` [Var 0] `TApp` TVar 0))] `AppUncurry` [Var 2])
      "k(Λa. λ(x : Int). h(x) @ a)(lst)",
    Example
      "E3"
      (ETrm rTyp EEmpty)
      (Var 0 `App` Abs (Abs (Var 0)))
      "r (λx. λy. y)",
    Example
      "E3 (Fc translation 1)"
      (ETrm rTyp EEmpty)
      (Var 0 `App` TAbs (Abs (TAbs (Abs (Var 0))) `Ann` TArr (TVar 0) idTyp))
      "r (Λ a. (λx. Λ b. λy. y) : a → ∀b. b → b)",
    Example
      "E3 (Fc translation 2)"
      (ETrm rTyp EEmpty)
      (Var 0 `App` TAbs (AbsAnn (TVar 0) (TAbs (AbsAnn (TVar 0) (Var 0)))))
      "r (Λa. λx : a. Λb. λy : b. y)",
    Example
      "E3 (uncurried)"
      (ETrm rTypUncurry EEmpty)
      (Var 0 `AppUncurry` [AbsUncurry 1 (AbsUncurry 1 (Var 0))])
      "r(λ(x). λ(y). y)",
    Example
      "E3 (Fc translation 1, uncurried)"
      (ETrm rTypUncurry EEmpty)
      (Var 0 `AppUncurry` [TAbs (AbsUncurry 1 (TAbs (AbsUncurry 1 (Var 0))) `Ann` TUncurry [TVar 0] idTypUncurry)])
      "r(Λ a. (λ(x). Λ b. λ(y). y) : (a) → ∀b. (b) → b)",
    Example
      "E3 (Fc translation 2, uncurried)"
      (ETrm rTypUncurry EEmpty)
      (Var 0 `AppUncurry` [TAbs (AbsUncurryAnn [TVar 0] (TAbs (AbsUncurryAnn [TVar 0] (Var 0))))])
      "r(Λa. λ(x : a). Λb. λ(y : b). y)",
    -- FreezeML paper additions
    Example
      "F5"
      (ETrm autoTyp (ETrm idTyp EEmpty))
      (Var 0 `App` Var 1)
      "auto id",
    Example
      "F5 (uncurried)"
      (ETrm autoTypUncurry (ETrm idTypUncurry EEmpty))
      (Var 0 `AppUncurry` [Var 1])
      "auto(id)",
    Example
      "F6"
      (ETrm headTyp (ETrm (TList idTyp) EEmpty))
      (Cons `App` (Var 0 `App` Var 1) `App` Var 1)
      "cons (head ids) ids",
    Example
      "F6 (uncurried)"
      (ETrm headTypUncurry (ETrm (TList idTypUncurry) EEmpty))
      (ConsUncurry `AppUncurry` [Var 0 `AppUncurry` [Var 1], Var 1])
      "cons(head(ids), ids)",
    Example
      "F7"
      (ETrm headTyp (ETrm (TList idTyp) EEmpty))
      (Var 0 `App` Var 1 `App` LitInt 3)
      "head ids 3",
    Example
      "F7 (uncurried)"
      (ETrm headTypUncurry (ETrm (TList idTypUncurry) EEmpty))
      (Var 0 `AppUncurry` [Var 1] `AppUncurry` [LitInt 3])
      "head(ids)(3)",
    Example
      "F8"
      (ETrm chooseTyp (ETrm headTyp (ETrm (TList idTyp) EEmpty)))
      (Var 0 `App` (Var 1 `App` Var 2))
      "choose (head ids)",
    -- Spine-local type inference
    Example
      "Pair"
      EEmpty
      ((Pair `App` Abs (Var 0) `App` LitInt 1) `Ann` ((TInt `TArr` TInt) `TProd` TInt))
      "(Pair (λx. x) 1) : (Int → Int) × Int",
    Example
      "Pair (Fc translation 1)"
      EEmpty
      ((Pair `App` (Abs (Var 0) `Ann` TArr TInt TInt) `App` LitInt 1) `Ann` ((TInt `TArr` TInt) `TProd` TInt))
      "(Pair (λx. x : Int → Int) 1) : (Int → Int) × Int",
    Example
      "Pair (Fc translation 2)"
      EEmpty
      ((Pair `App` AbsAnn TInt (Var 0) `App` LitInt 1) `Ann` ((TInt `TArr` TInt) `TProd` TInt))
      "(Pair (λx : Int. x) 1) : (Int → Int) × Int",
    Example
      "Pair (uncurried)"
      EEmpty
      ((PairUncurry `AppUncurry` [AbsUncurry 1 (Var 0), LitInt 1]) `Ann` (([TInt] `TUncurry` TInt) `TProd` TInt))
      "(Pair(λ(x). x, 1) : ((Int) → Int) × Int",
    Example
      "Pair (Fc translation 1, uncurried)"
      EEmpty
      ((PairUncurry `AppUncurry` [AbsUncurry 1 (Var 0) `Ann` TUncurry [TInt] TInt, LitInt 1]) `Ann` (([TInt] `TUncurry` TInt) `TProd` TInt))
      "(Pair(λ(x). x : (Int) → Int), 1) : ((Int) → Int) × Int",
    Example
      "Pair (Fc translation 2, uncurried)"
      EEmpty
      ((PairUncurry `AppUncurry` [AbsUncurryAnn [TInt] (Var 0), LitInt 1]) `Ann` (([TInt] `TUncurry` TInt) `TProd` TInt))
      "(Pair(λ(x : Int). x, 1) : ((Int) → Int) × Int",
    Example
      "Const"
      EEmpty
      (TAbs (TAbs (AbsAnn (TVar 1) (AbsAnn (TVar 0) (Var 1)))) `App` LitInt 1 `App` LitBool True)
      "(Λa. Λb. λx : a. λy : b. x) 1 True",
    Example
      "Const (uncurried)"
      EEmpty
      (TAbs (TAbs (AbsUncurryAnn [TVar 1] (AbsUncurryAnn [TVar 0] (Var 1)))) `AppUncurry` [LitInt 1] `AppUncurry` [LitBool True])
      "(Λa. Λb. λ(x : a). λ(y : b). x)(1)(True)"
  ]