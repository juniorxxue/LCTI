{-# LANGUAGE RankNTypes #-}
module Examples where

import Syntax
import Data.Map (Map)
import qualified Data.Map as Map
-- We'll import the infer function from Main

-- Data structure for examples
data Example = Example 
  { exampleName :: String
  , exampleEnv :: Env
  , exampleTerm :: Trm
  , exampleDescription :: String
  }

-- Common type definitions
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

-- Convert list to map for easy lookup
examplesMap :: Map String Example
examplesMap = Map.fromList [(exampleName ex, ex) | ex <- examplesList]

-- Get all example names
exampleNames :: [String]
exampleNames = Map.keys examplesMap

-- Get a specific example by name
getExample :: String -> Maybe Example
getExample name = Map.lookup name examplesMap

-- List of all examples (for backward compatibility)
examples :: [Example]
examples = Map.elems examplesMap

-- Internal list of examples (used to build the map)
examplesList :: [Example]
examplesList = 
  [ Example "A1" EEmpty (Abs (Abs (Var 0))) 
      "λx. λy. y"
    
  , Example "A1Ann" EEmpty (TAbs $ TAbs $ Ann (Abs (Abs (Var 0))) (TArr (TVar 1) (TArr (TVar 0) (TVar 0))))
      "Λa. Λb. (λx. λy. y) : a → b → b"
    
  , Example "A1Ann'" EEmpty (TAbs $ TAbs $ AbsAnn (TVar 1) $ AbsAnn (TVar 0) $ Var 0)
      "Λa. Λb. λx : a. λy : b. y"
    
  , Example "A2" (ETrm idTyp (ETrm chooseTyp EEmpty)) (Var 1 `App` Var 0)
      "choose id"
    
  , Example "A3" (ETrm (TList idTyp) (ETrm chooseTyp EEmpty)) (Var 1 `App` Nil `App` Var 0)
      "choose Nil ids"
    
  , Example "A3Ann" (ETrm (TList idTyp) (ETrm chooseTyp EEmpty)) (Var 1 `App` (Nil `Ann` TList idTyp) `App` Var 0)
      "choose (Nil : [∀a. a → a]) ids"
    
  , Example "A4" EEmpty (Abs (App (Var 0) (Var 0)))
      "λx. x x"
    
  , Example "A4Ann" EEmpty (Abs (App (Var 0) (Var 0)) `Ann` autoTyp)
      "(λx. x x) : (∀a. a → a) → (∀a. a → a)"
    
  , Example "A4Ann'" EEmpty (AbsAnn idTyp (App (Var 0) (Var 0)))
      "λx : (∀a. a → a). x x"
    
  , Example "A5" (ETrm idTyp (ETrm autoTyp EEmpty)) (Var 0 `App` Var 1)
      "id auto"
    
  , Example "A6" (ETrm idTyp (ETrm auto'Typ EEmpty)) (Var 0 `App` Var 1)
      "id auto'"
    
  , Example "A7" (ETrm chooseTyp (ETrm idTyp (ETrm autoTyp EEmpty))) (Var 0 `App` Var 1 `App` Var 2)
      "choose id auto"
    
  , Example "A7Ann" (ETrm chooseTyp (ETrm idTyp (ETrm autoTyp EEmpty))) (Var 0 `App` (Var 1 `TApp` idTyp) `App` Var 2)
      "choose (id @ (∀a. a → a)) auto"
    
  , Example "A8" (ETrm chooseTyp (ETrm idTyp (ETrm auto'Typ EEmpty))) (Var 0 `App` Var 1 `App` Var 2)
      "choose id auto'"
    
  , Example "A8Ann" (ETrm chooseTyp (ETrm idTyp (ETrm auto'Typ EEmpty))) (Var 0 `App` TAbs (Abs (Var 2 `App` (Var 0 `TApp` TVar 0)) `Ann` TArr idTyp (TArr (TVar 0) (TVar 0))) `App` Var 2)
      "choose (Λa. λf. id f @a : (∀b. b → b) → a → a) auto'"
    
  , Example "A8Ann'" (ETrm chooseTyp (ETrm idTyp (ETrm auto'Typ EEmpty))) (Var 0 `App` TAbs (Abs (Abs (Var 3 `App` Var 1 `App` Var 0)) `Ann` TArr idTyp (TArr (TVar 0) (TVar 0))) `App` Var 2)
      "choose (Λa. λf. λx. id f x : (∀b. b → b) → a → a) auto'"
    
  , Example "A8Ann''" (ETrm chooseTyp (ETrm idTyp (ETrm auto'Typ EEmpty))) (Var 0 `App` TAbs (AbsAnn idTyp (Var 2 `App` (Var 0 `TApp` TVar 0)) `Ann` TArr idTyp (TArr (TVar 0) (TVar 0))) `App` Var 2)
      "choose (Λa. λf : ∀b. b → b. id f @a) auto'"
    
  , Example "A9" (ETrm (TForall $ TArr (TArr (TVar 0) (TVar 0)) $ TArr (TList (TVar 0)) (TVar 0)) (ETrm chooseTyp (ETrm idTyp (ETrm (TList idTyp) EEmpty)))) (Var 0 `App` (Var 1 `App` Var 2) `App` Var 3)
      "f (choose id) ids where f : ∀a. (a → a) → [a] → a"
    
  , Example "A10" (ETrm polyTyp (ETrm idTyp EEmpty)) (Var 0 `App` Var 1)
      "poly id"
    
  , Example "A11" (ETrm polyTyp EEmpty) (Var 0 `App` Abs (Var 0))
      "poly (λx. x)"
    
  , Example "A11Ann" (ETrm polyTyp EEmpty) (Var 0 `App` TAbs (Abs (Var 0)))
      "poly (Λa. λx. x : a → a)"
    
  , Example "A12" (ETrm idTyp (ETrm polyTyp EEmpty)) (Var 0 `App` Var 1 `App` Abs (Var 0))
      "id poly (λx. x)"
    
  , Example "A12Ann" (ETrm idTyp (ETrm polyTyp EEmpty)) (Var 0 `App` Var 1 `App` TAbs (Abs (Var 0)))
      "id poly (Λa. λx. x)"
    
  -- B series: Polymorphic contexts
  , Example "B1" EEmpty (Abs (Pair `App` (Var 0 `App` LitInt 1) `App` (Var 0 `App` LitBool True)))
      "λf. (f 1, f True)"
    
  , Example "B1Ann" EEmpty (Abs (Pair `App` (Var 0 `App` LitInt 1) `App` (Var 0 `App` LitBool True)) `Ann` (idTyp `TArr` TProd TInt TBool))
      "(λf. (f 1, f True)) : (∀a. a → a) → Int × Bool"
    
  , Example "B1Ann'" EEmpty (AbsAnn idTyp (Pair `App` (Var 0 `App` LitInt 1) `App` (Var 0 `App` LitBool True)))
      "λf : ∀a. a → a. (f 1, f True)"
    
  , Example "B2" (ETrm polyTyp (ETrm headTyp EEmpty)) (Abs (Var 1 `App` (Var 2 `App` Var 0)))
      "λxs. poly (head xs)"
    
  , Example "B2Ann" (ETrm polyTyp (ETrm headTyp EEmpty)) (Abs (Var 1 `App` (Var 2 `App` Var 0)) `Ann` (TList idTyp `TArr` TProd TInt TBool))
      "(λxs. poly (head xs)) : [∀a. a → a] → Int × Bool"
    
  , Example "B2Ann'" (ETrm polyTyp (ETrm headTyp EEmpty)) (AbsAnn (TList idTyp) (Var 1 `App` (Var 2 `App` Var 0)))
      "λxs : [∀a. a → a]. poly (head xs)"
    
  -- C series: List operations
  , Example "C1" (ETrm lengthTyp (ETrm (TList idTyp) EEmpty)) (Var 0 `App` Var 1)
      "length ids"
    
  , Example "C2" (ETrm tailTyp (ETrm (TList idTyp) EEmpty)) (Var 0 `App` Var 1)
      "tail ids"
    
  , Example "C3" (ETrm headTyp (ETrm (TList idTyp) EEmpty)) (Var 0 `App` Var 1)
      "head ids"
    
  , Example "C4" (ETrm singleTyp (ETrm idTyp EEmpty)) (Var 0 `App` Var 1)
      "single id"
    
  , Example "C5" (ETrm idTyp (ETrm (TList idTyp) EEmpty)) (Cons `App` Var 0 `App` Var 1)
      "cons id ids"
    
  , Example "C6" (ETrm (TList idTyp) EEmpty) (Cons `App` Abs (Var 0) `App` Var 0)
      "cons (λx. x) ids"
    
  , Example "C6Ann" (ETrm (TList idTyp) EEmpty) (Cons `App` idTrm `App` Var 0)
      "cons (Λa. λx. x : a → a) ids"
    
  , Example "C6Ann'" (ETrm (TList idTyp) EEmpty) (Cons `App` TAbs (AbsAnn (TVar 0) (Var 0)) `App` Var 0)
      "cons (Λa. λx : a. x) ids"
    
  , Example "C7" (ETrm appendTyp (ETrm singleTyp (ETrm incTyp (ETrm idTyp EEmpty)))) (Var 0 `App` (Var 1 `App` Var 2) `App` (Var 1 `App` Var 3))
      "append (single inc) (single id)"
    
  , Example "C7Ann" (ETrm appendTyp (ETrm singleTyp (ETrm incTyp (ETrm idTyp EEmpty)))) (Var 0 `App` (Var 1 `App` Var 2) `App` (Var 1 `App` (Var 3 `TApp` TInt)))
      "append (single inc) (single (id @ Int))"
    
  , Example "C8" (ETrm appendTyp (ETrm singleTyp (ETrm idTyp (ETrm (TList idTyp) EEmpty)))) (Var 0 `App` (Var 1 `App` Var 2) `App` Var 3)
      "append (single id) ids"
    
  , Example "C9" (ETrm mapTyp (ETrm polyTyp (ETrm singleTyp (ETrm idTyp EEmpty)))) (Var 0 `App` Var 1 `App` (Var 2 `App` Var 3))
      "map poly (single id)"
    
  , Example "C10" (ETrm mapTyp (ETrm headTyp (ETrm singleTyp (ETrm (TList idTyp) EEmpty)))) (Var 0 `App` Var 1 `App` (Var 2 `App` Var 3))
      "map head (single ids)"
    
  , Example "C10Ann" (ETrm mapTyp (ETrm headTyp (ETrm singleTyp (ETrm (TList idTyp) EEmpty)))) (Var 0 `App` (Var 1 `TApp` idTyp) `App` (Var 2 `App` Var 3))
      "map (head @ (∀a. a → a)) (single ids)"
    
  -- D series: Higher-order functions
  , Example "D1" (ETrm appTyp (ETrm polyTyp (ETrm idTyp EEmpty))) (Var 0 `App` Var 1 `App` Var 2)
      "app poly id"
    
  , Example "D2" (ETrm revappTyp (ETrm idTyp (ETrm polyTyp EEmpty))) (Var 0 `App` Var 1 `App` Var 2)
      "revapp id poly"
    
  , Example "D3" (ETrm runSTTyp (ETrm argSTTyp EEmpty)) (Var 0 `App` Var 1)
      "runST argST"
    
  , Example "D4" (ETrm appTyp (ETrm runSTTyp (ETrm argSTTyp EEmpty))) (Var 0 `App` Var 1 `App` Var 2)
      "app runST argST"
    
  , Example "D4Ann" (ETrm appTyp (ETrm runSTTyp (ETrm argSTTyp EEmpty))) (Var 0 `App` (Abs (Var 2 `App` TAbs (Var 0 `TApp` TVar 0)) `Ann` TArr argSTTyp TInt) `App` Var 2)
      "app (λx. runST (Λa. x @a) : (∀a. ST a Int) → Int) argST"
    
  , Example "D4Ann'" (ETrm appTyp (ETrm runSTTyp (ETrm argSTTyp EEmpty))) (Var 0 `App` AbsAnn argSTTyp (Var 2 `App` TAbs (Var 0 `TApp` TVar 0)) `App` Var 2)
      "app (λx : ∀a. ST a Int. runST (Λa. x @a)) argST"
    
  , Example "D4Ann''" (ETrm appTyp (ETrm runSTTyp (ETrm argSTTyp EEmpty))) (Var 0 `App` (Var 1 `TApp` TInt) `App` Var 2)
      "app (runST @Int) argST"
    
  , Example "D5" (ETrm revappTyp (ETrm argSTTyp (ETrm runSTTyp EEmpty))) (Var 0 `App` Var 1 `App` Var 2)
      "revapp argST runST"
    
  , Example "D5Ann" (ETrm revappTyp (ETrm argSTTyp (ETrm runSTTyp EEmpty))) (Var 0 `App` Var 1 `App` (Var 2 `TApp` TInt))
      "revapp argST (runST @Int)"
    
  , Example "D5Ann'" (ETrm revappTyp (ETrm argSTTyp (ETrm runSTTyp EEmpty))) (Var 0 `App` Var 1 `App` (Abs (Var 3 `App` TAbs (Var 0 `TApp` TVar 0)) `Ann` TArr argSTTyp TInt))
      "revapp argST (λx. runST (Λa. x @a) : (∀a. ST a Int) → Int)"
    
  -- E series: Complex examples
  , Example "E1" (ETrm (TForall $ TArr (TVar 0) $ TArr (TList (TVar 0)) (TVar 0)) (ETrm (TArr TInt idTyp) (ETrm (TList $ TForall $ TArr TInt $ TArr (TVar 0) (TVar 0)) EEmpty))) (Var 0 `App` Var 1 `App` Var 2)
      "k h lst where h : Int → (∀a. a → a), k : ∀a. a → [a] → a, lst : [∀a. Int → a → a]"
    
  , Example "E2" (ETrm (TForall $ TArr (TVar 0) $ TArr (TList (TVar 0)) (TVar 0)) (ETrm (TArr TInt idTyp) (ETrm (TList $ TForall $ TArr TInt $ TArr (TVar 0) (TVar 0)) EEmpty))) (Var 0 `App` Abs (Var 2 `App` Var 0) `App` Var 2)
      "k (λx. h x) lst"
    
  , Example "E2Ann" (ETrm (TForall $ TArr (TVar 0) $ TArr (TList (TVar 0)) (TVar 0)) (ETrm (TArr TInt idTyp) (ETrm (TList $ TForall $ TArr TInt $ TArr (TVar 0) (TVar 0)) EEmpty))) (Var 0 `App` TAbs (Abs ((Var 2 `App` Var 0)) `Ann` TArr TInt (TArr (TVar 0) (TVar 0))) `App` Var 2)
      "k (Λa. λx. h x @ a : Int → a → a) lst"
    
  , Example "E2Ann'" (ETrm (TForall $ TArr (TVar 0) $ TArr (TList (TVar 0)) (TVar 0)) (ETrm (TArr TInt idTyp) (ETrm (TList $ TForall $ TArr TInt $ TArr (TVar 0) (TVar 0)) EEmpty))) (Var 0 `App` TAbs (AbsAnn TInt (Var 2 `App` Var 0 `TApp` TVar 0)) `App` Var 2)
      "k (Λa. λx : Int. h x @ a) lst"
    
  , Example "E3" (ETrm (TArr (TForall (TArr (TVar 0) idTyp)) TInt) EEmpty) (Var 0 `App` Abs (Abs (Var 0)))
      "r (λx. λy. y) where r : (∀a. a → ∀b. b → b) → Int"
    
  , Example "E3Ann" (ETrm (TArr (TForall (TArr (TVar 0) idTyp)) TInt) EEmpty) (Var 0 `App` TAbs (Abs (TAbs (Abs (Var 0))) `Ann` TArr (TVar 0) idTyp))
      "r (Λ a. (λx. Λ b. λy. y) : a → ∀b. b → b)"
    
  , Example "E3Ann'" (ETrm (TArr (TForall (TArr (TVar 0) idTyp)) TInt) EEmpty) (Var 0 `App` TAbs (AbsAnn (TVar 0) (TAbs (AbsAnn (TVar 0) (Var 0)))))
      "r (Λa. λx : a. Λb. λy : b. y)"
    
  -- F series: FreezeML paper additions
  , Example "F5" (ETrm autoTyp (ETrm idTyp EEmpty)) (Var 0 `App` Var 1)
      "auto id"
    
  , Example "F6" (ETrm headTyp (ETrm (TList idTyp) EEmpty)) (Cons `App` (Var 0 `App` Var 1) `App` Var 1)
      "cons (head ids) ids"
    
  , Example "F7" (ETrm headTyp (ETrm (TList idTyp) EEmpty)) (Var 0 `App` Var 1 `App` LitInt 3)
      "head ids 3"
    
  , Example "F8" (ETrm chooseTyp (ETrm headTyp (ETrm (TList idTyp) EEmpty))) (Var 0 `App` (Var 1 `App` Var 2))
      "choose (head ids)"
    
  -- Spine-local type inference
  , Example "Pair" EEmpty ((Pair `App` Abs (Var 0) `App` LitInt 1) `Ann` ((TInt `TArr` TInt) `TProd` TInt))
      "(Pair (λx. x) 1) : (Int → Int) × Int"
    
  , Example "PairAnn" EEmpty ((Pair `App` (Abs (Var 0) `Ann` TArr TInt TInt) `App` LitInt 1) `Ann` ((TInt `TArr` TInt) `TProd` TInt))
      "(Pair (λx. x : Int → Int) 1) : (Int → Int) × Int"
  ]
