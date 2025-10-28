module Examples where

data Example = Example
  { exampleName :: String
  , exampleString :: String
  }
  deriving (Eq, Show)

preEnvStrings :: [(String, String)]
preEnvStrings =
  -- Curried versions
  [ ("id", "forall a. a -> a")
  , ("choose", "forall a. a -> a -> a")
  , ("ids", "[forall a. a -> a]")
  , ("auto", "(forall a. a -> a) -> (forall a. a -> a)")
  , ("auto'", "forall a. (forall b. b -> b) -> a -> a")
  , ("poly", "(forall a. a -> a) -> int * bool")
  , ("head", "forall a. [a] -> a")
  , ("tail", "forall a. [a] -> [a]")
  , ("length", "forall a. [a] -> int")
  , ("single", "forall a. a -> [a]")
  , ("inc", "int -> int")
  , ("append", "forall a. [a] -> [a] -> [a]")
  , ("map", "forall a. forall b. (a -> b) -> [a] -> [b]")
  , ("app", "forall a. forall b. (a -> b) -> a -> b")
  , ("revapp", "forall a. forall b. a -> (a -> b) -> b")
  , ("runST", "forall a. (forall b. ST b a) -> a")
  , ("argST", "forall a. ST a int")
  , ("f", "forall a. (a -> a) -> [a] -> a")
  , ("h", "int -> (forall a. a -> a)")
  , ("k", "forall a. a -> [a] -> a")
  , ("lst", "[forall a. int -> a -> a]")
  , ("r", "(forall a. a -> (forall b. b -> b)) -> int")
  , ("nil", "forall a. [a]")
  , ("cons", "forall a. a -> [a] -> [a]")
  , ("fst", "forall a. forall b. a * b -> a")
  , ("snd", "forall a. forall b. a * b -> b")
  , ("st", "forall a. forall b. a -> b -> ST a b")
  , ("f1", "int * int")
  , ("f2", "(forall a. a -> a) * int")
  -- Uncurried versions
  , ("id_uc", "forall a. {a} -> a")
  , ("choose_uc", "forall a. {a, a} -> a")
  , ("ids_uc", "[forall a. {a} -> a]")
  , ("auto_uc", "{forall a. {a} -> a} -> (forall a. {a} -> a)")
  , ("auto'_uc", "forall a. {forall b. {b} -> b} -> {a} -> a")
  , ("poly_uc", "{forall a. {a} -> a} -> int * bool")
  , ("head_uc", "forall a. {[a]} -> a")
  , ("tail_uc", "forall a. {[a]} -> [a]")
  , ("length_uc", "forall a. {[a]} -> int")
  , ("single_uc", "forall a. {a} -> [a]")
  , ("inc_uc", "{int} -> int")
  , ("append_uc", "forall a. {[a], [a]} -> [a]")
  , ("map_uc", "forall a. forall b. {{a} -> b, [a]} -> [b]")
  , ("app_uc", "forall a. forall b. {{a} -> b, a} -> b")
  , ("revapp_uc", "forall a. forall b. {a, {a} -> b} -> b")
  , ("runST_uc", "forall a. {forall b. ST b a} -> a")
  , ("argST_uc", "forall a. ST a int")
  , ("f_uc", "forall a. {{a} -> a, [a]} -> a")
  , ("h_uc", "{int} -> (forall a. {a} -> a)")
  , ("k_uc", "forall a. {a} -> {[a]} -> a")
  , ("lst_uc", "[forall a. {int} -> {a} -> a]")
  , ("r_uc", "{forall a. {a} -> (forall b. {b} -> b)} -> int")
  , ("cons_uc", "forall a. {a, [a]} -> [a]")
  , ("fst_uc", "forall a. forall b. {a * b} -> a")
  , ("snd_uc", "forall a. forall b. {a * b} -> b")
  , ("st_uc", "forall a. forall b. {a, b} -> ST a b")
  ] 

examplesList :: [Example]
examplesList =
  [ Example "A1" "lambda x. lambda y. y"
  , Example "A1 (Fc translation 1)" "Lambda a. Lambda b. (lambda x. lambda y. y) : a -> b -> b"
  , Example "A1 (Fc translation 1, uncurried)" "Lambda a. Lambda b. ((lambda {x, y}. y) : ({a, b} -> b))"
  , Example "A1 (Fc translation 2)" "Lambda a. Lambda b. lambda x : a. lambda y : b. y"
  , Example "A1 (Fc translation 2, uncurried)" "Lambda a. Lambda b. lambda {x : a, y : b}. y"
  , Example "A1 (uncurried)" "lambda {x, y}. y"
  , Example "A2" "choose id"
  , Example "A2 (uncurried)" "choose_uc {id_uc}"
  , Example "A3" "choose nil ids"
  , Example "A3 (Fc translation)" "choose (nil : [forall a. a -> a]) ids"
  , Example "A3 (uncurried)" "choose_uc {nil, ids_uc}"
  , Example "A3 (Fc translation, uncurried)" "choose_uc {(nil : [forall a. {a} -> a]), ids_uc}"
  , Example "A4" "lambda x. x x"
  , Example "A4 (Fc translation 1)" "(lambda x. x x) : (forall a. a -> a) -> (forall a. a -> a)"
  , Example "A4 (Fc translation 2)" "lambda x : (forall a. a -> a). x x"
  , Example "A4 (uncurried)" "lambda {x}. x {x}"
  , Example "A4 (Fc translation 1, uncurried)" "(lambda {x}. x {x}) : {forall a. {a} -> a} -> (forall a. {a} -> a)"
  , Example "A4 (Fc translation 2, uncurried)" "lambda {x : forall a. {a} -> a}. x {x}"
  , Example "A5" "id auto"
  , Example "A5 (uncurried)" "id_uc {auto_uc}"
  , Example "A6" "id auto'"
  , Example "A6 (uncurried)" "id_uc {auto'_uc}"
  , Example "A7" "choose id auto"
  , Example "A7 (Fc translation)" "choose (id @ (forall a. a -> a)) auto"
  , Example "A7 (uncurried)" "choose_uc {id_uc, auto_uc}"
  , Example "A7 (Fc translation, uncurried)" "choose_uc {(id_uc @ (forall a. {a} -> a)), auto_uc}"
  , Example "A8" "choose id auto'"
  , Example "A8 (Fc translation 1)" "choose (Lambda a. lambda f. id f @ a : (forall b. b -> b) -> a -> a) auto'"
  , Example "A8 (Fc translation 2)" "choose (Lambda a. lambda f. lambda x. id f x : (forall b. b -> b) -> a -> a) auto'"
  , Example "A8 (Fc translation 3)" "choose (Lambda a. lambda f : forall b. b -> b. id f @ a) auto'"
  , Example "A8 (uncurried)" "choose_uc {id_uc, auto'_uc}"
  , Example "A8 (Fc translation 1, uncurried)" "choose_uc {Lambda a. ((lambda {f}. id_uc {f @ a}) : {forall b. {b} -> b} -> {a} -> a), auto'_uc}"
  , Example "A8 (Fc translation 2, uncurried)" "choose_uc {Lambda a. ((lambda {f}. lambda {x}. id_uc {f} {x}) : {forall b. {b} -> b} -> {a} -> a), auto'_uc}"
  , Example "A8 (Fc translation 3, uncurried)" "choose_uc {(Lambda a. lambda {f : forall b. {b} -> b}. id_uc {(f @ a)}), auto'_uc}"
  , Example "A9" "f (choose id) ids"
  , Example "A10" "poly id"
  , Example "A10 (uncurried)" "poly_uc {id_uc}"
  , Example "A11" "poly (lambda x. x)"
  , Example "A11 (Fc translation)" "poly (Lambda a. lambda x. x)"
  , Example "A11 (uncurried)" "poly_uc {lambda {x}. x}"
  , Example "A11 (Fc translation, uncurried)" "poly_uc {Lambda a. lambda {x}. x}"
  , Example "A12" "id poly (lambda x. x)"
  , Example "A12 (Fc translation)" "id poly (Lambda a. lambda x. x)"
  , Example "A12 (uncurried)" "id_uc {poly_uc} {lambda {x}. x}"
  , Example "A12 (Fc translation, uncurried)" "id_uc {poly_uc} {Lambda a. lambda {x}. x}"
  , Example "B1" "lambda f. <f 1, f true>"
  , Example "B1 (Fc translation 1)" "(lambda f. <f 1, f true>) : (forall a. a -> a) -> int * bool"
  , Example "B1 (Fc translation 2)" "lambda f : forall a. a -> a. <f 1, f true>"
  , Example "B1 (uncurried)" "lambda {f}. <f 1, f true>"
  , Example "B1 (Fc translation 1, uncurried)" "(lambda {f}. <f 1, f true>) : {forall a. {a} -> a} -> int * bool"
  , Example "B1 (Fc translation 2, uncurried)" "lambda {f : forall a. {a} -> a}. <f 1, f true>"
  , Example "B2" "lambda xs. poly (head xs)"
  , Example "B2 (Fc translation 1)" "(lambda xs. poly (head xs)) : [forall a. a -> a] -> int * bool"
  , Example "B2 (Fc translation 2)" "lambda xs : [forall a. a -> a]. poly (head xs)"
  , Example "B2 (uncurried)" "lambda {xs}. poly_uc {head_uc {xs}}"
  , Example "B2 (Fc translation 1, uncurried)" "(lambda {xs}. poly_uc {head_uc {xs}}) : {[forall a. {a} -> a]} -> int * bool"
  , Example "B2 (Fc translation 2, uncurried)" "lambda {xs : [forall a. {a} -> a]}. poly_uc {head_uc {xs}}"
  , Example "C1" "length ids"
  , Example "C1 (uncurried)" "length_uc {ids_uc}"
  , Example "C2" "tail ids"
  , Example "C2 (uncurried)" "tail_uc {ids_uc}"
  , Example "C3" "head ids"
  , Example "C3 (uncurried)" "head_uc {ids_uc}"
  , Example "C4" "single id"
  , Example "C4 (uncurried)" "single_uc {id_uc}"
  , Example "C5" "cons id ids"
  , Example "C5 (uncurried)" "cons_uc {id_uc, ids_uc}"
  , Example "C6" "cons (lambda x. x) ids"
  , Example "C6 (Fc translation 1)" "cons (Lambda a. lambda x. x : a -> a) ids"
  , Example "C6 (Fc translation 2)" "cons (Lambda a. lambda x : a. x) ids"
  , Example "C6 (uncurried)" "cons_uc {lambda {x}. x, ids_uc}"
  , Example "C6 (Fc translation 1, uncurried)" "cons_uc {(Lambda a. lambda {x}. x : {a} -> a), ids_uc}"
  , Example "C6 (Fc translation 2, uncurried)" "cons_uc {(Lambda a. lambda {x : a}. x), ids_uc}"
  , Example "C7" "append (single inc) (single id)"
  , Example "C7 (Fc translation)" "append (single inc) (single (id @ int))"
  , Example "C7 (uncurried)" "append_uc {single_uc {inc_uc}, single_uc {id_uc}}"
  , Example "C7 (Fc translation, uncurried)" "append_uc {single_uc {inc_uc}, single_uc {id_uc @ int}}"
  , Example "C8" "append (single id) ids"
  , Example "C8 (uncurried)" "append_uc {single_uc {id_uc}, ids_uc}"
  , Example "C9" "map poly (single id)"
  , Example "C9 (uncurried)" "map_uc {poly_uc, single_uc {id_uc}}"
  , Example "C10" "map head (single ids)"
  , Example "C10 (Fc translation)" "map (head @ (forall a. a -> a)) (single ids)"
  , Example "C10 (uncurried)" "map_uc {head_uc, single_uc {ids_uc}}"
  , Example "C10 (Fc translation, uncurried)" "map_uc {(head_uc @ (forall a. {a} -> a)), single_uc {ids_uc}}"
  , Example "D1" "app poly id"
  , Example "D1 (uncurried)" "app_uc {poly_uc, id_uc}"
  , Example "D2" "revapp id poly"
  , Example "D2 (uncurried)" "revapp_uc {id_uc, poly_uc}"
  , Example "D3" "runST argST"
  , Example "D3 (uncurried)" "runST_uc {argST_uc}"
  , Example "D4" "app runST argST"
  , Example "D4 (Fc translation 1)" "app (lambda x. runST (Lambda a. x @ a) : (forall a. ST a int) -> int) argST"
  , Example "D4 (Fc translation 2)" "app (lambda x : forall a. ST a int. runST (Lambda a. x @ a)) argST"
  , Example "D4 (Fc translation 3)" "app (runST @ int) argST"
  , Example "D4 (uncurried)" "app_uc {runST_uc, argST_uc}"
  , Example "D4 (Fc translation 1, uncurried)" "app_uc {(lambda {x}. runST_uc {Lambda a. x @ a} : {forall a. ST a int} -> int), argST_uc}"
  , Example "D4 (Fc translation 2, uncurried)" "app_uc {(lambda {x : forall a. ST a int}. runST_uc {Lambda a. x @ a}), argST_uc}"
  , Example "D4 (Fc translation 3, uncurried)" "app_uc {runST_uc @ int, argST_uc}"
  , Example "D5" "revapp argST runST"
  , Example "D5 (Fc translation 1)" "revapp argST (runST @ int)"
  , Example "D5 (Fc translation 2)" "revapp argST (lambda x. runST (Lambda a. x @ a) : (forall a. ST a int) -> int)"
  , Example "D5 (uncurried)" "revapp_uc {argST_uc, runST_uc}"
  , Example "D5 (Fc translation 1, uncurried)" "revapp_uc {argST_uc, (runST_uc @ int)}"
  , Example "D5 (Fc translation 2, uncurried)" "revapp_uc {argST_uc, (lambda {x}. runST_uc {Lambda a. x @ a}) : {forall a. ST a int} -> int}"
  , Example "E1" "k h lst"
  , Example "E1 (uncurried)" "k_uc {h_uc} {lst_uc}"
  , Example "E2" "k (lambda x. h x) lst"
  , Example "E2 (Fc translation 1)" "k (Lambda a. ((lambda x. h x @ a) : (int -> a -> a))) lst"
  , Example "E2 (Fc translation 2)" "k (Lambda a. lambda x : int. h x @ a) lst"
  , Example "E2 (uncurried)" "k_uc {lambda {x}. h_uc {x}} {lst_uc}"
  , Example "E2 (Fc translation 1, uncurried)" "k_uc {(Lambda a. ((lambda {x}. h_uc {x} @ a) : {int} -> {a} -> a))} {lst_uc}"
  , Example "E2 (Fc translation 2, uncurried)" "k_uc {(Lambda a. lambda {x : int}. h_uc {x} @ a)} {lst_uc}"
  , Example "E3" "r (lambda x. lambda y. y)"
  , Example "E3 (Fc translation 1)" "r (Lambda a. (lambda x. Lambda b. lambda y. y) : a -> forall b. b -> b)"
  , Example "E3 (Fc translation 2)" "r (Lambda a. lambda x : a. Lambda b. lambda y : b. y)"
  , Example "E3 (uncurried)" "r_uc {lambda {x}. lambda {y}. y}"
  , Example "E3 (Fc translation 1, uncurried)" "r_uc {(Lambda a. (lambda {x}. Lambda b. lambda {y}. y) : {a} -> forall b. {b} -> b)}"
  , Example "E3 (Fc translation 2, uncurried)" "r_uc {(Lambda a. lambda {x : a}. Lambda b. lambda {y : b}. y)}"
  , Example "F5" "auto id"
  , Example "F5 (uncurried)" "auto_uc {id_uc}"
  , Example "F6" "cons (head ids) ids"
  , Example "F6 (uncurried)" "cons_uc {head_uc {ids_uc}, ids_uc}"
  , Example "F7" "head ids 3"
  , Example "F7 (uncurried)" "head_uc {ids_uc} {3}"
  , Example "F8" "choose (head ids)"
  , Example "Pair" "<lambda x. x, 1> : (int -> int) * int"
  , Example "Const" "(Lambda a. Lambda b. lambda x : a. lambda y : b. x) 1 true"
  , Example "Const (uncurried)" "(Lambda a. Lambda b. lambda {x : a}. lambda {y : b}. x) {1} {true}"
  , Example "Pair0" "(fst <lambda x. x, 2>) : int -> int"
  , Example "Pair1" "fst f1"
  , Example "Pair2" "(fst f2) 1"
  , Example "Pair3" "(fst <id, 1>) 1"
  ]  