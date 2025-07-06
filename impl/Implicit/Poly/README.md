Beyond the formalization, we extend our system with lists, pairs and ST Monad.

TODO:
- Replace the Label of the rules (for infer*s*) once the paper is updated

| ID     | Example Program                        | Translation                                                        | Fc  |
| ------ | -------------------------------------- | ------------------------------------------------------------------ | --- |
| A1     | `\x. \y. y`                            | `/\a. /\b. (\x. \y. y) : a -> b -> b`                              | Ann |
| A2     | `choose id`                            | `choose id`                                                        | ✅  |
| A3     | `choose Nil ids`                       | `choose (Nil : [forall a. a -> a]) ids`                            | Ann |
| A4     | `\x. x x`                              | `(\x. x x) : (forall a. a -> a) -> (forall a. a -> a)`             | Ann |
| A5     | `id auto`                              | `id auto`                                                          | ✅  |
| A6     | `id auto'`                             | `id auto'`                                                         | ✅  |
| A7     | `choose id auto`                       | `choose (id @ (forall a. a -> a)) auto`                            | Ann |
| A8     | `choose id auto'`                      | `choose (/\a. (\f. id f @a) : (forall b. b -> b) -> a -> a) auto'` | ✅  |
| A9     | `f (choose id) ids`                    | `f (choose id) ids`                                                | ✅  |
| A10    | `poly id`                              | `poly id`                                                          | ✅  |
| A11    | `poly (\x. x)`                         | `poly (/\a. \x. x)`                                                | Ann |
| A12    | `id poly (\x. x)`                      | `id poly (/\a. \x. x)`                                             | Ann |
| B1     | `\f. (f 1, f True)`                    | `(\f. (f 1, f True)) : (forall a. a -> a) -> Int × Bool`           | Ann |
| B2     | `\xs. poly (head xs)`                  | `(\xs. poly (head xs)) : [forall a. a -> a] -> Int × Bool`         | Ann |
| C1     | `length ids`                           | `length ids`                                                       | ✅  |
| C2     | `tail ids`                             | `tail ids`                                                         | ✅  |
| C3     | `head ids`                             | `head ids`                                                         | ✅  |
| C4     | `single id`                            | `single id`                                                        | ✅  |
| C5     | `cons id ids`                          | `cons id ids`                                                      | ✅  |
| C6     | `cons (\x. x) ids`                     | `cons (/\a. \x. x : a -> a) ids`                                   | Ann |
| C7     | `append (single inc) (single id)`      | `append (single inc) (single (id @ Int))`                          | Ann |
| C8     | `append (single id) ids`               | `append (single id) ids`                                           | ✅  |
| C9     | `map poly (single id)`                 | `map poly (single id)`                                             | ✅  |
| C10    | `map head (single ids)`                | `map (head @ (forall a. a -> a)) (single ids)`                     | Ann |
| D1     | `app poly id`                          | `app poly id`                                                      | ✅  |
| D2     | `revapp id poly`                       | `revapp id poly`                                                   | ✅  |
| D3     | `runST argST`                          | `runST argST`                                                      | ✅  |
| D4     | `app runST argST`                      | `app (\x. runST (/\a. x @a) : (forall a. ST a Int) -> Int) argST`  | Ann |
| D5     | `revapp argST runST`                   | `revapp argST (runST @ Int)`                                       | Ann |
| E1, E2 | `k h lst`/`k (\x. h x) lst`            | `k (/\a. \x. h x : Int -> a -> a) lst`                             | Ann |
| E3     | `r (\x. \y. y)`                        | `r (/\ a. (\x. /\ b. \y. y) : a -> forall b. b -> b)`              | Ann |
| F5     | `auto id`                              | `auto id`                                                          | ✅  |
| F6     | `cons (head ids) ids`                  | `cons (head ids) ids`                                              | ✅  |
| F7     | `head ids 3`                           | `head ids 3`                                                       | ✅  |
| F8     | `choose (head ids)`                    | `choose (head ids)`                                                | ✅  |
| G1     | `(pair (\x. x) 1) : (Int -> Int, Int)` | variant1 : `(pair ((\x. x) : Int -> Int) 1) : (Int -> Int, Int)`   | Ann |
|        |                                        | variant2 : `(pair (\x. x) 1) : (Int -> Int, Int)`                  | ✅  |

**Legend:**
- ✅ Can be typed
- ❌ Cannot be typed
- **Ann** indicates examples that require more explicit type annotations to type

**Type Definitions:**
- `id : forall a. a -> a`
- `choose : forall a. a -> a -> a`
- `auto : (forall a. a -> a) -> (forall a. a -> a)`
- `auto' : forall a. (forall b. b -> b) -> a -> a`
- `poly : (forall a. a -> a) -> Int × Bool`
- `head : forall a. [a] -> a`
- `tail : forall a. [a] -> [a]`
- `length : forall a. [a] -> Int`
- `single : forall a. a -> [a]`
- `append : forall a. [a] -> [a] -> [a]`
- `inc : Int -> Int`
- `map : forall a b. (a -> b) -> [a] -> [b]`
- `app : forall a b. (a -> b) -> a -> b`
- `revapp : forall a b. a -> (a -> b) -> b`
- `runST : forall a. (forall b. ST b a) -> a`
- `argST : forall a. ST a Int`
- `ids : [forall a. a -> a]`
- `f : forall a. (a -> a) -> [a] -> a`
- `h : Int -> (forall a. a -> a)`
- `k : forall a. a -> [a] -> a`
- `lst : [forall a. Int -> a -> a]`
- `r : (forall a. a -> forall b. b -> b) -> Int`
 