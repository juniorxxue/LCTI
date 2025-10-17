# Implementation

This directory contains a Haskell implementation of local contextual type inference. All the algorithmic rules are implemented. In addition, we have also added several types, including lists, product types, and the ST Monad. All the examples provided in the paper run in this implementation.

### Building from Source

* **Prerequisites**: [GHC](https://www.haskell.org/downloads/) and [Cabal](https://www.haskell.org/cabal/)
* **Build**: From this directory, run:
  ```bash
  cabal build
  ```

### Usage

* **Run all examples**

  To test all the examples presented in the paper in one go:
  ```bash
  cabal run Poly
  ```

  Expected Output: The output will show the type-checking results of all examples. `[✓]` denotes success; `[x]` denotes failure. For example:

  ```bash
  --------------------------------------------------------------------------------
  A1: λx. λy. y
  [x] Typing failed
  --------------------------------------------------------------------------------
  A1 (Fc translation 1): Λa. Λb. (λx. λy. y) : a → b → b
  [✓] Typing result: ∀. ∀. t1 → t0 → t0
  --------------------------------------------------------------------------------
  A1 (Fc translation 2): Λa. Λb. λx : a. λy : b. y
  [✓] Typing result: ∀. ∀. t1 → t0 → t0
  --------------------------------------------------------------------------------
  A2: choose id
  [✓] Typing result: (∀. t0 → t0) → ∀. t0 → t0
  --------------------------------------------------------------------------------
  A3: choose Nil ids
  [x] Typing failed
  ...
  ```

* **Run specific examples**

  ```bash
  cabal run Poly -- A1              # Run single example
  cabal run Poly -- A1 A2 A3        # Run multiple examples
  ```

* **Show detailed derivations**

  Add the `--drv` argument to print the full derivation tree:

  ```bash
  cabal run Poly -- --drv A2        # Show derivation for A2
  ```

  Expected Output: Shows the complete derivation tree.

  ```bash
  Running examples: A2
  --------------------------------------------------------------------------------
  A2: choose id
  [✓] Typing result: (∀. t0 → t0) → ∀. t0 → t0

  [Ty-App] ∅, :∀. t0 → t0 → t0, :∀. t0 → t0 ⊢ □ ⇒ e1 e0 ⇒ (∀. t0 → t0) → ∀. t0 → t0
    [Ty-Sub] ∅, :∀. t0 → t0 → t0, :∀. t0 → t0 ⊢ [e0] ↝ □ ⇒ e1 ⇒ (∀. t0 → t0) → (∀. t0 → t0) → ∀. t0 → t0
      [Ty-Var] ∅, :∀. t0 → t0 → t0, :∀. t0 → t0 ⊢ □ ⇒ e1 ⇒ ∀. t0 → t0 → t0
        [Lookup] ∀. t0 → t0 → t0 in Γ
      [S-Forall-L] ∅, :∀. t0 → t0 → t0, :∀. t0 → t0; ∅ ⊢ ∀. t0 → t0 → t0 <: [e0] ↝ □ ⊣ ∅ ⇝ (∀. t0 → t0) → (∀. t0 → t0) → ∀. t0 → t0
        [S-Term-Open] ∅, :∀. t0 → t0 → t0, :∀. t0 → t0; ∅, ^ ⊢ t0 → t0 → t0 <: [e0] ↝ □ ⊣ ∅, =∀. t0 → t0 ⇝ (∀. t0 → t0) → (∀. t0 → t0) → ∀. t0 → t0
          [Ty-Var] ∅, :∀. t0 → t0 → t0, :∀. t0 → t0, ^ ⊢ □ ⇒ e0 ⇒ ∀. t0 → t0
            [Lookup] ∀. t0 → t0 in Γ
          [S-Ex-R] ∅, :∀. t0 → t0 → t0, :∀. t0 → t0; ∅, ^ ⊢ t0 <: ∀. t0 → t0 ⊣ ∅, =∀. t0 → t0
          [S-Empty] ∅, :∀. t0 → t0 → t0, :∀. t0 → t0; ∅, =∀. t0 → t0 ⊢ t0 → t0 <: □ ⊣ ∅, =∀. t0 → t0 ⇝ (∀. t0 → t0) → ∀. t0 → t0
  ```

### Examples

The table below summarizes every example used in the paper.

| ID     | Example Program                        | Translation                                          | Fc  | Fc (Uncurried) | Translation (Uncurried)                                       |
| ------ | -------------------------------------- | ---------------------------------------------------- | --- | -------------- | ------------------------------------------------------------- |
| A1     | `\x. \y. y`                            | `/\a. /\b. \x : a. \y : b. y`                        | Ann | Ann            | `/\a. /\b. \(x, y). y : (a, b) → b`                           |
| A2     | `choose id`                            | `choose id`                                          | ✅  | -              | -                                                             |
| A3     | `choose Nil ids`                       | `choose (Nil : [forall a. a -> a]) ids`              | Ann | Ann            | `choose(Nil : [forall a. (a) -> a], ids)`                     |
| A4     | `\x. x x`                              | `\x : (forall a. a -> a). x x`                       | Ann | Ann            | `(λ(x). x(x)) : (∀a. (a) → a) → (∀a. (a) → a)`                |
| A5     | `id auto`                              | `id auto`                                            | ✅  | ✅             | `id(auto)`                                                    |
| A6     | `id auto'`                             | `id auto'`                                           | ✅  | ✅             | `id(auto')`                                                   |
| A7     | `choose id auto`                       | `choose (id @ (forall a. a -> a)) auto`              | Ann | Ann            | `choose(id @ (∀a. (a) → a), auto)`                            |
| A8     | `choose id auto'`                      | `choose (/\a. \f : forall b. b -> b. id f @a) auto'` | ✅  | ✅             | `choose(Λa. λ(f). id(f @a) : (∀b. (b) → b) → (a) → a, auto')` |
| A9     | `f (choose id) ids`                    | `f (choose id) ids`                                  | ✅  | -              | -                                                             |
| A10    | `poly id`                              | `poly id`                                            | ✅  | ✅             | `poly(id)`                                                    |
| A11    | `poly (\x. x)`                         | `poly (/\a. \x. x)`                                  | Ann | Ann            | `poly(Λa. λ(x). x)`                                           |
| A12    | `id poly (\x. x)`                      | `id poly (/\a. \x. x)`                               | Ann | Ann            | `id(poly)(Λa. λ(x). x)`                                       |
| B1     | `\f. (f 1, f True)`                    | `\f : (forall a. a -> a). (f 1, f True)`             | Ann | Ann            | `λ(f : ∀a. (a) → a). (f(1), f(True))`                         |
| B2     | `\xs. poly (head xs)`                  | `\xs : [forall a. a -> a]. poly (head xs)`           | Ann | Ann            | `λ(xs : [∀a. (a) → a]). poly(head(xs))`                       |
| C1     | `length ids`                           | `length ids`                                         | ✅  | ✅             | `length(ids)`                                                 |
| C2     | `tail ids`                             | `tail ids`                                           | ✅  | ✅             | `tail(ids)`                                                   |
| C3     | `head ids`                             | `head ids`                                           | ✅  | ✅             | `head(ids)`                                                   |
| C4     | `single id`                            | `single id`                                          | ✅  | ✅             | `single(id)`                                                  |
| C5     | `cons id ids`                          | `cons id ids`                                        | ✅  | ✅             | `cons(id, ids)`                                               |
| C6     | `cons (\x. x) ids`                     | `cons (/\a. \x : a. x) ids`                          | Ann | Ann            | `cons(Λa. λ(x). x : (a) → a, ids)`                            |
| C7     | `append (single inc) (single id)`      | `append (single inc) (single (id @ Int))`            | Ann | Ann            | `append(single(inc), single(id @ Int))`                       |
| C8     | `append (single id) ids`               | `append (single id) ids`                             | ✅  | ✅             | `append(single(id), ids)`                                     |
| C9     | `map poly (single id)`                 | `map poly (single id)`                               | ✅  | ✅             | `map(poly, single(id))`                                       |
| C10    | `map head (single ids)`                | `map (head @ (forall a. a -> a)) (single ids)`       | Ann | Ann            | `map(head @ (∀a. (a) → a), single(ids))`                      |
| D1     | `app poly id`                          | `app poly id`                                        | ✅  | ✅             | `app(poly, id)`                                               |
| D2     | `revapp id poly`                       | `revapp id poly`                                     | ✅  | ✅             | `revapp(id, poly)`                                            |
| D3     | `runST argST`                          | `runST argST`                                        | ✅  | ✅             | `runST(argST)`                                                |
| D4     | `app runST argST`                      | `app (runST @ Int) argST`                            | Ann | Ann            | `app(runST @Int, argST)`                                      |
| D5     | `revapp argST runST`                   | `revapp argST (runST @ Int)`                         | Ann | Ann            | `revapp(argST, runST @Int)`                                   |
| E1, E2 | `k h lst`/`k (\x. h x) lst`            | `k (/\a. \x : Int. h x @ a) lst`                     | Ann | Ann            | `k(Λa. λx : Int. h(x) @ a)(lst)`                              |
| E3     | `r (\x. \y. y)`                        | `r (/\ a. \x : a. /\ b. \y : b. y)`                  | Ann | Ann            | `r(Λa. λ(x : a). Λb. λ(y : b). y)`                            |
| F5     | `auto id`                              | `auto id`                                            | ✅  | ✅             | `auto(id)`                                                    |
| F6     | `cons (head ids) ids`                  | `cons (head ids) ids`                                | ✅  | ✅             | `cons(head(ids), ids)`                                        |
| F7     | `head ids 3`                           | `head ids 3`                                         | ✅  | ✅             | `head(ids)(3)`                                                |
| F8     | `choose (head ids)`                    | `choose (head ids)`                                  | ✅  | -              | -                                                             |
| G1     | `(pair (\x. x) 1) : (Int -> Int, Int)` | `(pair (\x : Int. x) 1) : (Int -> Int, Int)`         | Ann | Ann            | `(pair(λ(x). x : (Int) → Int), 1) : ((Int) → Int) × Int`      |
| Const  | `(Λa. Λb. λx : a. λy : b. x) 1 True`   | `(Λa. Λb. λx : a. λy : b. x) 1 True`                 | ✅  | ✅             | `(Λa. Λb. λ(x : a). λ(y : b). x)(1)(True)`                    |

**Legend:**
- ✅: successfully typed
- ❌: typing failed
- **Ann**: requires additional type annotations
- **-**: (for uncurried version only) not applicable due to partial application

**Type Definitions:**
- `cons: forall a. a -> [a] -> [a]`
- `nil: forall a. [a]`
- `pair: forall a b. a -> b -> a × b`
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

**Type Definitions (uncurried):**
- `cons: forall a. (a, [a]) -> [a]`
- `pair: forall a b. (a, b) -> a × b`
- `id : forall a. (a) -> a`
- `choose : forall a. (a, a) -> a`
- `auto : (forall a. (a) -> a) -> (forall a. (a) -> a)`
- `auto' : forall a. (forall b. (b) -> b) -> (a) -> a`
- `poly : (forall a. (a) -> a) -> Int × Bool`
- `head : forall a. ([a]) -> a`
- `tail : forall a. ([a]) -> [a]`
- `length : forall a. ([a]) -> Int`
- `single : forall a. (a) -> [a]`
- `append : forall a. ([a], [a]) -> [a]`
- `inc : (Int) -> Int`
- `map : forall a b. (a -> b, [a]) -> [b]`
- `app : forall a b. (a -> b, a) -> b`
- `revapp : forall a b. (a, a -> b) -> b`
- `runST : forall a. (forall b. ST b a) -> a`
- `ids : [forall a. (a) -> a]`
- `f : forall a. ((a) -> a) -> ([a]) -> a`
- `h : (Int) -> (forall a. (a) -> a)`
- `k : forall a. (a) -> ([a]) -> a`
- `lst : [forall a. (Int) -> (a) -> a]`
- `r : (forall a. (a) -> forall b. (b) -> b) -> Int`

### Adding Custom Examples

To add and test your own examples, simply append new entries to the `examplesList` in `app/Examples.hs`. Each example should be defined as an `Example` record, specifying the following fields:

- **`exampleName`**: A unique identifier for the example (e.g., "MyExample")
- **`exampleEnv`**: The typing environment using De Bruijn indices
- **`exampleTerm`**: The term to be type-checked using De Bruijn indices
- **`exampleDescription`**: A description of what the example demonstrates

**Example structure:**
```haskell
    Example
      "MyExample"
      (ETrm TInt EEmpty)
      (Abs (Var 0) `App` Var 0)
      "y : Int |- (λx. x) y"
```

**Running custom examples:**
```bash
cabal run Poly -- MyExample              # Run single custom example
cabal run Poly -- MyExample OtherExample # Run multiple custom examples
cabal run Poly -- --drv MyExample        # Show detailed derivation
```

**Note:** You'll need to rebuild the project after adding examples:
```bash
cabal build
```
