# Implementation

This directory contains a Haskell implementation of local contextual type inference. All the algorithmic rules are implmented. In addition, we have also added several types, including lists, product types and ST Monad. All the examples provided in the paper run in this implementation.

### Building from Source

* **Prerequisites**: [GHC](https://www.haskell.org/downloads/) and [Cabal](https://www.haskell.org/cabal/)
* **Build**: From this directory, run:
  ```bash
  cabal build
  ```
`
### Usage

* **Run all examples**

  To test all the examples presented in the paper in one go:
  ```bash
  cabal run Poly
  ```

  Expected Output: The output will show the type-checking results of all examples. `[✓]` denotes success; `[x]` denotes a type error. For example:

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

  Add `--drv` argument to print the full derivation tree:

  ```bash
  cabal run Poly -- --drv A2        # Show derivation for A2
  ```

  Expected Output: Shows the complete derivation tree with subtyping and typing rules applied.

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
