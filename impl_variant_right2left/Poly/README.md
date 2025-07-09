# Right-to-Left Variant Implementation

This directory contains a Haskell implementation of the right-to-left variant of local contextual type inference.

### Building from Source

* **Prerequisites**: [GHC](https://www.haskell.org/downloads/) and [Cabal](https://www.haskell.org/cabal/)
* **Build**: From this directory, run:
  ```bash
  cabal build
  ```

### Usage

* **Run the pair examples**

  To test the `pair` example:
  ```bash
  cabal run Poly
  ```

  Expected Output:

  ```bash
  --------------------------------------------------------------------------------
  Pair: (Pair (λx. x) 1) : (Int → Int) × Int
  [✓] Typing result: (Int → Int) × Int
  ```

* **Show detailed derivations**

  Add `--drv` argument to print the full derivation tree:

  ```bash
  cabal run Poly -- --drv
  ```

  Expected Output: Shows the complete derivation tree.

  ```bash
  --------------------------------------------------------------------------------
  Pair: (Pair (λx. x) 1) : (Int → Int) × Int
  [✓] Typing result: (Int → Int) × Int

  [Ty-Ann] ∅ ⊢ □ ⇒ Pair (λ. e0) 1 : (Int → Int) × Int ⇒ (Int → Int) × Int
    [Ty-App] ∅ ⊢ (Int → Int) × Int ⇒ Pair (λ. e0) 1 ⇒ (Int → Int) × Int
      [Ty-App] ∅ ⊢ [1] ↝ (Int → Int) × Int ⇒ Pair (λ. e0) ⇒ Int → (Int → Int) × Int
        [Ty-Sub] ∅ ⊢ [λ. e0] ↝ [1] ↝ (Int → Int) × Int ⇒ Pair ⇒ (Int → Int) → Int → (Int → Int) × Int
          [Ty-Pair] ∅ ⊢ □ ⇒ Pair ⇒ ∀. ∀. t1 → t0 → t1 × t0
          [S-Forall-L] ∅; ∅ ⊢ ∀. ∀. t1 → t0 → t1 × t0 <: [λ. e0] ↝ [1] ↝ (Int → Int) × Int ⊣ ∅ ⇝ (Int → Int) → Int → (Int → Int) × Int
            [S-Forall-L] ∅; ∅, ^ ⊢ ∀. t1 → t0 → t1 × t0 <: [λ. e0] ↝ [1] ↝ (Int → Int) × Int ⊣ ∅, =Int → Int ⇝ (Int → Int) → Int → (Int → Int) × Int
              [S-Term-Close] ∅; ∅, ^, ^ ⊢ t1 → t0 → t1 × t0 <: [λ. e0] ↝ [1] ↝ (Int → Int) × Int ⊣ ∅, =Int → Int, =Int ⇝ (Int → Int) → Int → (Int → Int) × Int
                [S-Term-Close] ∅; ∅, ^, ^ ⊢ t0 → t1 × t0 <: [1] ↝ (Int → Int) × Int ⊣ ∅, =Int → Int, =Int ⇝ Int → (Int → Int) × Int
                  [S-Type] ∅; ∅, ^, ^ ⊢ t1 × t0 <: (Int → Int) × Int ⊣ ∅, =Int → Int, =Int ⇝ (Int → Int) × Int
                    [S-Prod] ∅; ∅, ^, ^ ⊢ t1 × t0 <: (Int → Int) × Int ⊣ ∅, =Int → Int, =Int
                      [S-Ex-L] ∅; ∅, ^, ^ ⊢ t1 <: Int → Int ⊣ ∅, =Int → Int, ^
                      [S-Ex-L] ∅; ∅, =Int → Int, ^ ⊢ t0 <: Int ⊣ ∅, =Int → Int, =Int
                  [Ty-Sub] ∅, =Int → Int, =Int ⊢ Int ⇒ 1 ⇒ Int
                    [Ty-Int] ∅, =Int → Int, =Int ⊢ □ ⇒ 1 ⇒ Int
                    [S-Type] ∅, =Int → Int, =Int; ∅ ⊢ Int <: Int ⊣ ∅ ⇝ Int
                      [S-Int] ∅, =Int → Int, =Int; ∅ ⊢ Int <: Int ⊣ ∅
                [Ty-Abs1] ∅, =Int → Int, =Int ⊢ Int → Int ⇒ λ. e0 ⇒ Int → Int
                  [Ty-Sub] ∅, =Int → Int, =Int, :Int ⊢ Int ⇒ e0 ⇒ Int
                    [Ty-Var] ∅, =Int → Int, =Int, :Int ⊢ □ ⇒ e0 ⇒ Int
                      [Lookup] Int in Γ
                    [S-Type] ∅, =Int → Int, =Int, :Int; ∅ ⊢ Int <: Int ⊣ ∅ ⇝ Int
                      [S-Int] ∅, =Int → Int, =Int, :Int; ∅ ⊢ Int <: Int ⊣ ∅
  ```
