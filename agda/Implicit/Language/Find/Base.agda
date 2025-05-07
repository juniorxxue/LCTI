module Implicit.Language.Find.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.Base
open import Implicit.Language.Occur.Base
open import Implicit.Language.Regular.Base

infix 3 _↑tyʲ_⇘_
data _↑tyʲ_⇘_ : Counter m → Fin (1 + m) → Counter (1 + m) → Set where
  ↑tyʲ-Z : Z ↑tyʲ k ⇘ Z
  ↑tyʲ-∞ : ∞ ↑tyʲ k ⇘ ∞
  ↑tyʲ-𝕊 : w ↑tyʲ k ⇘ w'
         → j ↑tyʲ k ⇘ j'
         → 𝕊₍ w ₎ j ↑tyʲ k ⇘ 𝕊₍ w' ₎ j'
  ↑tyʲ-𝕥 : j ↑tyʲ k ⇘ j'
         → (upA : A ↑ty k ⇘ A')
         → 𝕥₍ A ₎ j ↑tyʲ k ⇘ 𝕥₍ A' ₎ j'

infix 3 ↑tyʲ0_⇘_
↑tyʲ0_⇘_ : Counter m → Counter (1 + m) → Set
↑tyʲ0_⇘_ j = _↑tyʲ_⇘_ j #0

postulate
  ↑tyʲ-unique : j ↑tyʲ k ⇘ j'
            → j ↑tyʲ k ⇘ j''
            → j' ≡ j''

  ↑tyʲ0-total : ∀ (j : Counter m)
            → ∃[ j' ](↑tyʲ0 j ⇘ j')


  ↑tyʲ-comm0' : ∀ {k : Fin (1 + m)} {j jₖ j₀ jₖ₊₁}
            → j ↑tyʲ k ⇘ jₖ
            → ↑tyʲ0 jₖ ⇘ jₖ₊₁
            → ↑tyʲ0 j ⇘ j₀
            → j₀ ↑tyʲ #S k ⇘ jₖ₊₁

  nonz-↑tyʲ' : NonZ j'
          → j ↑tyʲ k ⇘ j'
          → NonZ j

  nonz-↑tyʲ : NonZ j
          → j ↑tyʲ k ⇘ j'
          → NonZ j


data ¬find1 : Type m → Fin m → Counter m → Set where
  ¬f1-∞ : k ¬ε A
        → ¬find1 A k Z
  ¬f1-arr1 : k ¬ε A
           → ¬find1 B k j
           → ¬find1 (A `→ B) k (𝕊₍ ∞ ₎ j)
  ¬f1-arr2 : ¬find1 B k j
           → ¬find1 (A `→ B) k (𝕊₍ Z ₎ j)
  ¬f1-∀-𝕊 : ¬find1 A (#S k) (𝕊₍ w' ₎ j')
         → (upj : ↑tyʲ0 j ⇘ j')
         → (upw : ↑tyʲ0 w ⇘ w')
         → ¬find1 (`∀ A) k (𝕊₍ w ₎ j)


data find1 : Type m → Fin m → Counter m → Set where
  f1-∞ : k ε A → find1 A k Z
  f1-arr-l-∞ : k ε A
           → find1 (A `→ B) k (𝕊₍ ∞ ₎ j)
  f1-arr-r-∞ : k ¬ε A
           → find1 B k j
           → find1 (A `→ B) k (𝕊₍ ∞ ₎ j)
  f1-arr-r-Z : find1 B k j
             → find1 (A `→ B) k (𝕊₍ Z ₎ j)
  f1-∀-𝕊 : find1 A (#S k) (𝕊₍ w' ₎ j')
         → (upj : ↑tyʲ0 j ⇘ j')
         → (upw : ↑tyʲ0 w ⇘ w')
         → find1 (`∀ A) k (𝕊₍ w ₎ j)
-- lack a case T counter


data find2 : Type m → Fin m → Counter m → Set where
  f2-∞ : k ε A
      → find2 A k ∞

  f2-arr-l : find1 A k w
          → find2 (A `→ B) k (𝕊₍ w ₎ j)

  f2-arr-r : ¬find1 A k w
          → find2 A k j
          → find2 (A `→ B) k (𝕊₍ w ₎ j)

  f2-∀-𝕊  : find2 A (#S k) j'
         → (upj : ↑tyʲ0 j ⇘ j')
         → find2 (`∀ A) k (𝕊₍ w ₎ j)

  f2-𝕥    : find2 A (#S k) j'
          → (upj : ↑tyʲ0 j ⇘ j')
          → find2 (`∀ A) k (𝕥₍ B ₎ j)

{- Example
_ : find2 ((Int `→ ‶ #0) `→ ‶ #0) #0 (𝕊₍ 𝕊₍ Z ₎ Z ₎ Z)
_ = f2-arr-l (f1-arr-r-Z (f1-∞ ε-var))
-}

postulate

  find-ε : find2 A k ∞
         → k ε A

  find-arr-l : find2 A k ∞
           → find2 (A `→ B) k ∞


find-Z-false : find2 A k Z
             → ⊥
find-Z-false ()


infix 3 _⊢rʲ_
data _⊢rʲ_ : Env n m → Counter m → Set where
  rj-Z : Γ ⊢rʲ Z
  rj-∞ : Γ ⊢rʲ ∞
  rj-𝕊 : Γ ⊢rʲ j
       → Γ ⊢rʲ (𝕊₍ w ₎ j)
  rj-𝕥 : Γ ⊢rʲ j
       → (regA : Γ ⊢r A)
       → Γ ⊢rʲ (𝕥₍ A ₎ j)
