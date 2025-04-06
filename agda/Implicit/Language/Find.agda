module Implicit.Language.Find where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.Base
open import Implicit.Language.Occur.Base

infix 3 _↑tyʲ_⇘_
data _↑tyʲ_⇘_ : Counter m → Fin (1 + m) → Counter (1 + m) → Set where
  ↑tyʲ-Z : Z ↑tyʲ k ⇘ Z
  ↑tyʲ-∞ : ∞ ↑tyʲ k ⇘ ∞
  ↑tyʲ-𝕚 : j ↑tyʲ k ⇘ j'
         → (𝕚 j) ↑tyʲ k ⇘ (𝕚 j')
  ↑tyʲ-𝕔 : j ↑tyʲ k ⇘ j'
         → (𝕔 j) ↑tyʲ k ⇘ (𝕔 j')
  ↑tyʲ-𝕥 : j ↑tyʲ k ⇘ j'
         → (upA : A ↑ty k ⇘ A')
         → 𝕥₍ A ₎ j ↑tyʲ k ⇘ 𝕥₍ A' ₎ j'

infix 3 ↑tyʲ0_⇘_
↑tyʲ0_⇘_ : Counter m → Counter (1 + m) → Set
↑tyʲ0_⇘_ j = _↑tyʲ_⇘_ j #0


↑tyʲ-unique : j ↑tyʲ k ⇘ j'
            → j ↑tyʲ k ⇘ j''
            → j' ≡ j''
↑tyʲ-unique ↑tyʲ-Z ↑tyʲ-Z = refl
↑tyʲ-unique ↑tyʲ-∞ ↑tyʲ-∞ = refl
↑tyʲ-unique (↑tyʲ-𝕚 up1) (↑tyʲ-𝕚 up2) = cong 𝕚 (↑tyʲ-unique up1 up2)
↑tyʲ-unique (↑tyʲ-𝕔 up1) (↑tyʲ-𝕔 up2) = cong 𝕔 (↑tyʲ-unique up1 up2)
↑tyʲ-unique (↑tyʲ-𝕥 up1 upA) (↑tyʲ-𝕥 up2 upA₁)
  with refl ← ↑ty-unique upA upA₁
  with refl ← ↑tyʲ-unique up1 up2 = refl

-- find A k j
-- at j-th position of A type, should have a bound variable, example: |-1 forall a. a -> a <: Int
data find : Type m → Fin m → Counter m → Set where
  f-∞       : k ε A
            → find A k ∞
  f-arr-𝕚-l : k ε A
            → find (A `→ B) k (𝕚 j)
  f-arr-𝕚-r : (¬inA : k ¬ε A)
            → find B k j
            → find (A `→ B) k (𝕚 j)
  f-arr-𝕔   : (¬inA : k ¬ε A)
            → find B k j
            → find (A `→ B) k (𝕔 j)
  f-∀-𝕚     : find A (#S k) (𝕚 j')
            → (upj : ↑tyʲ0 j ⇘ j')
            → find (`∀ A) k (𝕚 j)
  f-∀-𝕔     : find A (#S k) (𝕔 j')
            → (upj : ↑tyʲ0 j ⇘ j')
            → find (`∀ A) k (𝕔 j)
  f-𝕥       : find A (#S k) j'
            → (upj : ↑tyʲ0 j ⇘ j')
            → find (`∀ A) k (𝕥₍ B ₎ j)

find-ε : find A k ∞
       → k ε A
find-ε (f-∞ x) = x

{-
find-arr-r : find B k ∞
         → find (A `→ B) k ∞
find-arr-r fd = f-∞ (ε-arr-r {!!} (find-ε fd))
-}

find-arr-l : find A k ∞
           → find (A `→ B) k ∞
find-arr-l fd = f-∞ (ε-arr-l (find-ε fd))


find-Z-false : find A k Z
             → ⊥
find-Z-false ()
