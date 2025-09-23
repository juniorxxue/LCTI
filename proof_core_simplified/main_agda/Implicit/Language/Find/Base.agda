module Implicit.Language.Find.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.Base
open import Implicit.Language.Occur.Base
open import Implicit.Language.Regular.Base

data IsoInf : Counter → Set where
  i∞-z : IsoInf (𝕚 ∞)
  i∞-i : IsoInf j
       → IsoInf (𝕚 j)

-- find A k j
-- at j-th position of A type, should have a bound variable, example: |-1 forall a. a -> a <: Int
data find : Type m → Fin m → Counter → Set where
  f-∞       : (inA : k ε A)
            → find A k ∞
  f-iso     : (iso : IsoInf j)
            → find (‶ k) k j
  f-arr-𝕚-l : (inA : k ε A)
            → find (A `→ B) k (𝕚 j)
  f-arr-𝕚-r : (¬inA : k ¬ε A)
            → find B k j
            → find (A `→ B) k (𝕚 j)
  f-arr-𝕔   : (¬inA : k ¬ε A)
            → find B k j
            → find (A `→ B) k (𝕔 j)
  f-∀-𝕚     : find A (#S k) (𝕚 j)
            → find (`∀ A) k (𝕚 j)
  f-∀-𝕔     : find A (#S k) (𝕔 j)
            → find (`∀ A) k (𝕔 j)

find-ε : find A k ∞
       → k ε A
find-ε (f-∞ inA) = inA

find-arr-l : find A k ∞
           → find (A `→ B) k ∞
find-arr-l (f-∞ inA) = f-∞ (ε-arr-l inA)

find-Z-false : find A k Z
             → ⊥
find-Z-false (f-iso ())
