module Implicit.Language.Find where

open import Implicit.Language.Base
open import Implicit.Language.Shift.Base
open import Implicit.Language.Lookup.Base
open import Implicit.Language.Occur.Base

-- find A k j
-- at j-th position of A type, should have a bound variable, example: |-1 forall a. a -> a <: Int
data find : Type m → Fin m → Counter → Set where
  f-∞       : k ε A
            → find A k ∞
  f-arr-𝕚-l : k ε A
            → find (A `→ B) k (𝕚 j)
  f-arr-𝕚-r : find B k j
            → find (A `→ B) k (𝕚 j)
  f-arr-𝕔   : (¬inA : k ¬ε A)
            → find B k j
            → find (A `→ B) k (𝕔 j)
  f-∀       : find A (#S k) j
            → find (`∀ A) k j

find-ε : find A k ∞
       → k ε A
find-ε (f-∞ x) = x
find-ε (f-∀ fd) = ε-∀ (find-ε fd)

find-arr-r : find B k ∞
         → find (A `→ B) k ∞
find-arr-r fd = f-∞ (ε-arr-r (find-ε fd))

find-arr-l : find A k ∞
           → find (A `→ B) k ∞
find-arr-l fd = f-∞ (ε-arr-l (find-ε fd))
