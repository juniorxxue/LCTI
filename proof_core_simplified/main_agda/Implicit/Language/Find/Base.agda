module Implicit.Language.Find.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.Base
open import Implicit.Language.Occur.Base
open import Implicit.Language.Regular.Base

data □like : Mask → Set where
  □like-Z : □like `□
  □like-S : □like j
          → □like (□ · j)

-- find A k j
-- at j-th position of A type, should have a bound variable, example: |-1 forall a. a -> a <: Int
data find : Type m → Fin m → Mask → Set where
  f-□       : (inA : k ε A)
            → find A k `□
  f-iso     : (iso : □like j)
            → find (‶ k) k j
  f-arr-l : (inA : k ε A)
            → find (A `→ B) k (□ · j)
  f-arr-r : (¬inA : k ¬ε A)
            → find B k j
            → find (A `→ B) k (i · j)
  f-∀     : find A (#S k) (i · j)
          → find (`∀ A) k (i · j)

find-ε : find A k `□
       → k ε A
find-ε (f-□ inA) = inA
find-ε (f-iso iso) = ε-var

find-arr-l : find A k `□
           → find (A `→ B) k `□
find-arr-l (f-□ inA) = f-□ (ε-arr-l inA)
find-arr-l (f-iso iso) = f-□ (ε-arr-l ε-var)

find-Z-false : find A k `■
             → ⊥
find-Z-false (f-iso ())
