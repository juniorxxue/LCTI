module Implicit.Language.Counter where

open import Implicit.Language.Base
open import Implicit.Language.Lookup

data Counter : Set where
  Z : Counter
  ∞ : Counter
  𝕚 : Counter → Counter
  𝕔 : Counter → Counter

variable
  j : Counter

data NonZ : Counter → Set where
  nz-∞ : NonZ ∞
  nz-I : NonZ (𝕚 j)
  nz-C : NonZ (𝕔 j)

data 𝕚𝕔 : Counter → Set where
  case-𝕚 : 𝕚𝕔 (𝕚 j)
  case-𝕔 : 𝕚𝕔 (𝕔 j)

-- find A k j
-- at j-th position of A type, should have a bound variable, example: |-1 forall a. a -> a <: Int
data find : Type m → Fin m → Counter → Set where
  f-∞       : k ε A
            → find A k ∞
  f-arr-𝕚-l : k ε A
            → find (A `→ B) k (𝕚 j)
  f-arr-𝕚-r : find B k j
            → find (A `→ B) k (𝕚 j)
  f-arr-𝕔   : (¬inA : ¬ (k ε A))
            → find B k j
            → find (A `→ B) k (𝕔 j)
  f-∀       : find A (#S k) j
            → find (`∀ A) k j
