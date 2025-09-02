module Implicit.Algo.Properties.Peek where

open import Implicit.Language.All
open import Implicit.Algo.Base


pk-ε : A ~~pk~~ B w/ k ↪ T
     → k ε A
pk-ε pk-var-l = ε-var
pk-ε (pk-arr-l pk) = ε-arr-l (pk-ε pk)
pk-ε {k = k} (pk-arr-r {A = A} pk) with ε-dec {k = k} {A = A}
... | inj₁ inA = ε-arr-l inA
... | inj₂ ¬inA = ε-arr-r ¬inA (pk-ε pk)
pk-ε (pk-∀ pk upC) = ε-∀ (pk-ε pk)
