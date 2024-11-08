module Implicit.Algo.Examples where

open import Implicit.Common
open import Implicit.Algo

idEnv : Env 1 0
idEnv = ∅ , `∀ (‶ #0 `→ ‶ #0)

idExp : Term 0 0
idExp = Λ (((ƛ ` #0) ⦂ ‶ #0 `→ ‶ #0))

{-
idExp[Int]1 : ∅ ⊢ □ ⇒ (idExp [ Int ]) · (lit 1) ⇒ Int
idExp[Int]1 = {!!}
-}

-- implicit inst
id1 : idEnv ⊢ □ ⇒ (` #0) · (lit 1) ⇒ Int
id1 = ⊢app (⊢sub (⊢var refl) ne-app gc-var
                 (s-∀l (s-term-o ⊢o-var^0 ⊢lit (s-ex-r^ ⊢c-int Z (⟹^0 st-int)) (s-empty ⊢c-var=0)) st-int st-var-eq))
                       

