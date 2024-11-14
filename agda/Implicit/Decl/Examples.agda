module Implicit.Decl.Examples where

open import Implicit.Language
open import Implicit.Decl.Base

idEnv : Env 1 0
idEnv = ∅ , `∀ (‶ #0 `→ ‶ #0)

idExp : Term 0 0
idExp = Λ (((ƛ ` #0) ⦂ ‶ #0 `→ ‶ #0))

-- implicit inst
id1 : idEnv ⊢ Z # (` #0) · (lit 1) ⦂ Int
id1 = ⊢app₂ (⊢sub (⊢var Z)
                  (s-∀l (s-arr₂ s-var s-refl) case-𝕚 (f-arr-𝕚-l ^in-var) st-var st-var)
                  nz-I)
            ⊢lit


fEnv : Env 1 0
fEnv = ∅ , `∀ `∀ (‶ #1 `→ ‶ #0 `→ ‶ #0)

