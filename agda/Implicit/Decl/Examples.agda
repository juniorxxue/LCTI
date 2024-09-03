module Implicit.Decl.Examples where

open import Implicit.Common
open import Implicit.Decl

idEnv : Env 1 0
idEnv = ∅ , `∀ (‶ #0 `→ ‶ #0)

id[Int]1 : idEnv ⊢ Z # ((` #0) [ Int ]) · (lit 1) ⦂ Int
id[Int]1 = {!!}

idExp : Term 0 0
idExp = Λ (((ƛ ` #0) ⦂ ‶ #0 `→ ‶ #0))

idExp[Int]1 : ∅ ⊢ Z # (idExp [ Int ]) · (lit 1) ⦂ Int
idExp[Int]1 = {!!}

idExp[Int] : ∅ ⊢ Z # idExp [ Int ] ⦂ Int `→ Int
idExp[Int] = {!!}

-- implicit inst
id1 : idEnv ⊢ Z # (` #0) · (lit 1) ⦂ Int
id1 = ⊢app₂ (⊢sub (⊢var refl)
                  (s-∀l (s-arr₂ (s-var-r Z s-int) (s-refl (slv-var Z slv-int))) (f-S₁ b-var)) nz-S)
            ⊢lit
