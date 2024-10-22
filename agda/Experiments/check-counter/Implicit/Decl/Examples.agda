module Implicit.Decl.Examples where

open import Implicit.Common
open import Implicit.Decl

idEnv : Env 1 0
idEnv = ∅ , `∀ (‶ #0 `→ ‶ #0)

-- id[Int]1 : idEnv ⊢ Z # ((` #0) [ Int ]) · (lit 1) ⦂ Int

idExp : Term 0 0
idExp = Λ (((ƛ ` #0) ⦂ ‶ #0 `→ ‶ #0))

idExp[Int]1 : ∅ ⊢ Z # (idExp [ Int ]) · (lit 1) ⦂ Int
idExp[Int]1 = ⊢app₁ (⊢tapp (⊢tabs₁ (⊢ann (⊢lam₁ (⊢sub (⊢var refl) s-var nz-∞)))) (st-arr st-var-eq st-var-eq))
                    (⊢sub ⊢lit s-int nz-∞)

idExp[Int] : ∅ ⊢ Z # idExp [ Int ] ⦂ Int `→ Int
idExp[Int] = ⊢tapp (⊢tabs₁ (⊢ann (⊢lam₁ (⊢sub (⊢var refl) s-var nz-∞)))) (st-arr st-var-eq st-var-eq)

-- implicit inst
id1 : idEnv ⊢ Z # (` #0) · (lit 1) ⦂ Int
id1 = ⊢app₂ (⊢sub (⊢var refl)
                  (s-∀l (s-arr₂ s-var s-refl) (f-S₁ b-var))
                  nz-S)
            ⊢lit


fEnv : Env 1 0
fEnv = ∅ , `∀ `∀ (‶ #1 `→ ‶ #0 `→ ‶ #0)

f12 : fEnv ⊢ Z # (` #0) · (lit 1) · (lit 2) ⦂ Int
f12 = ⊢app₂ (⊢app₂ (⊢sub (⊢var refl)
                         (s-∀l (s-∀l (s-arr₂ (s-var-r (S= Z) s-int)
                                             (s-arr₂ (s-var-r Z s-int) s-refl)) (f-S₂ (f-S₂ (f-Z b-var)))) (f-S₃ (f-S₁ b-var)))
                         nz-S) ⊢lit) ⊢lit
