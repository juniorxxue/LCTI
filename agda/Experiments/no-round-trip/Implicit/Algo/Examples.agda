module Implicit.Algo.Examples where

open import Implicit.Common
open import Implicit.Algo

idEnv : Env 1 0
idEnv = ∅ , `∀ (‶ #0 `→ ‶ #0)

-- implicit inst
id1 : idEnv ⊢ □ ⇒ (` #0) · (lit 1) ⇒ Int
id1 = ⊢app (⊢sub (⊢var refl) ne-app gc-var
                 (s-∀l-eq (s-term-o ⊢o-var^0 ⊢lit (s-ex-r^ ⊢c-int Z ⟹^0) (s-empty ⊢c-var=0 (inst-var Z inst-int)))))
#1 : Fin 2
#1 = #S #0

fEnv : Env 1 0
fEnv = ∅ , `∀ `∀ (‶ #1 `→ ‶ #0 `→ ‶ #0)

{-
f12 : fEnv ⊢ □ ⇒ (` #0) · (lit 1) · (lit 2) ⇒ Int
f12 = ⊢app (⊢app (⊢sub (⊢var refl) ne-app gc-var
                       (s-∀l-eq (s-∀l-eq (s-term-o (⊢o-var^S ⊢o-var^0) ⊢lit
                                                   (s-ex-r^ ⊢c-int (S^ Z) (⟹^S ⟹^0))
                                                   (s-term-o ⊢o-var^0 ⊢lit (s-ex-r^ ⊢c-int Z ⟹^0) (s-empty ⊢c-var=0)))
                                                     (st-arr (st-var-neq λ ()) (st-arr st-var-eq st-var-eq)))
                                (st-arr st-var-eq (st-arr st-int st-int)))))
-}                                
                       

