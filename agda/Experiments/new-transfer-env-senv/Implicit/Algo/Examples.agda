module Implicit.Algo.Examples where

open import Implicit.Common
open import Implicit.Algo

idEnv : Env 1 0
idEnv = ∅ , `∀ (‶ #0 `→ ‶ #0)

id[Int]1 : idEnv ⊢ □ ⇒ ((` #0) [ Int ]) · (lit 1) ⇒ Int
id[Int]1 = ⊢app (⊢tapp (⊢sub (⊢var refl) ne-tapp gc-var
                       (s-∀-t
                         (s-term-c ⊢c-var=0 ⊢c-var=0
                           (⊢sub ⊢lit ne-τ gc-i
                                 (s-ex-r= ⊢c-int Z s-int))
                           (s-empty ⊢c-var=0)) (st-arr st-var-eq st-var-eq))))

idExp : Term 0 0
idExp = Λ (((ƛ ` #0) ⦂ ‶ #0 `→ ‶ #0))

{-
idExp[Int]1 : ∅ ⊢ □ ⇒ (idExp [ Int ]) · (lit 1) ⇒ Int
idExp[Int]1 = {!!}
-}

-- implicit inst
id1 : idEnv ⊢ □ ⇒ (` #0) · (lit 1) ⇒ Int
id1 = ⊢app (⊢sub (⊢var refl) ne-app gc-var
                 (s-∀l-eq (s-term-o ⊢o-var^0 ⊢lit
                                    (s-ex-r^ ⊢c-int Z ⟹^0)
                                    (s-empty ⊢c-var=0))
                                    (st-arr st-var-eq st-var-eq)))

#1 : Fin 2
#1 = #S #0

fEnv : Env 1 0
fEnv = ∅ , `∀ `∀ (‶ #1 `→ ‶ #0 `→ ‶ #0)

f12 : fEnv ⊢ □ ⇒ (` #0) · (lit 1) · (lit 2) ⇒ Int
f12 = ⊢app (⊢app (⊢sub (⊢var refl) ne-app gc-var
                       (s-∀l-eq (s-∀l-eq (s-term-o (⊢o-var^S ⊢o-var^0) ⊢lit
                                                   (s-ex-r^ ⊢c-int (S^ Z) (⟹^S ⟹^0))
                                                   (s-term-o ⊢o-var^0 ⊢lit (s-ex-r^ ⊢c-int Z ⟹^0) (s-empty ⊢c-var=0)))
                                                     (st-arr (st-var-neq λ ()) (st-arr st-var-eq st-var-eq)))
                                (st-arr st-var-eq (st-arr st-int st-int)))))
                       

