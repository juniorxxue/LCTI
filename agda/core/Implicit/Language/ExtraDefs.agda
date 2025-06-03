module Implicit.Language.ExtraDefs where

open import Implicit.Language.All


-- occur only at the end
infix 3 _ε'_
data _ε'_ : Fin m → Type m → Set where
  ε-var : k ε' (‶ k)
  ε-arr : k ¬ε A
        → k ε' B
        → k ε' (A `→ B)
  ε-∀ : #S k ε' A
      → k ε' (`∀ A)

-- not occur only at the end
infix 3 _¬ε'_
data _¬ε'_ : Fin m → Type m → Set where
  ¬ε'-int : k ¬ε' Int
  ¬ε'-var : k ≢ X
          → k ¬ε' ‶ X
  ¬ε'-arr-l : k ε A
          → k ¬ε' (A `→ B)
  ¬ε'-arr-r : k ¬ε A
            → k ¬ε' B
            → k ¬ε' (A `→ B)
  ¬ε'-∀ : #S k ¬ε' A
        → k ¬ε' (`∀ A)


ε'-dec : ∀ (k : Fin m) A
       → k ε' A ⊎ k ¬ε' A
ε'-dec k Int = inj₂ ¬ε'-int
ε'-dec k (‶ X) with k #≟ X
... | yes refl = inj₁ ε-var
... | no ¬p = inj₂ (¬ε'-var ¬p)
ε'-dec k (A `→ B) with ε-dec {k = k} {A = A}
... | inj₁ p = inj₂ (¬ε'-arr-l p)
... | inj₂ ¬p with ε'-dec k B
... | inj₁ y = inj₁ (ε-arr ¬p y)
... | inj₂ n = inj₂ (¬ε'-arr-r ¬p n)
ε'-dec k (`∀ A) with ε'-dec (#S k) A
... | inj₁ x = inj₁ (ε-∀ x)
... | inj₂ y = inj₂ (¬ε'-∀ y)
