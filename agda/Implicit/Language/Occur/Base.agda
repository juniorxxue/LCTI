module Implicit.Language.Occur.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All

-- lookup a variable (can represent three kinds of entries), in a type
infix 3 _ε_
data _ε_ : Fin m → Type m → Set where
  ε-var :
      k ε (‶ k)
  ε-arr-l :
      k ε A
    → k ε A `→ B
  ε-arr-r :
      (k ¬ε A)
    → k ε B
    → k ε A `→ B
  ε-∀ :
      #S k ε A
    → k ε `∀ A

infix 3 _¬εᵍ_
data _¬εᵍ_ : Fin m → Env n m → Set where
  Z : k ¬εᵍ ∅
  Z^ : #0 ¬εᵍ Γ ,^
  Z∙ : #0 ¬εᵍ Γ ,∙
  Z= : ↑ty0 A ⇘ A'
     → (#0 ¬ε A')
     → #0 ¬εᵍ Γ ,= A
  S, : (k ¬ε A)
       → k ¬εᵍ Γ
       → k ¬εᵍ Γ , A
  S∙ : k ¬εᵍ Γ
     → #S k ¬εᵍ Γ ,∙
  S^ : k ¬εᵍ Γ
     → #S k ¬εᵍ Γ ,^
  S= : k ¬εᵍ Γ
     → ↑ty0 A ⇘ A'
     → (#S k ¬ε A')
     → #S k ¬εᵍ Γ ,= A
