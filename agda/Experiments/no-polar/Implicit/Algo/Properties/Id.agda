module Implicit.Algo.Properties.Id where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Split
open import Implicit.Algo.Properties.Subst

data Split : (Σ : Context n m) → (A : Type m) → Set where
  case-τ :
      (spl : ⟦ Σ , A ⟧→s⟦ τ T , A' ⟧)
    → (eq : T ≡ A')
    → Split Σ A

  case-□ :
      (spl : ⟦ Σ , A ⟧→s⟦ □ , A' ⟧)
    → Split Σ A

postulate

  ⊢id0 : Γ ⊢ τ B ⇒ e ⇒ A
       → B ≡ A

  ≤id0 : Γ ⊢ A ≤ τ B ⊣ Γ' ↪ C
     → B ≡ C
