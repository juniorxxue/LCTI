module Implicit.Algo.Properties.PSubsumption where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.Reflexivity
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Regularity
open import Implicit.Algo.Properties.Polarity
open import Implicit.Algo.Properties.PStrengthenTVar
open import Implicit.Algo.Properties.PStrengthenSVar
open import Implicit.Algo.Properties.Weaken
open import Implicit.Algo.Properties.Irrelevance
open import Implicit.Algo.Properties.PTrans

postulate
  ≊-weaken : Σ₁ ≊ Σ₂
           → ↑tmᶜ0 Σ₁ ⇘ Σ₁'
           → ↑tmᶜ0 Σ₂ ⇘ Σ₂'
           → Σ₁' ≊ Σ₂'

postulate
  t-inf-open-false : Γ ⊢ □ ⇒ e ⇒ A
                   → Γ ⋈ ⊢o A
                   → ⊥

postulate
  ⊢to≤ : Γ ⊢ Σ ⇒ e ⇒ A
       → Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ A

postulate
  subsumption :  Γ ⊢ Σ ⇒ e ⇒ A
               → Σ ≊ Σ'
               → Γ ⋈ ⊢ A ≤⁺ Σ' ⊣ Γ ⋈ ↪ A'
               → Γ ⊢ Σ' ⇒ e ⇒ A'

postulate
  subsumption0 : Γ ⊢ □ ⇒ e ⇒ A
               → Γ ⊢ τ A ⇒ e ⇒ A

postulate
  s-refined-p : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
              → Δ ⊢ B ≤⁺ Σ ⊣ Δ ↪ B

