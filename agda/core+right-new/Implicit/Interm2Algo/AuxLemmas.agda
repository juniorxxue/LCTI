module Implicit.Interm2Algo.AuxLemmas where


open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm2Algo.EnvDiff
open import Implicit.Interm2Algo.ExtIrrev


ⅆ-⊆/c : Δ ⅆ Δ' ≋ Γ ⅆ Γ'
     → Γ' ⊆ Δ' w/t A w/c j
     → Γ ⊆ Δ w/t A w/c j
ⅆ-⊆/c dd (⊆Z regΓ) with refl ← ⅆ-out-eq dd = ⊆Z (⊆-regular regΓ (ⅆ-l-⊆ dd))
ⅆ-⊆/c dd (⊆∞ ext) = ⊆∞ (ⅆ-⊆/ dd ext)
ⅆ-⊆/c dd (⊆I ext ext₁) with ⅆ-total-mid dd (⊆/c-⊆ ext₁) (⊆/-⊆ ext)
... | ⟨ Ω' , ⟨ dd1 , dd2 ⟩ ⟩ = ⊆I (ⅆ-⊆/ dd2 ext) (ⅆ-⊆/c dd1 ext₁)
ⅆ-⊆/c dd (⊆C cloA ext) = ⊆C (⊆-⊢c cloA (ⅆ-r-⊆ dd)) (ⅆ-⊆/c dd ext)
ⅆ-⊆/c dd (⊆∀-I ext upj) with ⅆ-⊆/c (ⅆS==2 dd {!!}) ext
... | r = ⊆∀-I r upj
ⅆ-⊆/c dd (⊆∀-I-no ext upj) with ⅆ-⊆/c (ⅆS^ dd) ext
... | r = ⊆∀-I-no r upj
ⅆ-⊆/c dd (⊆∀-C ext upj) with ⅆ-⊆/c (ⅆS==2 dd {!!}) ext
... | r = ⊆∀-C r upj
ⅆ-⊆/c dd (⊆∀-C-no ext upj) with ⅆ-⊆/c (ⅆS^ dd) ext
... | r = ⊆∀-C-no r upj
ⅆ-⊆/c dd (⊆∀-T ext upj) with ⅆ-⊆/c (ⅆS==1 dd {!!}) ext
... | r = ⊆∀-T r upj
ⅆ-⊆/c dd (⊆I-X regΓ) with refl ← ⅆ-out-eq dd = ⊆I-X (⊆-regular regΓ (ⅆ-l-⊆ dd))
ⅆ-⊆/c dd (⊆C-X regΓ) with refl ← ⅆ-out-eq dd = ⊆C-X (⊆-regular regΓ (ⅆ-l-⊆ dd))
ⅆ-⊆/c dd (⊆T-X regΓ) with refl ← ⅆ-out-eq dd = ⊆T-X (⊆-regular regΓ (ⅆ-l-⊆ dd))
