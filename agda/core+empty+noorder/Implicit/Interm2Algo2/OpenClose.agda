{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}
module Implicit.Interm2Algo2.OpenClose where

open import Implicit.Language.All

⊆/x-openclose : Γ ⊆ Δ w/v X
              → Γ ⊢o ‶ X ⊎ Γ ⊢c ‶ X
⊆/x-openclose (ext-Z^ regΓ regA) = inj₁ (⊢o-var-^ Z)
⊆/x-openclose (ext-Z∙ regΓ) = inj₂ (⊢c-var-∙ Z)
⊆/x-openclose (ext-Z= regΓ regA) = inj₂ (⊢c-var-= Z)
⊆/x-openclose (ext-S^ ext) with ⊆/x-openclose ext
... | inj₁ (⊢o-var-^ x) = inj₁ (⊢o-var-^ (S^ x))
... | inj₂ (⊢c-var-∙ inΔ) = inj₂ (⊢c-var-∙ (S^ inΔ))
... | inj₂ (⊢c-var-= inΔ) = inj₂ (⊢c-var-= (S^ inΔ))
⊆/x-openclose (ext-S∙ ext) with ⊆/x-openclose ext
... | inj₁ (⊢o-var-^ x) = inj₁ (⊢o-var-^ (S∙ x))
... | inj₂ (⊢c-var-∙ inΔ) = inj₂ (⊢c-var-∙ (S∙ inΔ))
... | inj₂ (⊢c-var-= inΔ) = inj₂ (⊢c-var-= (S∙ inΔ))
⊆/x-openclose (ext-S= ext regA) with ⊆/x-openclose ext
... | inj₁ (⊢o-var-^ x) = inj₁ (⊢o-var-^ (S= x))
... | inj₂ (⊢c-var-∙ inΔ) = inj₂ (⊢c-var-∙ (S= inΔ))
... | inj₂ (⊢c-var-= inΔ) = inj₂ (⊢c-var-= (S= inΔ))
⊆/x-openclose (ext-mark x x₁) = inj₂ (⊢c-var-∙ (S⋈ x₁))

⊆/-openclose : Γ ⊆ Δ w/t A
              → Γ ⊢o A ⊎ Γ ⊢c A
⊆/-openclose (ext-int x) = inj₂ ⊢c-int
⊆/-openclose (ext-var x) = ⊆/x-openclose x
⊆/-openclose (ext-arr ext ext₁) with ⊆/-openclose ext | ⊆/-openclose ext₁
... | inj₁ x | inj₁ x₁ = inj₁ (⊢o-arr-l x)
... | inj₁ x | inj₂ y = inj₁ (⊢o-arr-l x)
... | inj₂ y | inj₁ x with refl ← ⊆/-⊢c-eq ext y = inj₁ (⊢o-arr-r x)
... | inj₂ y | inj₂ y₁ with refl ← ⊆/-⊢c-eq ext y
                       with refl ← ⊆/-⊢c-eq ext₁ y₁ = inj₂ (⊢c-arr y y₁)
⊆/-openclose (ext-∀ ext) with ⊆/-openclose ext
... | inj₁ x = inj₁ (⊢o-∀ x)
... | inj₂ y = inj₂ (⊢c-∀ y)
