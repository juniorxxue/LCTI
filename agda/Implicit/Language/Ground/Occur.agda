module Implicit.Language.Ground.Occur where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Occur.All
open import Implicit.Language.OpenClose.All
open import Implicit.Language.Norm.All
open import Implicit.Language.EnvOps.All
open import Implicit.Language.Ground.Base
open import Implicit.Language.Ground.Properties


grd-ε : k ε A
     → Γ ∋∙ k
     → Γ ≫ A ⇘ A%
     → k ε A%
grd-ε ε-var inΓ (grd-var= x) = ⊥-elim (∙∈-:=∈-false inΓ x)
grd-ε ε-var inΓ (grd-var∙ x) = ε-var
grd-ε (ε-arr-l inA) inΓ (grd-arr apA apA₁) = ε-arr-l (grd-ε inA inΓ apA)
grd-ε (ε-arr-r inA) inΓ (grd-arr apA apA₁) = ε-arr-r (grd-ε inA inΓ apA₁)
grd-ε (ε-∀ inA) inΓ (grd-∀ apA) = ε-∀ (grd-ε inA (S∙ inΓ) apA)

grd-ε-rev : k ε A%
         → k ¬εᵍ Γ
         → Γ ∋∙ k
         → Γ ≫ A ⇘ A%
         → k ε A
grd-ε-rev ε-var ninΓ inΓ (grd-var= x) = ⊥-elim (εᵍ-false x ε-var ninΓ)
grd-ε-rev ε-var ninΓ inΓ (grd-var∙ x) = ε-var
grd-ε-rev (ε-arr-l inA%) ninΓ inΓ (grd-var= x) = ⊥-elim (εᵍ-false x (ε-arr-l inA%) ninΓ)
grd-ε-rev (ε-arr-l inA%) ninΓ inΓ (grd-arr apA apA₁) = ε-arr-l (grd-ε-rev inA% ninΓ inΓ apA)
grd-ε-rev (ε-arr-r inA%) ninΓ inΓ (grd-var= x) = ⊥-elim (εᵍ-false x (ε-arr-r inA%) ninΓ)
grd-ε-rev (ε-arr-r inA%) ninΓ inΓ (grd-arr apA apA₁) = ε-arr-r (grd-ε-rev inA% ninΓ inΓ apA₁)
grd-ε-rev (ε-∀ inA%) ninΓ inΓ (grd-var= x) = ⊥-elim (εᵍ-false x (ε-∀ inA%) ninΓ)
grd-ε-rev (ε-∀ inA%) ninΓ inΓ (grd-∀ apA) = ε-∀ (grd-ε-rev inA% (S∙ ninΓ) (S∙ inΓ) apA)

grd-¬ε : ¬ (k ε A)
      → k ¬εᵍ Γ
      → Γ ∋∙ k
      → Γ ≫ A ⇘ A%
      → k ε A%
      → ⊥
grd-¬ε ninA ninΓ inΓ apA inA% = ninA (grd-ε-rev inA% ninΓ inΓ apA)
