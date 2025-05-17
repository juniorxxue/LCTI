module Implicit.Language.Ground.Find where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Occur.All
open import Implicit.Language.OpenClose.All
open import Implicit.Language.Norm.All
open import Implicit.Language.EnvOps.All
open import Implicit.Language.Find
open import Implicit.Language.Ground.Base
open import Implicit.Language.Ground.Properties
open import Implicit.Language.Ground.Occur

grd-find' : find A k j
         → Γ ∋∙ k
         → k ¬εᵍ Γ
         → Γ ≫ A ⇘ A%
         → find A% k j
grd-find' (f-∞ x) inΓ ninΓ apA = f-∞ (grd-ε x inΓ apA)
grd-find' (f-arr-𝕚-l x) inΓ ninΓ (grd-arr apA apA₁) = f-arr-𝕚-l (grd-ε x inΓ apA)
grd-find' (f-arr-𝕚-r fd) inΓ ninΓ (grd-arr apA apA₁) = f-arr-𝕚-r (grd-find' fd inΓ ninΓ apA₁)
grd-find' (f-arr-𝕔 ¬inA fd) inΓ ninΓ (grd-arr apA apA₁) = f-arr-𝕔 (grd-¬ε-prv apA ninΓ ¬inA) (grd-find' fd inΓ ninΓ apA₁)
grd-find' (f-∀ fd) inΓ ninΓ (grd-∀ apA) = f-∀ (grd-find' fd (S∙ inΓ) (S∙ ninΓ) apA)

grd-find0 : find A #0 j
          → Γ% ,∙ ≫ A ⇘ A% -- may need Norm Γ%
          → find A% #0 j
grd-find0 fd apA = grd-find' fd Z Z∙ apA
