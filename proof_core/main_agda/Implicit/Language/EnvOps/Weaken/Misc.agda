module Implicit.Language.EnvOps.Weaken.Misc where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Regular.All
open import Implicit.Language.Lookup.All

open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Ground.Base

open import Implicit.Language.EnvOps.Weaken.Base
open import Implicit.Language.EnvOps.Weaken.Lookup

⊢r-weaken : Γ ⊢r A
            → Γ ▶ k ⇘ Γ' w/ mA
            → A ↑ty k ⇘ A'
            → Γ' ⊢r A'
⊢r-weaken ⊢r-int newΓ ↑ty-int = ⊢r-int
⊢r-weaken (⊢r-var-∙ inΓ) newΓ ↑ty-var = ⊢r-var-∙ (∋∙-weaken inΓ newΓ)
⊢r-weaken (⊢r-arr regA regA₁) newΓ (↑ty-arr upA upA₁) = ⊢r-arr (⊢r-weaken regA newΓ upA) (⊢r-weaken regA₁ newΓ upA₁)
⊢r-weaken {mA = mA} (⊢r-∀ regA) newΓ (↑ty-∀ upA) = ⊢r-∀ (⊢r-weaken regA (▶S∙ newΓ (proj₂ (↑tyᵐ0-total mA))) upA)

⊢r-weaken=0 : Γ ⊢r A
            → ↑ty0 A ⇘ A'
            → Γ ⊢r T
            → Γ ,= T ⊢r A'
⊢r-weaken=0 regA upA regT = ⊢r-weaken regA (▶Z= regT) upA

⊢r-weaken∙0 : Γ ⊢r A
              → ↑ty0 A ⇘ A'
              → Γ ,∙ ⊢r A'
⊢r-weaken∙0 regA upA = ⊢r-weaken regA ▶Z∙ upA

⊢r-weaken⋈0 : Γ ⊢r A
            → Γ ⋈ ⊢r A
⊢r-weaken⋈0 regA = ⊢r-𝕣 regA ↳⋈

⊢r-weaken^0 : Γ ⊢r A
             → ↑ty0 A ⇘ A'
             → Γ ,^ ⊢r A'
⊢r-weaken^0 regA up = ⊢r-weaken regA ▶Z^ up

⊢c-weaken : Γ ⊢c A
            → Γ ▶ k ⇘ Γ' w/ mA
            → A ↑ty k ⇘ A'
            → Γ' ⊢c A'
⊢c-weaken ⊢c-int newΓ ↑ty-int = ⊢c-int
⊢c-weaken (⊢c-var-∙ inΔ) newΓ ↑ty-var = ⊢c-var-∙ (∋∙-weaken inΔ newΓ)
⊢c-weaken (⊢c-var-= inΔ) newΓ ↑ty-var = ⊢c-var-= (∋=-weaken inΔ newΓ)
⊢c-weaken (⊢c-arr cloA cloA₁) newΓ (↑ty-arr upA upA₁) = ⊢c-arr (⊢c-weaken cloA newΓ upA) (⊢c-weaken cloA₁ newΓ upA₁)
⊢c-weaken {mA = mA} (⊢c-∀ cloA) newΓ (↑ty-∀ upA) = ⊢c-∀ (⊢c-weaken cloA (▶S∙ newΓ (proj₂ (↑tyᵐ0-total mA))) upA)

⊢o-weaken : Γ ⊢o A
            → Γ ▶ k ⇘ Γ' w/ mA
            → A ↑ty k ⇘ A'
            → Γ' ⊢o A'
⊢o-weaken (⊢o-var-^ x) new ↑ty-var = ⊢o-var-^ (∋^-weaken x new)
⊢o-weaken (⊢o-arr-l opnA) new (↑ty-arr upA upA₁) = ⊢o-arr-l (⊢o-weaken opnA new upA)
⊢o-weaken (⊢o-arr-r opnA) new (↑ty-arr upA upA₁) = ⊢o-arr-r (⊢o-weaken opnA new upA₁)
⊢o-weaken {mA = mA} (⊢o-∀ opnA) new (↑ty-∀ upA) = ⊢o-∀ (⊢o-weaken opnA (▶S∙ new (proj₂ (↑tyᵐ0-total mA))) upA)

≫-weaken : Γ ≫ A ⇘ B
          → Γ ▶ k ⇘ Γ' w/ mA
          → A ↑ty k ⇘ A'
          → B ↑ty k ⇘ B'
          → Γ' ≫ A' ⇘ B'
≫-weaken grd-int newΓ ↑ty-int ↑ty-int = grd-int
≫-weaken (grd-var= x) newΓ ↑ty-var upB = grd-var= (∋:=-weaken x upB newΓ)
≫-weaken (grd-var∙ x) newΓ ↑ty-var ↑ty-var = grd-var∙ (∋∙-weaken x newΓ)
≫-weaken (grd-arr grd grd₁) newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = grd-arr (≫-weaken grd newΓ upA upB)
                                                                                  (≫-weaken grd₁ newΓ upA₁ upB₁)
≫-weaken {mA = mA} (grd-∀ grd) newΓ (↑ty-∀ upA) (↑ty-∀ upB) = grd-∀ (≫-weaken grd (▶S∙ newΓ (proj₂ (↑tyᵐ0-total mA))) upA upB)

tregular-weaken : TRegular Γ
                → Γ ▶ k ⇘ Γ' w/ mA
                → TRegular Γ'
tregular-weaken reg-Z ▶Z^ = reg-S^ reg-Z
tregular-weaken reg-Z ▶Z∙ = reg-S∙ reg-Z
tregular-weaken reg-Z (▶Z= regA) = reg-S= reg-Z regA
tregular-weaken (reg-S, treg regA) ▶Z^ = reg-S^ (reg-S, treg regA)
tregular-weaken (reg-S, treg regA) ▶Z∙ = reg-S∙ (reg-S, treg regA)
tregular-weaken (reg-S, treg regA) (▶Z= regA₁) = reg-S= (reg-S, treg regA) regA₁
tregular-weaken (reg-S, treg regA) (▶S, new up) = reg-S, (tregular-weaken treg new) (⊢r-weaken regA new up)
tregular-weaken (reg-S∙ treg) ▶Z^ = reg-S^ (reg-S∙ treg)
tregular-weaken (reg-S∙ treg) ▶Z∙ = reg-S∙ (reg-S∙ treg)
tregular-weaken (reg-S∙ treg) (▶Z= regA) = reg-S= (reg-S∙ treg) regA
tregular-weaken (reg-S∙ treg) (▶S∙ new upmA) = reg-S∙ (tregular-weaken treg new)
tregular-weaken (reg-S^ treg) ▶Z^ = reg-S^ (reg-S^ treg)
tregular-weaken (reg-S^ treg) ▶Z∙ = reg-S∙ (reg-S^ treg)
tregular-weaken (reg-S^ treg) (▶Z= regA) = reg-S= (reg-S^ treg) regA
tregular-weaken (reg-S^ treg) (▶S^ new upmA) = reg-S^ (tregular-weaken treg new)
tregular-weaken (reg-S= treg regA) ▶Z^ = reg-S^ (reg-S= treg regA)
tregular-weaken (reg-S= treg regA) ▶Z∙ = reg-S∙ (reg-S= treg regA)
tregular-weaken (reg-S= treg regA) (▶Z= regA₁) = reg-S= (reg-S= treg regA) regA₁
tregular-weaken (reg-S= treg regA) (▶S= new upmA upB) = reg-S= (tregular-weaken treg new) (⊢r-weaken regA new upB)

sregular-weaken : SRegular Γ
                 → Γ ▶ k ⇘ Γ' w/ mA
                 → SRegular Γ'
sregular-weaken (reg-Z regΓ) ▶Z^ = reg-S^ (reg-Z regΓ)
sregular-weaken (reg-Z regΓ) ▶Z∙ = reg-S∙ (reg-Z regΓ)
sregular-weaken (reg-Z regΓ) (▶Z= regA) = reg-S= (reg-Z regΓ) regA
sregular-weaken (reg-Z regΓ) (▶S⋈ new) = reg-Z (tregular-weaken regΓ new)
sregular-weaken (reg-S∙ sreg) ▶Z^ = reg-S^ (reg-S∙ sreg)
sregular-weaken (reg-S∙ sreg) ▶Z∙ = reg-S∙ (reg-S∙ sreg)
sregular-weaken (reg-S∙ sreg) (▶Z= regA) = reg-S= (reg-S∙ sreg) regA
sregular-weaken (reg-S∙ sreg) (▶S∙ new upmA) = reg-S∙ (sregular-weaken sreg new)
sregular-weaken (reg-S^ sreg) ▶Z^ = reg-S^ (reg-S^ sreg)
sregular-weaken (reg-S^ sreg) ▶Z∙ = reg-S∙ (reg-S^ sreg)
sregular-weaken (reg-S^ sreg) (▶Z= regA) = reg-S= (reg-S^ sreg) regA
sregular-weaken (reg-S^ sreg) (▶S^ new upmA) = reg-S^ (sregular-weaken sreg new)
sregular-weaken (reg-S= sreg regA) ▶Z^ = reg-S^ (reg-S= sreg regA)
sregular-weaken (reg-S= sreg regA) ▶Z∙ = reg-S∙ (reg-S= sreg regA)
sregular-weaken (reg-S= sreg regA) (▶Z= regA₁) = reg-S= (reg-S= sreg regA) regA₁
sregular-weaken (reg-S= sreg regA) (▶S= new upmA upB) = reg-S= (sregular-weaken sreg new) (⊢r-weaken regA new upB)
