module Implicit.Language.EnvOps.Strengthen.Misc where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Occur.All

open import Implicit.Language.Regular.Base
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Ground.Base

open import Implicit.Language.EnvOps.Strengthen.Base
open import Implicit.Language.EnvOps.Strengthen.Lookup


⊢r-strengthen : Γ ⊢r A'
               → Γ ◀ k ⇘ Γ'
               → A ↑ty k ⇘ A'
               → Γ' ⊢r A
⊢r-strengthen ⊢r-int new ↑ty-int = ⊢r-int
⊢r-strengthen (⊢r-var-∙ inΓ) new ↑ty-var = ⊢r-var-∙ (∋∙-strengthen inΓ new)
⊢r-strengthen (⊢r-arr regA regA₁) new (↑ty-arr upA upA₁) = ⊢r-arr (⊢r-strengthen regA new upA) (⊢r-strengthen regA₁ new upA₁)
⊢r-strengthen (⊢r-∀ regA) new (↑ty-∀ upA) = ⊢r-∀ (⊢r-strengthen regA (◀S∙ new) upA)


⊢c-strengthen : Γ ⊢c A'
               → Γ ◀ k ⇘ Γ'
               → A ↑ty k ⇘ A'
               → Γ' ⊢c A
⊢c-strengthen ⊢c-int new ↑ty-int = ⊢c-int
⊢c-strengthen (⊢c-var-∙ inΔ) new ↑ty-var = ⊢c-var-∙ (∋∙-strengthen inΔ new)
⊢c-strengthen (⊢c-var-= inΔ) new ↑ty-var = ⊢c-var-= (∋=-strengthen inΔ new)
⊢c-strengthen (⊢c-arr cloA cloA₁) new (↑ty-arr upA upA₁) = ⊢c-arr (⊢c-strengthen cloA new upA) (⊢c-strengthen cloA₁ new upA₁)
⊢c-strengthen (⊢c-∀ cloA) new (↑ty-∀ upA) = ⊢c-∀ (⊢c-strengthen cloA (◀S∙ new) upA)


⊢o-strengthen : Γ ⊢o A'
               → Γ ◀ k ⇘ Γ'
               → A ↑ty k ⇘ A'
               → Γ' ⊢o A
⊢o-strengthen (⊢o-var-^ x) new ↑ty-var = ⊢o-var-^ (∋^-strengthen x new)
⊢o-strengthen (⊢o-arr-l opnA) new (↑ty-arr upA upA₁) = ⊢o-arr-l (⊢o-strengthen opnA new upA)
⊢o-strengthen (⊢o-arr-r opnA) new (↑ty-arr upA upA₁) = ⊢o-arr-r (⊢o-strengthen opnA new upA₁)
⊢o-strengthen (⊢o-∀ opnA) new (↑ty-∀ upA) = ⊢o-∀ (⊢o-strengthen opnA (◀S∙ new) upA)


tregular-strengthen : TRegular Γ
                     → Γ ◀ k ⇘ Γ'
                     → TRegular Γ'
tregular-strengthen (reg-S, regΓ regA) (◀S, new up) = reg-S, (tregular-strengthen regΓ new) (⊢r-strengthen regA new up)
tregular-strengthen (reg-S∙ regΓ) ◀Z∙ = regΓ
tregular-strengthen (reg-S∙ regΓ) (◀S∙ new) = reg-S∙ (tregular-strengthen regΓ new)
tregular-strengthen (reg-S^ regΓ) ◀Z^ = regΓ
tregular-strengthen (reg-S^ regΓ) (◀S^ new) = reg-S^ (tregular-strengthen regΓ new)
tregular-strengthen (reg-S= regΓ regA) ◀Z= = regΓ
tregular-strengthen (reg-S= regΓ regA) (◀S= new x) = reg-S= (tregular-strengthen regΓ new) (⊢r-strengthen regA new x)

sregular-strengthen : SRegular Γ
                     → Γ ◀ k ⇘ Γ'
                     → SRegular Γ'
sregular-strengthen (reg-Z regΓ) (◀S⋈ new) = reg-Z (tregular-strengthen regΓ new)
sregular-strengthen (reg-S∙ regΓ) ◀Z∙ = regΓ
sregular-strengthen (reg-S∙ regΓ) (◀S∙ new) = reg-S∙ (sregular-strengthen regΓ new)
sregular-strengthen (reg-S^ regΓ) ◀Z^ = regΓ
sregular-strengthen (reg-S^ regΓ) (◀S^ new) = reg-S^ (sregular-strengthen regΓ new)
sregular-strengthen (reg-S= regΓ regA) ◀Z= = regΓ
sregular-strengthen (reg-S= regΓ regA) (◀S= new x) = reg-S= (sregular-strengthen regΓ new) (⊢r-strengthen regA new x)


≫-strengthen : Γ ≫ A' ⇘ B'
              → k ¬εᵍ Γ
              → Γ ◀ k ⇘ Γ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → Γ' ≫ A ⇘ B
≫-strengthen grd-int ninΓ new ↑ty-int ↑ty-int = grd-int
≫-strengthen (grd-var= x) ninΓ new ↑ty-var upB = grd-var= (∋:=-strengthen x ninΓ new upB)
≫-strengthen (grd-var∙ x) ninΓ new (↑ty-var  {X = X} {k = k}) upB with ↑ty-var-inv-helper upB refl
... | refl = grd-var∙ (∋∙-strengthen x new)
≫-strengthen (grd-arr grd grd₁) ninΓ new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  = grd-arr (≫-strengthen grd ninΓ new upA upB) (≫-strengthen grd₁ ninΓ new upA₁ upB₁)
≫-strengthen (grd-∀ grd) ninΓ new (↑ty-∀ upA) (↑ty-∀ upB) = grd-∀ (≫-strengthen grd (S∙ ninΓ) (◀S∙ new) upA upB)


≫-strengthen=0 : Γ ,= T ≫ A' ⇘ B'
               → Γ ⊢r T
               → ↑ty0 A ⇘ A'
               → ↑ty0 B ⇘ B'
               → Γ ≫ A ⇘ B
≫-strengthen=0 {T = T} grd regT upA upB
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ≫-strengthen grd (Z= upT (↑ty-¬ε upT)) ◀Z= upA upB

{-
inst-strengthen= : [ B' / punchIn k X ] Γ ⟹ Δ
                 → Γ ◀ k =⇘ Γ'
                 → Δ ◀ k =⇘ Δ'
                 → B ↑ty k ⇘ B'
                 → [ B / X ] Γ' ⟹ Δ'
inst-strengthen= {k = #0} {#0} (⟹=S inst up1 regB) ◀Z ◀Z upB
  with refl ← ↑ty-unique-inver up1 upB = inst
inst-strengthen= {k = #0} {#S X} (⟹=S inst up1 regB) ◀Z ◀Z upB
  with refl ← ↑ty-unique-inver up1 upB = inst
inst-strengthen= {k = #S k} {#0} (⟹^0 up regA env) (◀S^ newΓ) (◀S= newΔ x) upB
  with refl ← ◀=-unique newΓ newΔ = ⟹^0 (↑ty-comm1 upB up x) (⊢r-strengthen= regA newΓ x) (sregular-strengthen= env newΓ)
inst-strengthen= {k = #S k} {#S X} (⟹^S inst up1) (◀S^ newΓ) (◀S^ newΔ) upB
  with regA ← inst-⊢r inst
  with ⟨ preA , uppA ⟩ ← ⊢r-◀=-↑ty-surjective regA newΓ = ⟹^S (inst-strengthen= inst newΓ newΔ uppA) (↑ty-comm1 upB up1 uppA)
inst-strengthen= {k = #S k} {#S X} (⟹∙S inst up1) (◀S∙ newΓ) (◀S∙ newΔ) upB
  with regA ← inst-⊢r inst
  with ⟨ preA , uppA ⟩ ← ⊢r-◀=-↑ty-surjective regA newΓ = ⟹∙S (inst-strengthen= inst newΓ newΔ uppA) (↑ty-comm1 upB up1 uppA)
inst-strengthen= {k = #S k} {#S X} (⟹=S inst up1 regB) (◀S= newΓ x) (◀S= newΔ x₁) upB
  with refl ← ↑ty-unique-inver x x₁
  with regA ← inst-⊢r inst
  with ⟨ preA , uppA ⟩ ← ⊢r-◀=-↑ty-surjective regA newΓ = ⟹=S (inst-strengthen= inst newΓ newΔ uppA) (↑ty-comm1 upB up1 uppA) (⊢r-strengthen= regB newΓ x₁)
-}
