module Implicit.Language.EnvOps.RemoveTVar where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.Base
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Ground.Base

-- remove (x : A) from k-th position
infix 3 _◀_,⇘_
data _◀_,⇘_ : Env (1 + n) m → Fin (1 + n) → Env n m → Set where
  ◀Z : Γ , A ◀ #0 ,⇘ Γ
  ◀S, : Γ ◀ k ,⇘ Γ'
      → Γ , B ◀ #S k ,⇘ Γ' , B
  ◀S^ : Γ ◀ k ,⇘ Γ'
      → (Γ ,^) ◀ k ,⇘ Γ' ,^
  ◀S∙ : Γ ◀ k ,⇘ Γ'
      → (Γ ,∙) ◀ k ,⇘ Γ' ,∙
  ◀S= : Γ ◀ k ,⇘ Γ'
      → (Γ ,= A) ◀ k ,⇘ Γ' ,= A
  ◀S⋈ : Γ ◀ k ,⇘ Γ'
      → Γ ⋈ ◀ k ,⇘ Γ' ⋈

∋⦂-strengthen, : Γ ∋ punchIn k x ⦂ A
      → Γ ◀ k ,⇘ Γ'
      → Γ' ∋ x ⦂ A
∋⦂-strengthen, {k = #0} {#0} (S, inΓ) ◀Z = inΓ
∋⦂-strengthen, {k = #0} {#0} (S∙ inΓ up) (◀S∙ newΓ) = S∙ (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #0} {#0} (S^ inΓ up) (◀S^ newΓ) = S^ (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #0} {#0} (S= inΓ up) (◀S= newΓ) = S= (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #0} {#S x} (S, inΓ) ◀Z = inΓ
∋⦂-strengthen, {k = #0} {#S x} (S^ inΓ up) (◀S^ newΓ) = S^ (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #0} {#S x} (S∙ inΓ up) (◀S∙ newΓ) = S∙ (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #0} {#S x} (S= inΓ up) (◀S= newΓ) = S= (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #S k} {#0} Z (◀S, newΓ) = Z
∋⦂-strengthen, {k = #S k} {#0} (S∙ inΓ up) (◀S∙ newΓ) = S∙ (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #S k} {#0} (S^ inΓ up) (◀S^ newΓ) = S^ (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #S k} {#0} (S= inΓ up) (◀S= newΓ) = S= (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #S k} {#S x} (S, inΓ) (◀S, newΓ) = S, (∋⦂-strengthen, inΓ newΓ)
∋⦂-strengthen, {k = #S k} {#S x} (S∙ inΓ up) (◀S∙ newΓ) = S∙ (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #S k} {#S x} (S^ inΓ up) (◀S^ newΓ) = S^ (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #S k} {#S x} (S= inΓ up) (◀S= newΓ) = S= (∋⦂-strengthen, inΓ newΓ) up

∋:=-strengthen, : Γ ∋ X := A
       → Γ ◀ k ,⇘ Γ'
       → Γ' ∋ X := A
∋:=-strengthen, (Z up) (◀S= newΓ) = Z up
∋:=-strengthen, (S∙ inΓ up) (◀S∙ newΓ) = S∙ (∋:=-strengthen, inΓ newΓ) up
∋:=-strengthen, (S^ inΓ up) (◀S^ newΓ) = S^ (∋:=-strengthen, inΓ newΓ) up
∋:=-strengthen, (S= inΓ up) (◀S= newΓ) = S= (∋:=-strengthen, inΓ newΓ) up

∋∙-strengthen, : Γ ∋∙ X
      → Γ ◀ k ,⇘ Γ'
      → Γ' ∋∙ X
∋∙-strengthen, Z (◀S∙ newΓ') = Z
∋∙-strengthen, (S, inΓ) ◀Z = inΓ
∋∙-strengthen, (S, inΓ) (◀S, newΓ') = S, (∋∙-strengthen, inΓ newΓ')
∋∙-strengthen, (S∙ inΓ) (◀S∙ newΓ') = S∙ (∋∙-strengthen, inΓ newΓ')
∋∙-strengthen, (S= inΓ) (◀S= newΓ') = S= (∋∙-strengthen, inΓ newΓ')
∋∙-strengthen, (S^ inΓ) (◀S^ newΓ') = S^ (∋∙-strengthen, inΓ newΓ')
∋∙-strengthen, (S⋈ inΓ) (◀S⋈ newΓ') = S⋈ (∋∙-strengthen, inΓ newΓ')

∋^-strengthen, : Γ ∋^ X
               → Γ ◀ k ,⇘ Γ'
               → Γ' ∋^ X
∋^-strengthen, Z (◀S^ newΓ) = Z
∋^-strengthen, (S∙ inΓ) (◀S∙ newΓ) = S∙ (∋^-strengthen, inΓ newΓ)
∋^-strengthen, (S= inΓ) (◀S= newΓ) = S= (∋^-strengthen, inΓ newΓ)
∋^-strengthen, (S^ inΓ) (◀S^ newΓ) = S^ (∋^-strengthen, inΓ newΓ)

∋=-strengthen, : Γ ∋= X
       → Γ ◀ k ,⇘ Γ'
       → Γ' ∋= X
∋=-strengthen, Z (◀S= newΓ') = Z
∋=-strengthen, (S∙ inΓ) (◀S∙ newΓ') = S∙ (∋=-strengthen, inΓ newΓ')
∋=-strengthen, (S^ inΓ) (◀S^ newΓ') = S^ (∋=-strengthen, inΓ newΓ')
∋=-strengthen, (S= inΓ) (◀S= newΓ') = S= (∋=-strengthen, inΓ newΓ')

⊢r-strengthen, : Γ ⊢r A
               → Γ ◀ k ,⇘ Γ'
               → Γ' ⊢r A
⊢r-strengthen, ⊢r-int newΓ = ⊢r-int
⊢r-strengthen, (⊢r-var-∙ inΓ) newΓ = ⊢r-var-∙ (∋∙-strengthen, inΓ newΓ)
⊢r-strengthen, (⊢r-arr regA regA₁) newΓ = ⊢r-arr (⊢r-strengthen, regA newΓ) (⊢r-strengthen, regA₁ newΓ)
⊢r-strengthen, (⊢r-∀ regA) newΓ = ⊢r-∀ (⊢r-strengthen, regA (◀S∙ newΓ))


⊢r-strengthen,0 : Γ , A ⊢r B
                  → Γ ⊢r B
⊢r-strengthen,0 regA = ⊢r-strengthen, regA ◀Z

tregular-strengthen, : TRegular Γ
                     → Γ ◀ k ,⇘ Γ'
                     → TRegular Γ'
tregular-strengthen, (reg-S, regΓ regA) ◀Z = regΓ
tregular-strengthen, (reg-S, regΓ regA) (◀S, newΓ) = reg-S, (tregular-strengthen, regΓ newΓ) (⊢r-strengthen, regA newΓ)
tregular-strengthen, (reg-S∙ regΓ) (◀S∙ newΓ) = reg-S∙ (tregular-strengthen, regΓ newΓ)
tregular-strengthen, (reg-S^ regΓ) (◀S^ newΓ) = reg-S^ (tregular-strengthen, regΓ newΓ)
tregular-strengthen, (reg-S= regΓ regA) (◀S= newΓ) = reg-S= (tregular-strengthen, regΓ newΓ) (⊢r-strengthen, regA newΓ)

sregular-strengthen, : SRegular Γ
                     → Γ ◀ k ,⇘ Γ'
                     → SRegular Γ'
sregular-strengthen, (reg-Z regΓ) (◀S⋈ newΓ) = reg-Z (tregular-strengthen, regΓ newΓ)
sregular-strengthen, (reg-S∙ regΓ) (◀S∙ newΓ) = reg-S∙ (sregular-strengthen, regΓ newΓ)
sregular-strengthen, (reg-S^ regΓ) (◀S^ newΓ) = reg-S^ (sregular-strengthen, regΓ newΓ)
sregular-strengthen, (reg-S= regΓ regA) (◀S= newΓ) = reg-S= (sregular-strengthen, regΓ newΓ) (⊢r-strengthen, regA newΓ)

⊢c-strengthen, : Γ ⊢c A
               → Γ ◀ k ,⇘ Γ'
               → Γ' ⊢c A
⊢c-strengthen, ⊢c-int newΓ = ⊢c-int
⊢c-strengthen, (⊢c-var-∙ inΔ) newΓ = ⊢c-var-∙ (∋∙-strengthen, inΔ newΓ)
⊢c-strengthen, (⊢c-var-= inΔ) newΓ = ⊢c-var-= (∋=-strengthen, inΔ newΓ)
⊢c-strengthen, (⊢c-arr cloA cloA₁) newΓ = ⊢c-arr (⊢c-strengthen, cloA newΓ) (⊢c-strengthen, cloA₁ newΓ)
⊢c-strengthen, (⊢c-∀ cloA) newΓ = ⊢c-∀ (⊢c-strengthen, cloA (◀S∙ newΓ))

⊢o-strengthen, : Γ ⊢o A
               → Γ ◀ k ,⇘ Γ'
               → Γ' ⊢o A
⊢o-strengthen, (⊢o-var-^ x) newΓ = ⊢o-var-^ (∋^-strengthen, x newΓ)
⊢o-strengthen, (⊢o-arr-l opnA) newΓ = ⊢o-arr-l (⊢o-strengthen, opnA newΓ)
⊢o-strengthen, (⊢o-arr-r opnA) newΓ = ⊢o-arr-r (⊢o-strengthen, opnA newΓ)
⊢o-strengthen, (⊢o-∀ opnA) newΓ = ⊢o-∀ (⊢o-strengthen, opnA (◀S∙ newΓ))

≫-strengthen, : Γ ≫ A ⇘ B
              → Γ ◀ k ,⇘ Γ'
              → Γ' ≫ A ⇘ B
≫-strengthen, grd-int newΓ = grd-int
≫-strengthen, (grd-var= x) newΓ = grd-var= (∋:=-strengthen, x newΓ)
≫-strengthen, (grd-var∙ x) newΓ = grd-var∙ (∋∙-strengthen, x newΓ)
≫-strengthen, (grd-arr grdA grdA₁) newΓ = grd-arr (≫-strengthen, grdA newΓ) (≫-strengthen, grdA₁ newΓ)
≫-strengthen, (grd-∀ grdA) newΓ = grd-∀ (≫-strengthen, grdA (◀S∙ newΓ))
