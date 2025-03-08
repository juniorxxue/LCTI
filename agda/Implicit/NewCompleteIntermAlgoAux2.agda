module Implicit.NewCompleteIntermAlgoAux2 where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm.Base

open import Implicit.NewCompleteIntermAlgoAux

infix 3 _⊆_w/t_w/c_
data _⊆_w/t_w/c_ : Env n m → Env n m → Type m → Counter → Set where
  ⊆Z : (regΓ : SRegular Γ)
     → Γ ⊆ Γ w/t A w/c Z
  ⊆∞ : (ext : Γ ⊆ Δ w/t A)
     → Γ ⊆ Δ w/t A w/c ∞
  ⊆I : (ext : Γ ⊆ Ω w/t A)
     → Ω ⊆ Δ w/t B w/c j
     → Γ ⊆ Δ w/t (A `→ B) w/c (𝕚 j)
  ⊆C : (Γ ⊢c A)
     → Γ ⊆ Δ w/t B w/c j
     → Γ ⊆ Δ w/t (A `→ B) w/c (𝕔 j)
  ⊆∀-I : Γ ,∙ ⊆ Δ ,∙ w/t A w/c (𝕚 j)
     → Γ ⊆ Δ w/t `∀ A w/c (𝕚 j)
  ⊆∀-C : Γ ,∙ ⊆ Δ ,∙ w/t A w/c (𝕔 j)
     → Γ ⊆ Δ w/t `∀ A w/c (𝕔 j)
{-
-- a wf relation between j, Γ and A
infix 3 _⊢wf_#_
data _⊢wf_#_ : Env n m → Counter → Type m → Set where
  wf-Z : Γ ⊢ Z # A
  wf-∞ : Γ ⊢ ∞ # A
  wf-I : Γ ⊢ j # B
       → Γ ⊢ 𝕚 j # A `→ B
  wf-C : Γ ⊢ j # B
       → Γ ⊢ 𝕔 j # A `→ B
  wf-∀-𝕚 : Γ ⊢ j #
-}



⊆/c-⊆ : Γ ⊆ Δ w/t A w/c j
      → Γ ⊆ Δ
⊆/c-⊆ (⊆Z regΓ) = ⊆-refl regΓ
⊆/c-⊆ (⊆∞ x) = ⊆/-⊆ x
⊆/c-⊆ (⊆I ext ext₁) = ⊆-trans (⊆/-⊆ ext) (⊆/c-⊆ ext₁)
⊆/c-⊆ (⊆C x ext) = ⊆/c-⊆ ext
⊆/c-⊆ (⊆∀-I ext) with ⊆/c-⊆ ext
... | uvar r = r
⊆/c-⊆ (⊆∀-C ext) with ⊆/c-⊆ ext
... | uvar r = r

----------------------------------------------------------------------
--+                              inst                              +--
----------------------------------------------------------------------

⊆/x-^in-=out-inst : Γ ∋^ X
                → Δ ∋ X := A
                → Γ ⊆ Δ w/v X
                → [ A / X ] Γ ⟹ Δ
⊆/x-^in-=out-inst Z (Z up) (ext-Z^ regΓ regA) = ⟹^0 up regA regΓ
⊆/x-^in-=out-inst (S∙ inΓ) (S∙ inΔ up) (ext-S∙ ext) = ⟹∙S (⊆/x-^in-=out-inst inΓ inΔ ext) up
⊆/x-^in-=out-inst (S= inΓ) (S= inΔ up) (ext-S= ext regA) = ⟹=S (⊆/x-^in-=out-inst inΓ inΔ ext) up regA
⊆/x-^in-=out-inst (S^ inΓ) (S^ inΔ up) (ext-S^ ext) = ⟹^S (⊆/x-^in-=out-inst inΓ inΔ ext) up


----------------------------------------------------------------------
--+                     extension with counter                     +--
----------------------------------------------------------------------
{- seems doable, come back later, 03/08/25 2:41 PM
⊆/-=-∙ : Δ ,= B ⊆ Δ ,= B w/t A
       → Δ ,∙ ⊆ Δ ,∙ w/t A

⊆/c-=-∙ : Δ ,= B ⊆ Δ ,= B w/t A w/c j
        → find A #0 j
        → Δ ,∙ ⊆ Δ ,∙ w/t A w/c j
⊆/c-=-∙ (⊆Z (reg-S= regΓ regA)) (f-∀ fd) = ⊆Z (reg-S∙ regΓ)
⊆/c-=-∙ (⊆∞ x) fd = ⊆∞ {!!}
⊆/c-=-∙ (⊆I ext ext₁) (f-arr-𝕚-l x) = ⊆I {!!} {!!}
⊆/c-=-∙ (⊆I ext ext₁) (f-arr-𝕚-r fd) = ⊆I {!!} {!!}
⊆/c-=-∙ (⊆C x ext) (f-arr-𝕔 ¬inA fd) = ⊆C {!!} (⊆/c-=-∙ ext fd)
⊆/c-=-∙ (⊆∀-I ext) (f-∀ fd) = ⊆∀-I {!!}
⊆/c-=-∙ (⊆∀-C ext) (f-∀ fd) = ⊆∀-C {!!}
-}

⊆/x-⊢c : SRegular Γ
       → Γ ⊢c ‶ X
       → Γ ⊆ Γ w/v X
⊆/x-⊢c (reg-Z regΓ) (⊢c-var-∙ inΔ) = ext-mark regΓ
⊆/x-⊢c (reg-S∙ regΓ) (⊢c-var-∙ Z) = ext-Z∙ regΓ
⊆/x-⊢c (reg-S∙ regΓ) (⊢c-var-∙ (S∙ inΔ)) = ext-S∙ (⊆/x-⊢c regΓ (⊢c-var-∙ inΔ))
⊆/x-⊢c (reg-S^ regΓ) (⊢c-var-∙ (S^ inΔ)) = ext-S^ (⊆/x-⊢c regΓ (⊢c-var-∙ inΔ))
⊆/x-⊢c (reg-S= regΓ regA) (⊢c-var-∙ (S= inΔ)) = ext-S= (⊆/x-⊢c regΓ (⊢c-var-∙ inΔ)) regA
⊆/x-⊢c (reg-S∙ regΓ) (⊢c-var-= (S∙ inΔ)) = ext-S∙ (⊆/x-⊢c regΓ (⊢c-var-= inΔ))
⊆/x-⊢c (reg-S^ regΓ) (⊢c-var-= (S^ inΔ)) = ext-S^ (⊆/x-⊢c regΓ (⊢c-var-= inΔ))
⊆/x-⊢c (reg-S= regΓ regA) (⊢c-var-= Z) = ext-Z= regΓ regA
⊆/x-⊢c (reg-S= regΓ regA) (⊢c-var-= (S= inΔ)) = ext-S= (⊆/x-⊢c regΓ (⊢c-var-= inΔ)) regA

⊆/c-⊢c : SRegular Γ
       → Γ ⊢c A
       → Γ ⊆ Γ w/t A
⊆/c-⊢c regΓ ⊢c-int = ext-int regΓ
⊆/c-⊢c regΓ (⊢c-var-∙ inΔ) = ext-var (⊆/x-⊢c regΓ (⊢c-var-∙ inΔ))
⊆/c-⊢c regΓ (⊢c-var-= inΔ) = ext-var (⊆/x-⊢c regΓ (⊢c-var-= inΔ))
⊆/c-⊢c regΓ (⊢c-arr cloA cloA₁) = ext-arr (⊆/c-⊢c regΓ cloA) (⊆/c-⊢c regΓ cloA₁)
⊆/c-⊢c regΓ (⊢c-∀ cloA) = ext-∀ (⊆/c-⊢c (reg-S∙ regΓ) cloA)


⊆/c-∙-^=-gen : Γ ⊆ Δ w/t A w/c j
             → find A k j
             → Γ ◈ k ⇘ Γ'
             → [ B / k ] Δ ∙⟹ Δ'
             → Γ' ⊆ Δ' w/t A w/c j
⊆/c-∙-^=-gen (⊆Z regΓ) fd newΓ newΔ = ⊥-elim {!!}
⊆/c-∙-^=-gen (⊆∞ ext) fd newΓ newΔ = ⊆∞ {!!}
⊆/c-∙-^=-gen (⊆I ext ext₁) (f-arr-𝕚-l x) newΓ newΔ = ⊆I {!!} {!!}
⊆/c-∙-^=-gen (⊆I ext ext₁) (f-arr-𝕚-r fd) newΓ newΔ = ⊆I {!!} {!!}
⊆/c-∙-^=-gen (⊆C x ext) fd newΓ newΔ = {!!}
⊆/c-∙-^=-gen (⊆∀-I ext) fd newΓ newΔ = {!!}
⊆/c-∙-^=-gen (⊆∀-C ext) fd newΓ newΔ = {!!}


⊆/c-∙-^= : Γ ,∙ ⊆ Δ ,∙ w/t A w/c j
         → find A #0 j
         → Γ ,^ ⊆ Δ ,= B w/t A w/c j
⊆/c-∙-^= {B = B} ext fd = ⊆/c-∙-^=-gen ext fd ◈Z (∙⟹^0 (proj₂ (↑ty0-total B)))
