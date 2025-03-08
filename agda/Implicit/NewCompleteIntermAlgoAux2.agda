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
  ⊆∀-I : Γ ,^ ⊆ Δ ,= B w/t A w/c (𝕚 j)
     → Γ ⊆ Δ w/t `∀ A w/c (𝕚 j)
  ⊆∀-C : Γ ,^ ⊆ Δ ,= B w/t A w/c (𝕔 j)
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
... | evar-sol r regA = r
⊆/c-⊆ (⊆∀-C ext) with ⊆/c-⊆ ext
... | evar-sol r regA = r

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

postulate
  ⊆/c-∙-^=-gen : Γ ⊆ Δ w/t A w/c j
             → find A k j
             → Γ ◈ k ⇘ Γ'
             → [ B / k ] Δ ∙⟹ Δ'
             → Γ' ⊆ Δ' w/t A w/c j
{-
⊆/c-∙-^=-gen (⊆Z regΓ) fd newΓ newΔ = ⊥-elim {!!}
⊆/c-∙-^=-gen (⊆∞ ext) fd newΓ newΔ = ⊆∞ {!!}
⊆/c-∙-^=-gen (⊆I ext ext₁) (f-arr-𝕚-l x) newΓ newΔ = ⊆I {!!} {!!}
⊆/c-∙-^=-gen (⊆I ext ext₁) (f-arr-𝕚-r fd) newΓ newΔ = ⊆I {!!} {!!}
⊆/c-∙-^=-gen (⊆C x ext) fd newΓ newΔ = {!!}
⊆/c-∙-^=-gen (⊆∀-I ext) fd newΓ newΔ = {!!}
⊆/c-∙-^=-gen (⊆∀-C ext) fd newΓ newΔ = {!!}
-}

⊆/c-∙-^= : Γ ,∙ ⊆ Δ ,∙ w/t A w/c j
         → find A #0 j
         → Γ ,^ ⊆ Δ ,= B w/t A w/c j
⊆/c-∙-^= {B = B} ext fd = ⊆/c-∙-^=-gen ext fd ◈Z (∙⟹^0 (proj₂ (↑ty0-total B)))


⊆/c-=-irrev-gen : Γ ⊆ Δ w/t A w/c j
                → Γ ∋^ k
                → [ B / k ] Δ =⟹ Δ'
                → Γ ⊆ Δ' w/t A w/c j
⊆/c-=-irrev-gen (⊆Z regΓ) inΓ newΔ = ⊥-elim {!!}
⊆/c-=-irrev-gen (⊆∞ ext) inΓ newΔ = ⊆∞ {!!}
⊆/c-=-irrev-gen (⊆I ext ext₁) inΓ newΔ = ⊆I {!!} {!!}
⊆/c-=-irrev-gen (⊆C x ext) inΓ newΔ = ⊆C x (⊆/c-=-irrev-gen ext inΓ newΔ)
⊆/c-=-irrev-gen {B = B} (⊆∀-I ext) inΓ newΔ = ⊆∀-I (⊆/c-=-irrev-gen ext (S^ inΓ) (=⟹=S newΔ (proj₂ (↑ty0-total B))))
⊆/c-=-irrev-gen {B = B} (⊆∀-C ext) inΓ newΔ = ⊆∀-C (⊆/c-=-irrev-gen ext (S^ inΓ) (=⟹=S newΔ (proj₂ (↑ty0-total B))))

⊆/c-=-irrev : Γ ,^ ⊆ Δ ,= B₁ w/t A w/c j
            → Γ ,^ ⊆ Δ ,= B₂ w/t A w/c j
⊆/c-=-irrev {B₂ = B₂} ext = ⊆/c-=-irrev-gen ext Z (=⟹^0 (proj₂ (↑ty0-total B₂)))

⊆/c-=-irrev-gen-gen : Γ ⊆ Δ w/t A w/c j
                    → [ B / k ] Δ =⟹ Δ'
                    → Γ ⊆ Δ' w/t A w/c j
⊆/c-=-irrev-gen-gen (⊆Z regΓ) newΔ = {!!}
⊆/c-=-irrev-gen-gen (⊆∞ ext) newΔ = {!!}
⊆/c-=-irrev-gen-gen (⊆I ext ext₁) newΔ = ⊆I ext (⊆/c-=-irrev-gen-gen ext₁ newΔ)
⊆/c-=-irrev-gen-gen (⊆C x ext) newΔ = ⊆C x (⊆/c-=-irrev-gen-gen ext newΔ)
⊆/c-=-irrev-gen-gen {B = B} (⊆∀-I ext) newΔ = ⊆∀-I (⊆/c-=-irrev-gen-gen ext (=⟹=S newΔ (proj₂ (↑ty0-total B))))
⊆/c-=-irrev-gen-gen {B = B} (⊆∀-C ext) newΔ = ⊆∀-C (⊆/c-=-irrev-gen-gen ext (=⟹=S newΔ (proj₂ (↑ty0-total B))))

----------------------------------------------------------------------
--+                           new logic                            +--
----------------------------------------------------------------------

⊆/c-=-irrev-fd-gen' : Γ ⊆ Δ w/t A w/c j
                    → [ B / k ] Γ =⟹ Γ'
                    → [ B / k ] Δ =⟹ Δ'
                    → Γ' ⊆ Δ' w/t A w/c j
⊆/c-=-irrev-fd-gen' (⊆Z regΓ) newΓ newΔ = {!!}
⊆/c-=-irrev-fd-gen' (⊆∞ ext) newΓ newΔ = {!!}
⊆/c-=-irrev-fd-gen' (⊆I ext ext₁) newΓ newΔ = {!!}
⊆/c-=-irrev-fd-gen' (⊆C x ext) newΓ newΔ = {!!}
⊆/c-=-irrev-fd-gen' (⊆∀-I ext) newΓ newΔ = {!!}
⊆/c-=-irrev-fd-gen' (⊆∀-C ext) newΓ newΔ = {!!}

⊆/c-=-irrev-fd-gen-s : Γ ⊆ Δ w/t A
                   → Γ ∋^ k
                   → [ B / k ] Δ =⟹ Δ'
                   → k ε A
                   → Γ ⊆ Δ' w/t A

⊆/c-=-irrev-fd-gen : Γ ⊆ Δ w/t A w/c j
                   → Γ ∋^ k
                   → [ B / k ] Δ =⟹ Δ'
                   → find A k j
                   → Γ ⊆ Δ' w/t A w/c j
⊆/c-=-irrev-fd-gen (⊆Z regΓ) inΓ newΔ fd = ⊥-elim {!!}
⊆/c-=-irrev-fd-gen (⊆∞ ext) inΓ newΔ fd = ⊆∞ {!!}
⊆/c-=-irrev-fd-gen (⊆I ext ext₁) inΓ newΔ (f-arr-𝕚-l x) =
  ⊆I (⊆/c-=-irrev-fd-gen-s ext inΓ {!!} x) (⊆/c-=-irrev-fd-gen' ext₁ {!!} newΔ)
⊆/c-=-irrev-fd-gen (⊆I ext ext₁) inΓ newΔ (f-arr-𝕚-r fd) =
  ⊆I {!!} {!!}
⊆/c-=-irrev-fd-gen (⊆C x ext) inΓ newΔ (f-arr-𝕔 ¬inA fd) = ⊆C x (⊆/c-=-irrev-fd-gen ext inΓ newΔ fd)
⊆/c-=-irrev-fd-gen {B = B} (⊆∀-I ext) inΓ newΔ (f-∀ fd) =
  ⊆∀-I (⊆/c-=-irrev-fd-gen ext (S^ inΓ) (=⟹=S newΔ (proj₂ (↑ty0-total B))) fd)
⊆/c-=-irrev-fd-gen {B = B} (⊆∀-C ext) inΓ newΔ (f-∀ fd) =
  ⊆∀-C (⊆/c-=-irrev-fd-gen ext (S^ inΓ) (=⟹=S newΔ (proj₂ (↑ty0-total B))) fd)
