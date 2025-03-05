module Implicit.Algo.New.Extension where

open import Implicit.Language.All hiding (_⊆_)
open import Implicit.Algo.Base


postulate
  ⊆-∋∙ : Γ ∋∙ X
       → Γ ⊆ Δ
       → Δ ∋∙ X

  ⊆-∋= : Γ ∋=¹ X
       → Γ ⊆ Δ
       → Δ ∋=¹ X

⊆-closeA : Γ ⊢c A
         → Γ ⊆ Δ
         → Δ ⊢c A
⊆-closeA ⊢c-int ext = ⊢c-int
⊆-closeA (⊢c-var-∙ inΓ) ext = ⊢c-var-∙ (⊆-∋∙ inΓ ext)
⊆-closeA (⊢c-var-= inΓ) ext = ⊢c-var-= (⊆-∋= inΓ ext)
⊆-closeA (⊢c-arr cloA cloA₁) ext = ⊢c-arr (⊆-closeA cloA ext) (⊆-closeA cloA₁ ext)
⊆-closeA (⊢c-∀ cloA) ext = ⊢c-∀ (⊆-closeA cloA (uvar ext))

⊆-trans : Γ ⊆ Ω
        → Ω ⊆ Δ
        → Γ ⊆ Δ
⊆-trans (uvar ext1) (uvar ext2) = uvar (⊆-trans ext1 ext2)
⊆-trans (var ext1) (var ext2) = var (⊆-trans ext1 ext2)
⊆-trans (evar ext1) (evar ext2) = evar (⊆-trans ext1 ext2)
⊆-trans (evar ext1) (evar-sol ext2 cloA) = evar-sol (⊆-trans ext1 ext2) cloA
⊆-trans (evar-sol ext1 cloA) (svar ext2) = evar-sol (⊆-trans ext1 ext2) (⊆-closeA cloA ext2)
⊆-trans (svar ext1) (svar ext2) = svar (⊆-trans ext1 ext2)
⊆-trans (mark x) (mark x₁) = mark x

closed-env : TypClosed Γ
           → TypEnv Γ
closed-env clo-Z = Z⋈
closed-env (clo-S, cloΓ cloA) = S, (closed-env cloΓ)
closed-env (clo-S∙ cloΓ) = S∙ (closed-env cloΓ)
closed-env (clo-S^ cloΓ) = S^ (closed-env cloΓ)
closed-env (clo-S= cloΓ) = S= (closed-env cloΓ)

sclosed-senv : SubClosed Γ
             → SubEnv Γ
sclosed-senv (clo-Z x) = Z⋈ (closed-env x)
sclosed-senv (clo-S, cloΓ cloA) = S, (sclosed-senv cloΓ)
sclosed-senv (clo-S∙ cloΓ) = S∙ (sclosed-senv cloΓ)
sclosed-senv (clo-S^ cloΓ) = S^ (sclosed-senv cloΓ)
sclosed-senv (clo-S= cloΓ cloA) = S= (sclosed-senv cloΓ)

inst-⊆ : [ B / X ] Γ ⟹ Δ
       → Γ ⊆ Δ
inst-⊆ (⟹^0 up cloA env) = evar-sol (⊆-refl env) cloA
inst-⊆ (⟹^S inst up1) = evar (inst-⊆ inst)
inst-⊆ (⟹∙S inst up1) = uvar (inst-⊆ inst)
inst-⊆ (⟹,S inst) = var (inst-⊆ inst)
inst-⊆ (⟹=S inst up1) = svar (inst-⊆ inst)


postulate
  s-⊆ : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
      → Γ ⊆ Δ


  ss-⊆ : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
     → Γ ⊆ Δ

{-
s-⊆ (s-empty cloΓ cloA x) = ⊆-refl _
s-⊆ (s-type ss) = {!!}
s-⊆ (s-term-c cloA ap ⊢e s) = s-⊆ s
s-⊆ (s-term-o opnA ⊢e x s) = ⊆-trans (ss-⊆ x) (s-⊆ s)
s-⊆ (s-∀l s upᶜ upᵉ upC upD) with s-⊆ s
... | evar-sol r cloA = r
-}
