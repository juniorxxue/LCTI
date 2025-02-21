module Implicit.Algo.Properties.NewExtension where

open import Implicit.Language.All
open import Implicit.Algo.Base

infix 3 _⊆_
data _⊆_ : Env n m → Env n m → Set where
  uvar :
      Γ ⊆ Δ
    → Γ ,∙ ⊆ Δ ,∙
  var :
      Γ ⊆ Δ
    → Γ , A ⊆ Δ , A
  evar :
      Γ ⊆ Δ
    → Γ ,^ ⊆ Δ ,^
  evar-sol :
      Γ ⊆ Δ
    → (cloA : Δ ⊢c A)
    → Γ ,^ ⊆ Δ ,= A
  svar :
      Γ ⊆ Δ
    → Γ ,= A ⊆ Δ ,= A
  mark : TypEnv Γ
       → Γ ⋈ ⊆ Γ ⋈

{-
⊆-refl : SubClosed Γ
       → Γ ⊆ Γ
⊆-refl (clo-Z x) = mark
⊆-refl (clo-S, cloΓ cloA) = var (⊆-refl cloΓ)
⊆-refl (clo-S∙ cloΓ) = uvar (⊆-refl cloΓ)
⊆-refl (clo-S^ cloΓ) = evar (⊆-refl cloΓ)
⊆-refl (clo-S= cloΓ cloA) = svar (⊆-refl cloΓ)
-}

⊆-refl : SubEnv Γ
       → Γ ⊆ Γ
⊆-refl (Z⋈ x) = mark x
⊆-refl (S, se) = var (⊆-refl se)
⊆-refl (S= se) = svar (⊆-refl se)
⊆-refl (S∙ se) = uvar (⊆-refl se)
⊆-refl (S^ se) = evar (⊆-refl se)



⊆-senv : Γ ⊆ Γ'
       → SubEnv Γ
⊆-senv (uvar ext) = S∙ (⊆-senv ext)
⊆-senv (var ext) = S, (⊆-senv ext)
⊆-senv (evar ext) = S^ (⊆-senv ext)
⊆-senv (evar-sol ext cloA) = S^ (⊆-senv ext)
⊆-senv (svar ext) = S= (⊆-senv ext)
⊆-senv (mark x) = Z⋈ x

postulate
  ⊆-∋∙ : Γ ∋∙ X
       → Γ ⊆ Δ
       → Δ ∋∙ X

  ⊆-∋= : Γ ∋= X
       → Γ ⊆ Δ
       → Δ ∋= X

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


inst-⊆ : [ B / X ] Γ ⟹ Δ
       → Γ ⊆ Δ
inst-⊆ (⟹^0 up cloA env) = evar-sol (⊆-refl env) cloA
inst-⊆ (⟹^S inst up1) = evar (inst-⊆ inst)
inst-⊆ (⟹∙S inst up1) = uvar (inst-⊆ inst)
inst-⊆ (⟹,S inst) = var (inst-⊆ inst)
inst-⊆ (⟹=S inst up1) = svar (inst-⊆ inst)

s-⊆ : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
    → Γ ⊆ Δ
s-⊆ (s-int cloΓ) = {!!}
s-⊆ (s-empty cloΓ clo) = {!!}
s-⊆ (s-var-∙ cloΓ x) = {!!}
s-⊆ (s-var-= cloΓ x) = {!!}
s-⊆ (s-ex-l^ x-in cloA inst) = inst-⊆ inst
s-⊆ (s-ex-l= x-in s) = s-⊆ s
s-⊆ (s-ex-typ-l= x-in s) = s-⊆ s
s-⊆ (s-ex-r^ x-in cloA inst) = inst-⊆ inst
s-⊆ (s-ex-r= x-in s) = s-⊆ s
s-⊆ (s-ex-typ-r= x-in s) = s-⊆ s
s-⊆ (s-arr s s₁) = ⊆-trans (s-⊆ s) (s-⊆ s₁)
s-⊆ (s-term-c ⊢e s) = s-⊆ s
s-⊆ (s-term-o opnA ⊢e s s₁) = ⊆-trans (s-⊆ s) (s-⊆ s₁)
s-⊆ (s-∀ s) with s-⊆ s
... | uvar r = r
s-⊆ (s-∀l s upᶜ upᵉ st₁ st₂) with s-⊆ s
... | evar-sol r cloA = r
