module Implicit.Language.EnvOps.Replace where

open import Implicit.Language.Base
open import Implicit.Language.Lookup
open import Implicit.Language.Shift
open import Implicit.Language.Subst
open import Implicit.Language.OpenClose.Base

-- in k position, we replace a ,= B with ,∙
infix 3 _◆_⇘_
data _◆_⇘_ : Env n m → Fin m → Env n m → Set where
  ◆Z : Γ ,= A ◆ #0 ⇘ Γ ,∙
  ◆S, : Γ ◆ k ⇘ Γ'
      → Γ , A ◆ k ⇘ Γ' , A
  ◆S∙ : Γ ◆ k ⇘ Γ'
      → Γ ,∙ ◆ #S k ⇘ Γ' ,∙
  ◆S= : Γ ◆ k ⇘ Γ'
      → Γ ,= A ◆ #S k ⇘ Γ' ,= A
  ◆S^ : Γ ◆ k ⇘ Γ'
      → Γ ,^ ◆ #S k ⇘ Γ' ,^

◆-∙∈ : Γ ∋∙ X
     → Γ ◆ k ⇘ Γ'
     → Γ' ∋∙ X
◆-∙∈ (S= inΓ) ◆Z = S∙ inΓ
◆-∙∈ (S, inΓ) (◆S, ◆Γ) = S, (◆-∙∈ inΓ ◆Γ)
◆-∙∈ Z (◆S∙ ◆Γ) = Z
◆-∙∈ (S∙ inΓ) (◆S∙ ◆Γ) = S∙ (◆-∙∈ inΓ ◆Γ)
◆-∙∈ (S= inΓ) (◆S= ◆Γ) = S= (◆-∙∈ inΓ ◆Γ)
◆-∙∈ (S^ inΓ) (◆S^ ◆Γ) = S^ (◆-∙∈ inΓ ◆Γ)


-- should this A exposed to the outside?
◆-=∈-≢ : Γ ∋= X
     → Γ ◆ k ⇘ Γ'
     → k ≢ X
     → Γ' ∋= X
◆-=∈-≢ Z ◆Z neq = ⊥-elim (neq refl)
◆-=∈-≢ Z (◆S= ◆Γ) neq = Z
◆-=∈-≢ (S, inΓ) (◆S, ◆Γ) neq = S, (◆-=∈-≢ inΓ ◆Γ neq)
◆-=∈-≢ (S^ inΓ) (◆S^ ◆Γ) neq = S^ (◆-=∈-≢ inΓ ◆Γ (≢-pred neq))
◆-=∈-≢ (S∙ inΓ) (◆S∙ ◆Γ) neq = S∙ (◆-=∈-≢ inΓ ◆Γ (≢-pred neq))
◆-=∈-≢ (S= inΓ) ◆Z neq = S∙ inΓ
◆-=∈-≢ (S= inΓ) (◆S= ◆Γ) neq = S= (◆-=∈-≢ inΓ ◆Γ (≢-pred neq))

◆-=∈-≡ : Γ ∋= k
     → Γ ◆ k ⇘ Γ'
     → Γ' ∋∙ k
◆-=∈-≡ Z ◆Z = Z
◆-=∈-≡ (S, inΓ) (◆S, ◆Γ) = S, (◆-=∈-≡ inΓ ◆Γ)
◆-=∈-≡ (S^ inΓ) (◆S^ ◆Γ) = S^ (◆-=∈-≡ inΓ ◆Γ)
◆-=∈-≡ (S∙ inΓ) (◆S∙ ◆Γ) = S∙ (◆-=∈-≡ inΓ ◆Γ)
◆-=∈-≡ (S= inΓ) (◆S= ◆Γ) = S= (◆-=∈-≡ inΓ ◆Γ)

⊢c-◆ : Γ ⊢c A
     → Γ ◆ k ⇘ Γ'
     → Γ' ⊢c A
⊢c-◆ ⊢c-int ◆Γ = ⊢c-int
⊢c-◆ (⊢c-var-∙ inΓ) ◆Γ = ⊢c-var-∙ (◆-∙∈ inΓ ◆Γ)
⊢c-◆ {k = k} (⊢c-var-= {X = X} inΓ) ◆Γ with k #≟ X
... | yes refl = ⊢c-var-∙ (◆-=∈-≡ inΓ ◆Γ)
... | no ¬p = ⊢c-var-= (◆-=∈-≢ inΓ ◆Γ ¬p)
⊢c-◆ (⊢c-arr clo clo₁) ◆Γ = ⊢c-arr (⊢c-◆ clo ◆Γ) (⊢c-◆ clo₁ ◆Γ)
⊢c-◆ (⊢c-∀ clo) ◆Γ = ⊢c-∀ (⊢c-◆ clo (◆S∙ ◆Γ))

⊢c-◆0 : Γ ,= B ⊢c A
      → Γ ,∙ ⊢c A
⊢c-◆0 clo = ⊢c-◆ clo ◆Z

----------------------------------------------------------------------
--+                   replace ,A by another type                   +--
----------------------------------------------------------------------

infix 3 _◈_⇘_
data _◈_⇘_ : Env n m → Fin n → Env n m → Set where
  ◈Z : Γ , A ◈ #0 ⇘ Γ , B
  ◈S, : Γ ◈ k ⇘ Γ'
      → Γ , A ◈ #S k ⇘ Γ' , A
  ◈S∙ : Γ ◈ k ⇘ Γ'
      → Γ ,∙ ◈ k ⇘ Γ' ,∙
  ◈S= : Γ ◈ k ⇘ Γ'
      → Γ ,= A ◈ k ⇘ Γ' ,= A
  ◈S^ : Γ ◈ k ⇘ Γ'
      → Γ ,^ ◈ k ⇘ Γ' ,^

postulate
  ⊢c-◈ : Γ ⊢c A
       → Γ ◈ k ⇘ Γ'
       → Γ' ⊢c A


⊢cᵉ-◈ : Γ ⊢cᵉ e
      → Γ ◈ k ⇘ Γ'
      → Γ' ⊢cᵉ e
⊢cᵉ-◈ ⊢c-lit newΓ = ⊢c-lit
⊢cᵉ-◈ ⊢c-var newΓ = ⊢c-var
⊢cᵉ-◈ (⊢c-lam cloe) newΓ = ⊢c-lam (⊢cᵉ-◈ cloe (◈S, newΓ))
⊢cᵉ-◈ (⊢c-app cloe cloe₁) newΓ = ⊢c-app (⊢cᵉ-◈ cloe newΓ) (⊢cᵉ-◈ cloe₁ newΓ)
⊢cᵉ-◈ (⊢c-ann cloA cloe) newΓ = ⊢c-ann (⊢c-◈ cloA newΓ) (⊢cᵉ-◈ cloe newΓ)
⊢cᵉ-◈ (⊢c-tlam cloe) newΓ = ⊢c-tlam (⊢cᵉ-◈ cloe (◈S∙ newΓ))

⊢cᵉ-◈0 : Γ , A ⊢cᵉ e
       → Γ , B ⊢cᵉ e
⊢cᵉ-◈0 clo = ⊢cᵉ-◈ clo ◈Z
