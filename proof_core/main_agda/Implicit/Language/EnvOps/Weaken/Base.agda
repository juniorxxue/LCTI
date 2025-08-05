module Implicit.Language.EnvOps.Weaken.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Regular.All

MType : ℕ → Set
MType m = Maybe (Type m)

variable
  mA mB mA₁ mB₁ mA₂ mB₂ mA' mB' : MType m

infix 3 ↑tyᵐ0_⇘_
data ↑tyᵐ0_⇘_ : MType m → MType (1 + m) → Set where
  ↑tyᵐ-nothing : ↑tyᵐ0 nothing ⇘ (MType (1 + m) ∋⦂ nothing)
  ↑tyᵐ-just : ↑ty0 A ⇘ A'
            → ↑tyᵐ0 (just A) ⇘ (just A')

↑tyᵐ0-total : ∀ (mA : MType m) → ∃[ mA' ](↑tyᵐ0 mA ⇘ mA')
↑tyᵐ0-total (just x) with ↑ty0-total x
... | ⟨ A' , upA ⟩ = ⟨ just A' , ↑tyᵐ-just upA ⟩
↑tyᵐ0-total nothing = ⟨ nothing , ↑tyᵐ-nothing ⟩

infix 3 _▶_⇘_w/_
data _▶_⇘_w/_ : Env n m → Fin (1 + m) → Env n (1 + m) → MType m → Set where
  ▶Z^ : Γ ▶ #0 ⇘ Γ ,^ w/ nothing
  ▶Z∙ : Γ ▶ #0 ⇘ Γ ,∙ w/ nothing
  ▶Z= : (regA : Γ ⊢r A)
      → Γ ▶ #0 ⇘ Γ ,= A w/ (just A)
  ▶S, : Γ ▶ k ⇘ Γ' w/ mA
      → (up : B ↑ty k ⇘ B')
      → Γ , B ▶ k ⇘ Γ' , B' w/ mA
  ▶S^ : Γ ▶ k ⇘ Γ' w/ mA
      → (upmA : ↑tyᵐ0 mA ⇘ mA')
      → Γ ,^ ▶ #S k ⇘ Γ' ,^ w/ mA'
  ▶S∙ : Γ ▶ k ⇘ Γ'  w/ mA
      → (upmA : ↑tyᵐ0 mA ⇘ mA')
      → Γ ,∙ ▶ #S k ⇘ Γ' ,∙  w/ mA'
  ▶S= : Γ ▶ k ⇘ Γ' w/ mA
      → (upmA : ↑tyᵐ0 mA ⇘ mA')
      → (upB : B ↑ty k ⇘ B')
      → Γ ,= B ▶ #S k ⇘ Γ' ,= B' w/ mA'
  ▶S⋈ : Γ ▶ k ⇘ Γ' w/ mA
      → Γ ⋈ ▶ k ⇘ Γ' ⋈ w/ mA

infix 3 _⨟_▶_⇘_⨟_w/_
data _⨟_▶_⇘_⨟_w/_ : Env n m → Env n m → Fin (1 + m) → Env n (1 + m) → Env n (1 + m) → MType m → Set where
  ▶Z^ : Γ ⨟ Δ ▶ #0 ⇘ (Γ ,^) ⨟ (Δ ,^) w/ nothing
  ▶Z∙ : Γ ⨟ Δ ▶ #0 ⇘ Γ ,∙ ⨟ Δ ,∙ w/ nothing
  ▶Z= : (regA : Γ ⊢r A)
      → Γ ⨟ Δ ▶ #0 ⇘ Γ ,= A ⨟ Δ ,= A w/ (just A)
  ▶S, : Γ ⨟ Δ ▶ k ⇘ Γ' ⨟ Δ' w/ mA
      → (up : B ↑ty k ⇘ B')
      → Γ , B ⨟ Δ , B ▶ k ⇘ Γ' , B' ⨟ Δ' , B' w/ mA
  ▶S^ : Γ ⨟ Δ ▶ k ⇘ Γ' ⨟ Δ' w/ mA
      → (upmA : ↑tyᵐ0 mA ⇘ mA')
      → Γ ,^ ⨟ Δ ,^ ▶ #S k ⇘ Γ' ,^ ⨟ Δ' ,^ w/ mA'
  ▶S∙ : Γ ⨟ Δ ▶ k ⇘ Γ' ⨟ Δ'  w/ mA
      → (upmA : ↑tyᵐ0 mA ⇘ mA')
      → Γ ,∙ ⨟ Δ ,∙ ▶ #S k ⇘ Γ' ,∙ ⨟ Δ' ,∙  w/ mA'
  ▶S= : Γ ⨟ Δ ▶ k ⇘ Γ' ⨟ Δ' w/ mA
      → (upmA : ↑tyᵐ0 mA ⇘ mA')
      → (upB : B ↑ty k ⇘ B')
      → Γ ,= B ⨟ Δ ,= B ▶ #S k ⇘ Γ' ,= B' ⨟ Δ' ,= B' w/ mA'
  ▶S⋈ : Γ ⨟ Δ ▶ k ⇘ Γ' ⨟ Δ' w/ mA
      → Γ ⋈ ⨟ Δ ⋈ ▶ k ⇘ Γ' ⋈ ⨟ Δ' ⋈ w/ mA
