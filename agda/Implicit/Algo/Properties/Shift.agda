module Implicit.Algo.Properties.Shift where

open import Implicit.Language.All
open import Implicit.Algo.Base


↑tmᶜ-total : ∀ (Σ : Context n m) (k)
  → ∃ λ Σ'
  → Σ ↑tmᶜ k ⇘ Σ'
↑tmᶜ-total □ k = ⟨ □ , ↑tmᶜ-□ ⟩
↑tmᶜ-total (τ A) k = ⟨ τ A , ↑tmᶜ-τ ⟩
↑tmᶜ-total ([ e ]↝ Σ) k with ↑tm-total e k | ↑tmᶜ-total Σ k
... | ⟨ e' , up-e ⟩ | ⟨ Σ' , up-Σ ⟩ = ⟨ [ e' ]↝ Σ' , ↑tmᶜ-e up-e up-Σ ⟩

↑tmᶜ0-total : ∀ (Σ : Context n m)
  → ∃ λ Σ'
  → ↑tmᶜ0 Σ ⇘ Σ'
↑tmᶜ0-total Σ = ↑tmᶜ-total Σ #0

↑tmᶜ-unique : Σ ↑tmᶜ k ⇘ Σ₁
            → Σ ↑tmᶜ k ⇘ Σ₂
            → Σ₁ ≡ Σ₂
↑tmᶜ-unique ↑tmᶜ-□ ↑tmᶜ-□ = refl
↑tmᶜ-unique ↑tmᶜ-τ ↑tmᶜ-τ = refl
↑tmᶜ-unique (↑tmᶜ-e up-e up1) (↑tmᶜ-e up-e₁ up2) rewrite ↑tm-unique up-e up-e₁ | ↑tmᶜ-unique up1 up2 = refl

↑tyᶜ-total : ∀ (Σ : Context n m) (k)
  → ∃ λ Σ'
  → Σ ↑tyᶜ k ⇘ Σ'
↑tyᶜ-total □ k = ⟨ □ , ↑tyᶜ-□ ⟩
↑tyᶜ-total (τ A) k with ↑ty-total A k
... | ⟨ A' , upA ⟩ = ⟨ τ A' , ↑tyᶜ-τ upA ⟩
↑tyᶜ-total ([ e ]↝ Σ) k with ↑tyᵉ-total e k | ↑tyᶜ-total Σ k
... | ⟨ e' , upe ⟩ | ⟨ Σ' , upΣ ⟩ = ⟨ [ e' ]↝ Σ' , ↑tyᶜ-e upe upΣ ⟩

↑tyᶜ0-total : ∀ (Σ : Context n m)
  → ∃ λ Σ'
  → ↑tyᶜ0 Σ ⇘ Σ'
↑tyᶜ0-total Σ = ↑tyᶜ-total Σ #0


↑tm-↑tyᵉ-comm' : e ↑tm k₁ ⇘ e₁
                → e ↑tyᵉ k₂ ⇘ e'
                → e' ↑tm k₁ ⇘ e₂
                → e₁ ↑tyᵉ k₂ ⇘ e₂
↑tm-↑tyᵉ-comm' ↑tm-lit ↑tyᵉ-lit ↑tm-lit = ↑tyᵉ-lit
↑tm-↑tyᵉ-comm' ↑tm-var ↑tyᵉ-var ↑tm-var = ↑tyᵉ-var
↑tm-↑tyᵉ-comm' (↑tm-ƛ up1) (↑tyᵉ-ƛ up2) (↑tm-ƛ up3) = ↑tyᵉ-ƛ (↑tm-↑tyᵉ-comm' up1 up2 up3)
↑tm-↑tyᵉ-comm' (↑tm-app up1 up4) (↑tyᵉ-app up2 up5) (↑tm-app up3 up6) = ↑tyᵉ-app (↑tm-↑tyᵉ-comm' up1 up2 up3) (↑tm-↑tyᵉ-comm' up4 up5 up6)
↑tm-↑tyᵉ-comm' (↑tm-⦂ up1) (↑tyᵉ-⦂ up2 up) (↑tm-⦂ up3) = ↑tyᵉ-⦂ (↑tm-↑tyᵉ-comm' up1 up2 up3) up
↑tm-↑tyᵉ-comm' (↑tm-Λ up1) (↑tyᵉ-Λ up2) (↑tm-Λ up3) = ↑tyᵉ-Λ (↑tm-↑tyᵉ-comm' up1 up2 up3)

↑tmᶜ-↑tyᶜ-comm' : Σ ↑tmᶜ k₁ ⇘ Σ₁
                → Σ ↑tyᶜ k₂ ⇘ Σ'
                → Σ' ↑tmᶜ k₁ ⇘ Σ₂
                → Σ₁ ↑tyᶜ k₂ ⇘ Σ₂
↑tmᶜ-↑tyᶜ-comm' ↑tmᶜ-□ ↑tyᶜ-□ ↑tmᶜ-□ = ↑tyᶜ-□
↑tmᶜ-↑tyᶜ-comm' ↑tmᶜ-τ (↑tyᶜ-τ up-t) ↑tmᶜ-τ = ↑tyᶜ-τ up-t
↑tmᶜ-↑tyᶜ-comm' (↑tmᶜ-e up-e up1) (↑tyᶜ-e up-e₁ up2) (↑tmᶜ-e up-e₂ up3) = ↑tyᶜ-e (↑tm-↑tyᵉ-comm' up-e up-e₁ up-e₂) (↑tmᶜ-↑tyᶜ-comm' up1 up2 up3)


↑tyᶜ-comm0' : ∀ {Σ : Context n m} {Σₖ Σₖ₊₁ Σ₀ k}
              → Σ ↑tyᶜ k ⇘ Σₖ
              → ↑tyᶜ0 Σₖ ⇘ Σₖ₊₁
              ---------------------
              → ↑tyᶜ0 Σ ⇘ Σ₀
              → Σ₀ ↑tyᶜ #S k ⇘ Σₖ₊₁
↑tyᶜ-comm0' ↑tyᶜ-□ ↑tyᶜ-□ ↑tyᶜ-□ = ↑tyᶜ-□
↑tyᶜ-comm0' (↑tyᶜ-τ up-t) (↑tyᶜ-τ up-t₁) (↑tyᶜ-τ up-t₂) = ↑tyᶜ-τ (↑ty-comm0' up-t up-t₁ up-t₂)
↑tyᶜ-comm0' (↑tyᶜ-e up-e up1) (↑tyᶜ-e up-e₁ up2) (↑tyᶜ-e up-e₂ up3) = ↑tyᶜ-e (↑tyᵉ-comm0' up-e up-e₁ up-e₂) (↑tyᶜ-comm0' up1 up2 up3)


↑tm-↑tyᵉ-comm : e ↑tm k₁ ⇘ e₁
             → e₁ ↑tyᵉ k₂ ⇘ e₂
             → e ↑tyᵉ k₂ ⇘ e'
             → e' ↑tm k₁ ⇘ e₂
↑tm-↑tyᵉ-comm ↑tm-lit ↑tyᵉ-lit ↑tyᵉ-lit = ↑tm-lit
↑tm-↑tyᵉ-comm ↑tm-var ↑tyᵉ-var ↑tyᵉ-var = ↑tm-var
↑tm-↑tyᵉ-comm (↑tm-ƛ up1) (↑tyᵉ-ƛ up2) (↑tyᵉ-ƛ up3) = ↑tm-ƛ (↑tm-↑tyᵉ-comm up1 up2 up3)
↑tm-↑tyᵉ-comm (↑tm-app up1 up4) (↑tyᵉ-app up2 up5) (↑tyᵉ-app up3 up6) = ↑tm-app (↑tm-↑tyᵉ-comm up1 up2 up3) (↑tm-↑tyᵉ-comm up4 up5 up6)
↑tm-↑tyᵉ-comm (↑tm-⦂ up1) (↑tyᵉ-⦂ up2 up) (↑tyᵉ-⦂ up3 up₁) with refl ← ↑ty-unique up₁ up = ↑tm-⦂ (↑tm-↑tyᵉ-comm up1 up2 up3)
↑tm-↑tyᵉ-comm (↑tm-Λ up1) (↑tyᵉ-Λ up2) (↑tyᵉ-Λ up3) = ↑tm-Λ (↑tm-↑tyᵉ-comm up1 up2 up3)

↑tmᶜ-↑tyᶜ-comm : Σ ↑tmᶜ k₁ ⇘ Σ₁
               → Σ₁ ↑tyᶜ k₂ ⇘ Σ₂
               → Σ ↑tyᶜ k₂ ⇘ Σ'
               → Σ' ↑tmᶜ k₁ ⇘ Σ₂
↑tmᶜ-↑tyᶜ-comm ↑tmᶜ-□ ↑tyᶜ-□ ↑tyᶜ-□ = ↑tmᶜ-□
↑tmᶜ-↑tyᶜ-comm ↑tmᶜ-τ (↑tyᶜ-τ up-t) (↑tyᶜ-τ up-t₁) with refl ← ↑ty-unique up-t up-t₁ = ↑tmᶜ-τ
↑tmᶜ-↑tyᶜ-comm (↑tmᶜ-e up-e up1) (↑tyᶜ-e up-e₁ up2) (↑tyᶜ-e up-e₂ up3) = ↑tmᶜ-e (↑tm-↑tyᵉ-comm up-e up-e₁ up-e₂) (↑tmᶜ-↑tyᶜ-comm up1 up2 up3)

↑tmᶜ-comm' : k₁ #≤ k₂
           → Σ ↑tmᶜ k₂ ⇘ Σ₁
           → Σ₁ ↑tmᶜ (inject₁ k₁) ⇘ Σ₂
           ----------------
           → Σ ↑tmᶜ k₁ ⇘ Σ'
           → Σ' ↑tmᶜ #S k₂ ⇘ Σ₂
↑tmᶜ-comm' lt ↑tmᶜ-□ ↑tmᶜ-□ ↑tmᶜ-□ = ↑tmᶜ-□
↑tmᶜ-comm' lt ↑tmᶜ-τ ↑tmᶜ-τ ↑tmᶜ-τ = ↑tmᶜ-τ
↑tmᶜ-comm' lt (↑tmᶜ-e up-e up1) (↑tmᶜ-e up-e₁ up2) (↑tmᶜ-e up-e₂ up3) = ↑tmᶜ-e (↑tm-comm' lt up-e up-e₁ up-e₂) (↑tmᶜ-comm' lt up1 up2 up3)

nonempty-↑tmᶜ' : NonEmpty Σ'
              → Σ ↑tmᶜ k ⇘ Σ'
              → NonEmpty Σ
nonempty-↑tmᶜ' ne-τ ↑tmᶜ-τ = ne-τ
nonempty-↑tmᶜ' ne-app (↑tmᶜ-e up-e upΣ) = ne-app

nonempty-↑tmᶜ : NonEmpty Σ
              → Σ ↑tmᶜ k ⇘ Σ'
              → NonEmpty Σ'
nonempty-↑tmᶜ ne-τ ↑tmᶜ-τ = ne-τ
nonempty-↑tmᶜ ne-app (↑tmᶜ-e up-e upΣ) = ne-app
