module Implicit.Algo2Interm.AlgoCounter.Base where

open import Implicit.Language.All
open import Implicit.Algo.Base

-- assumption: A is open
infix 3 _⊢_↦_↡_
data _⊢_↦_↡_ : Env n m → Type m → Context n m → Counter m → Set where
  tf-tvar :
    Γ ⊢ ‶ X ↦ □ ↡ Z
  tf-∀ :
    Γ ⊢ `∀ A ↦ □ ↡ Z
  tf-arr :
      Γ ⊢c A
    → Γ ≫ A ⇘ A%
    → Γ ⊢ B ↦ Σ ↡ j
    → Γ ⊢ A `→ B ↦ A% ◐↝ Σ ↡ 𝕊₍ Z ₎ j

infix 3 _⊢_⇒_⇒_↡_
infix 3 _⊢_≤⁺_⊣_↪_↡_

data _⊢_⇒_⇒_↡_ : Env n m → Context n m → Term n m → Type m → Counter m → Set
data _⊢_≤⁺_⊣_↪_↡_ : Env n m → Type m → Context n m → Env n m → Type m → Counter m → Set


data _⊢_⇒_⇒_↡_ where
  ⊢lit : ∀ {num : ℕ}
    → (regΓ : TRegular Γ)
    → Γ ⊢ □ ⇒ lit num ⇒ Int ↡ Z

  ⊢var :
      (regΓ : TRegular Γ)
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊢ □ ⇒ ` x ⇒ A ↡ Z

  ⊢ann :
      Γ ⊢ τ A ⇒ e ⇒ B ↡ ∞
    → Γ ⊢ □ ⇒ e ⦂ A ⇒ A ↡ Z

  ⊢app :
      Γ ⊢ [ e₂ ]↝ Σ ⇒ e₁ ⇒ A `→ B ↡ (𝕊₍ w ₎ j)
    → Γ ⊢ Σ ⇒ e₁ · e₂ ⇒ B ↡ j

  ⊢lam₁ :
      Γ , A ⊢ τ B ⇒ e ⇒ C ↡ ∞
    → Γ ⊢ τ (A `→ B) ⇒ ƛ e ⇒ A `→ C ↡ ∞

  ⊢lam₂ :
      Γ ⊢ □ ⇒ e₂ ⇒ A ↡ Z
    → (up-c : ↑tmᶜ0 Σ ⇘ Σ')
    → Γ , A ⊢ Σ' ⇒ e ⇒ B ↡ j
    → Γ ⊢ [ e₂ ]↝ Σ ⇒ ƛ e ⇒ A `→ B ↡ (𝕊₍ Z ₎ j)

  ⊢sub :
      Γ ⊢ □ ⇒ g ⇒ A ↡ Z
    → (ne : NonEmpty Σ)
    → (gc : GenericConsumer g)
    → (s : Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ B ↡ j)
    → Γ ⊢ Σ ⇒ g ⇒ B ↡ j

  ⊢tabs :
      Γ ,∙ ⊢ □ ⇒ e ⇒ A ↡ Z
    → Γ ⊢ □ ⇒ Λ e ⇒ `∀ A ↡ Z

  ⊢tapp :
      Γ ⊢ A ⓪↝ Σ ⇒ e ⇒ `∀ B ↡ 𝕋₍ A ₎ j
    → (st : ⟦ A ⟧ B ⇘ B*)
    → Γ ⊢ Σ ⇒ e ⓪ A ⇒ B* ↡ j


data _⊢_≤⁺_⊣_↪_↡_ where

  s-empty :
      (regΓ : SRegular Δ)
    → (cloA : Δ ⊢c A)
    → Δ ≫ A ⇘ A%
    → Δ ⊢ A ≤⁺ □ ⊣ Δ ↪ A% ↡ Z

  s-type :
      (ss : Δ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Ψ)
    → Δ ⊢ A ≤⁺ (τ B) ⊣ Ψ ↪ B ↡ ∞

  s-term-c :
      (cloA : Δ ⊢c A)
    → (ap : Δ ≫ A ⇘ A%)
    → (⊢e : 𝕣 Δ ⊢ τ A% ⇒ e ⇒ A' ↡ ∞)
    → Δ ⊢ B ≤⁺ Σ ⊣ Ψ ↪ D ↡ j
    → Δ ⊢ (A `→ B) ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ A% `→ D ↡ 𝕊₍ ∞ ₎ j

  s-term-o :
      (opnA : Δ ⊢o A)
    → (tf : Δ ⊢ A ↦ δ ↡ w)
    → (⊢e : 𝕣 Δ ⊢ δ ⇒ e ⇒ C)
    → (ss : Δ ⊢ C ⌞ ≤⁻ ⌝ A ⊣ Ω)
    → Ω ⊢ B ≤⁺ Σ ⊣ Ψ ↪ D ↡ j
    → Δ ⊢ A `→ B ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D ↡ 𝕊₍ w ₎ j

  s-∀l :
      Δ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,= B ↪ (C' `→ D') ↡ (𝕊₍ w' ₎ j')
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upj : ↑tyʲ0 j ⇘ j')
    → (upw : ↑tyʲ0 w ⇘ w')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D ↡ (𝕊₍ w ₎ j)

  s-∀l-p :
      Δ ,^ ⊢ A ≤⁺ (E' ◐↝ Σ') ⊣ Ψ ,= B ↪ (C' `→ D') ↡ (𝕊₍ Z ₎ j')
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upj : ↑tyʲ0 j ⇘ j')
    → (upE : ↑ty0 E ⇘ E')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ (E ◐↝ Σ) ⊣ Ψ ↪ C `→ D ↡ (𝕊₍ Z ₎ j)

  s-tapp :
      Δ ,= B ⊢ A ≤⁺ Σ' ⊣ Ψ ,= B ↪ C ↡ j'
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upj : ↑tyʲ0 j ⇘ j')
    → Δ ⊢ `∀ A ≤⁺ (B ⓪↝ Σ) ⊣ Ψ ↪ `∀ C ↡ (𝕋₍ B ₎ j)
