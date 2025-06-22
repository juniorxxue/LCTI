module Implicit.Algo2Interm.AlgoCounter.Base where

open import Implicit.Language.All
open import Implicit.Algo.Base

✫ : Counter m → Counter m
✫ Z = Z
✫ ∞ = ∞
✫ (𝕚 j) = j
✫ (𝕔 j) = j
✫ (𝕥₍ A ₎ j) = j

infix 3 _⊢_⇒_⇒_↡_
infix 3 _⊢_≤⁺_⊣_↪_↡_
infix 3 _⊨_⟹_↡_

data _⊢_⇒_⇒_↡_ : Env n m → Context n m → Term n m → Type m → Counter m → Set
data _⊢_≤⁺_⊣_↪_↡_ : Env n m → Type m → Context n m → Env n m → Type m → Counter m → Set
data _⊨_⟹_↡_ : Env n m → Context n m → Type m → Counter m → Set


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
      Γ ⊢ [ e₂ ]↝ Σ ⇒ e₁ ⇒ A `→ B ↡ j
    → Γ ⊢ Σ ⇒ e₁ · e₂ ⇒ B ↡ (✫ j)

  ⊢lam₁ :
      Γ , A ⊢ τ B ⇒ e ⇒ C ↡ ∞
    → Γ ⊢ τ (A `→ B) ⇒ ƛ e ⇒ A `→ C ↡ ∞

  ⊢lam₂ :
      Γ ⊢ □ ⇒ e₂ ⇒ A ↡ Z
    → (up-c : ↑tmᶜ0 Σ ⇘ Σ')
    → Γ , A ⊢ Σ' ⇒ e ⇒ B ↡ j
    → Γ ⊢ [ e₂ ]↝ Σ ⇒ ƛ e ⇒ A `→ B ↡ (𝕚 j)

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
      Γ ⊢ A ⓪↝ Σ ⇒ e ⇒ `∀ B ↡ 𝕥₍ A ₎ j
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
      (ap : Δ ≫ A ⇘ A%)
    → (⊢e : 𝕣 Δ ⊢ τ A% ⇒ e ⇒ A' ↡ ∞)
    → Δ ⊢ B ≤⁺ Σ ⊣ Ψ ↪ D ↡ j
    → Δ ⊢ (A `→ B) ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ A% `→ D ↡ 𝕔 j

  s-term-o :
      (⊢e : 𝕣 Δ ⊢ □ ⇒ e ⇒ C ↡ Z)
    → (ss : Δ ⊢ C ⌞ ≤⁻ ⌝ A ⊣ Ω)
    → Ω ⊢ B ≤⁺ Σ ⊣ Ψ ↪ D ↡ j
    → Δ ⊢ A `→ B ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D ↡ 𝕚 j

  s-term-c-n :
      Δ ⊢ B ≤⁺ Σ ⊣ Ψ ↪ D ↡ j
    → (ap : Ψ ≫ A ⇘ A%)
    → (⊢e : 𝕣 Ψ ⊢ τ A% ⇒ e ⇒ A' ↡ ∞)
    → Δ ⊢ (A `→ B) ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ A% `→ D ↡ 𝕔 j

  s-term-o-n :
      Δ ⊢ B ≤⁺ Σ ⊣ Ω ↪ D ↡ j
    → (⊢e : 𝕣 Ω ⊢ □ ⇒ e ⇒ C  ↡ Z)
    → (ss : Ω ⊢ C ⌞ ≤⁻ ⌝ A ⊣ Ψ)
    → Δ ⊢ A `→ B ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D ↡ 𝕚 j

  s-∀l-𝕚 :
      Δ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,= B ↪ (C' `→ D') ↡ (𝕚 j')
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upj : ↑tyʲ0 j ⇘ j')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D ↡ (𝕚 j)

  s-∀l-𝕔 :
      Δ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,= B ↪ (C' `→ D') ↡ (𝕔 j')
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upj : ↑tyʲ0 j ⇘ j')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D ↡ (𝕔 j)

  s-∀l-no-𝕚 :
      Δ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,^ ↪ (C' `→ D') ↡ (𝕚 j')
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upj : ↑tyʲ0 j ⇘ j')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D  ↡ (𝕚 j)

  s-∀l-no-𝕔 :
      Δ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,^ ↪ (C' `→ D') ↡ (𝕔 j')
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upj : ↑tyʲ0 j ⇘ j')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D ↡ (𝕔 j)

  s-tapp :
      Δ ,= B ⊢ A ≤⁺ Σ' ⊣ Ψ ,= B ↪ C ↡ j'
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upj : ↑tyʲ0 j ⇘ j')
    → Δ ⊢ `∀ A ≤⁺ (B ⓪↝ Σ) ⊣ Ψ ↪ `∀ C ↡ (𝕥₍ B ₎ j)

  s-svar-term :
      Δ ∋ X := A
    → Δ ⊢ A ≤⁺ ([ e ]↝ Σ) ⊣ Δ ↪ B `→ C ↡ j
    → Δ ⊢ ‶ X ≤⁺ ([ e ]↝ Σ) ⊣ Δ ↪ B `→ C ↡ j

  s-svar-tapp :
      Δ ∋ X := A
    → Δ ⊢ A ≤⁺ (B ⓪↝ Σ) ⊣ Δ ↪ `∀ C ↡ (𝕥₍ B ₎ j)
    → Δ ⊢ ‶ X ≤⁺ (B ⓪↝ Σ) ⊣ Δ ↪ `∀ C ↡ (𝕥₍ B ₎ j)

  s-evar-infers :
      (infs : 𝕣 Δ ⊨ [ e ]↝ Σ ⟹ A ↡ (𝕚 j))
    → (inst : [ A / X ] Δ ⟹ Ψ) -- implies Γ ∋^k
    → Δ ⊢ ‶ X ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ A ↡ (𝕚 j)

data _⊨_⟹_↡_ where
  infs-z : (regΓ : TRegular Γ)
         → (regA : Γ ⊢r A)
         → Γ ⊨ τ A ⟹ A ↡ ∞
  infs-s : (⊢e : Γ ⊢ □ ⇒ e ⇒ A ↡ Z)
         → Γ ⊨ Σ ⟹ B ↡ j
         → Γ ⊨ [ e ]↝ Σ ⟹ A `→ B ↡ 𝕚 j
