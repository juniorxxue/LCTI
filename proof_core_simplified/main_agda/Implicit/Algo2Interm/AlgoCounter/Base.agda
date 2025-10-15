module Implicit.Algo2Interm.AlgoCounter.Base where

open import Implicit.Language.All
open import Implicit.Algo.Base

infix 3 _⊢_⇒_⇒_↡_
infix 3 _⊢_≤⁺_⊣_↪_↡_
infix 3 _⊨_⟹_↡_

data _⊢_⇒_⇒_↡_ : Env n m → Context n m → Term n m → Type m → Mask → Set
data _⊢_≤⁺_⊣_↪_↡_ : Env n m → Type m → Context n m → Env n m → Type m → Mask → Set
data _⊨_⟹_↡_ : Env n m → Context n m → Type m → Mask → Set


data _⊢_⇒_⇒_↡_ where
  ⊢lit : ∀ {num : ℕ}
    → (regΓ : TRegular Γ)
    → Γ ⊢ □ ⇒ lit num ⇒ Int ↡ `■

  ⊢var :
      (regΓ : TRegular Γ)
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊢ □ ⇒ ` x ⇒ A ↡ `■

  ⊢ann :
      Γ ⊢ τ A ⇒ e ⇒ B ↡ `□
    → Γ ⊢ □ ⇒ e ⦂ A ⇒ A ↡ `■

  ⊢app :
      Γ ⊢ [ e₂ ]↝ Σ ⇒ e₁ ⇒ A `→ B ↡ (i · j)
    → Γ ⊢ Σ ⇒ e₁ · e₂ ⇒ B ↡ j

  ⊢lam₁ :
      Γ , A ⊢ τ B ⇒ e ⇒ C ↡ `□
    → Γ ⊢ τ (A `→ B) ⇒ ƛ e ⇒ A `→ C ↡ `□

  ⊢lam₂ :
      Γ ⊢ □ ⇒ e₂ ⇒ A ↡ `■
    → (up-c : ↑tmᶜ0 Σ ⇘ Σ')
    → Γ , A ⊢ Σ' ⇒ e ⇒ B ↡ j
    → Γ ⊢ [ e₂ ]↝ Σ ⇒ ƛ e ⇒ A `→ B ↡ (□ · j)

  ⊢sub :
      Γ ⊢ □ ⇒ g ⇒ A ↡ `■
    → (ne : NonEmpty Σ)
    → (gc : GenericConsumer g)
    → (s : Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ B ↡ j)
    → Γ ⊢ Σ ⇒ g ⇒ B ↡ j

  ⊢tabs :
      Γ ,∙ ⊢ □ ⇒ e ⇒ A ↡ `■
    → Γ ⊢ □ ⇒ Λ e ⇒ `∀ A ↡ `■

  ⊢tabs-τ :
      Γ ,∙ ⊢ τ B ⇒ e ⇒ A ↡ `□
    → Γ ⊢ τ (`∀ B) ⇒ Λ e ⇒ `∀ A ↡ `□

  ⊢tapp :
      Γ ⊢ □ ⇒ e ⇒ `∀ B ↡ `■
    → (st : ⟦ A ⟧ B ⇘ B*)
    → (regA : Γ ⊢r A)
    → (s : Γ ⋈ ⊢ B* ≤⁺ Σ ⊣ Γ ⋈ ↪ C ↡ j)
    → Γ ⊢ Σ ⇒ e ⓪ A ⇒ C ↡ j


data _⊢_≤⁺_⊣_↪_↡_ where

  s-empty :
      (regΓ : SRegular Δ)
    → (cloA : Δ ⊢c A)
    → Δ ≫ A ⇘ A%
    → Δ ⊢ A ≤⁺ □ ⊣ Δ ↪ A% ↡ `■

  s-type :
      (ss : Δ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Ψ)
    → Δ ⊢ A ≤⁺ (τ B) ⊣ Ψ ↪ B ↡ `□

  s-term-c :
      (cloA : Δ ⊢c A)
    → (ap : Δ ≫ A ⇘ A%)
    → (⊢e : 𝕣 Δ ⊢ τ A% ⇒ e ⇒ A' ↡ `□)
    → Δ ⊢ B ≤⁺ Σ ⊣ Ψ ↪ D ↡ j
    → Δ ⊢ (A `→ B) ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ A% `→ D ↡ (■ · j)

  s-term-o :
      (opnA : Δ ⊢o A)
    → (⊢e : 𝕣 Δ ⊢ □ ⇒ e ⇒ C ↡ `■)
    → (ss : Δ ⊢ C ⌞ ≤⁻ ⌝ A ⊣ Ω)
    → Ω ⊢ B ≤⁺ Σ ⊣ Ψ ↪ D ↡ j
    → Δ ⊢ A `→ B ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D ↡ (□ · j)

  s-∀l :
      Δ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,= B ↪ (C' `→ D') ↡ (i · j)
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D ↡ (i · j)

  s-∀l-no :
      Δ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,^ ↪ (C' `→ D') ↡ (i · j)
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D  ↡ (i · j)

  s-svar-term :
      Δ ∋ X := A
    → Δ ⊢ A ≤⁺ ([ e ]↝ Σ) ⊣ Δ ↪ B `→ C ↡ j
    → Δ ⊢ ‶ X ≤⁺ ([ e ]↝ Σ) ⊣ Δ ↪ B `→ C ↡ j

  s-evar-infers :
      (infs : 𝕣 Δ ⊨ [ e ]↝ Σ ⟹ A ↡ (□ · j))
    → (inst : [ A / X ] Δ ⟹ Ψ) -- implies Γ ∋^k
    → Δ ⊢ ‶ X ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ A ↡ (□ · j)

data _⊨_⟹_↡_ where
  infs-z : (regΓ : TRegular Γ)
         → (regA : Γ ⊢r A)
         → Γ ⊨ τ A ⟹ A ↡ `□
  infs-s : (⊢e : Γ ⊢ □ ⇒ e ⇒ A ↡ `■)
         → Γ ⊨ Σ ⟹ B ↡ j
         → Γ ⊨ [ e ]↝ Σ ⟹ A `→ B ↡ (□ · j)
