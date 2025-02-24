module Implicit.AlgoCounter.Base where

open import Implicit.Language.All
open import Implicit.Algo.Base

✫ : Counter → Counter
✫ Z = Z
✫ ∞ = ∞
✫ (𝕚 j) = j
✫ (𝕔 j) = j

infix 3 _⊢_⇒_⇒_↡_
infix 3 _⊢_⌞_⌝_⊣_↪_↡_

data _⊢_⇒_⇒_↡_ : Env n m → Context n m → Term n m → Type m → Counter → Set
data _⊢_⌞_⌝_⊣_↪_↡_ : Env n m → Type m → Polar → Context n m → Env n m → Type m → Counter → Set

data _⊢_⇒_⇒_↡_ where

  ⊢lit : ∀ {num : ℕ}
    → (cloΓ : TypClosed Γ)
    → Γ ⊢ □ ⇒ lit num ⇒ Int ↡ Z

  ⊢var :
      (cloΓ : TypClosed Γ)
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
    → (cloΣ : Γ ⊢cᶜ Σ)
    → (s : Γ ⋈ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Γ ⋈ ↪ B ↡ j)
    → Γ ⊢ Σ ⇒ g ⇒ B ↡ j

  ⊢tabs :
      Γ ,∙ ⊢ □ ⇒ e ⇒ A ↡ Z
    → Γ ⊢ □ ⇒ Λ e ⇒ `∀ A ↡ Z


data _⊢_⌞_⌝_⊣_↪_↡_ where
  s-int :
     (cloΓ : SubClosed Γ)
    → Γ ⊢ Int ⌞ ≤ ⌝ τ Int ⊣ Γ ↪ Int ↡ ∞

  s-empty :
     (cloΓ : SubClosed Γ)
    → (clo : Γ ⊢c A)
    → Γ ⊢ A ⌞ ≤⁺ ⌝ □ ⊣ Γ ↪ A ↡ Z

  s-var-∙ :
          (cloΓ : SubClosed Γ)
    → Γ ∋∙ X
    → Γ ⊢ (‶ X) ⌞ ≤ ⌝ τ (‶ X) ⊣ Γ ↪ ‶ X ↡ ∞

  s-var-= :
      (cloΓ : SubClosed Γ)
    → Γ ∋=¹ X
    → Γ ⊢ (‶ X) ⌞ ≤ ⌝ τ (‶ X) ⊣ Γ ↪ ‶ X ↡ ∞

  s-ex-l^ :
      (cloA : Γ ⊢c¹ A)
      → (cloΓ : SubClosed Γ)
    → (inst : [ A / X ] Γ ⟹ Γ')
    → Γ ⊢ ‶ X ⌞ ≤⁺ ⌝ τ A ⊣ Γ' ↪ A ↡ ∞

  s-ex-l= :
      (x-in : Γ ∋ X := B)
    → Γ ⊢ B ⌞ ≤⁺ ⌝ τ A ⊣ Γ' ↪ A' ↡ ∞
    → Γ ⊢ ‶ X ⌞ ≤⁺ ⌝ τ A ⊣ Γ' ↪ A ↡ ∞

  s-ex-typ-l= :
      (x-in : Γ ∋ X :=¹ B)
    → Γ ⊢ B ⌞ ≤ ⌝ τ A ⊣ Γ' ↪ A' ↡ ∞
    → Γ ⊢ ‶ X ⌞ ≤ ⌝ τ A ⊣ Γ' ↪ A ↡ ∞

  s-ex-r^ :
      (cloA : Γ ⊢c¹ A)
    → (cloΓ : SubClosed Γ)
    → (inst : [ A / X ] Γ ⟹ Γ')
    → Γ ⊢ A ⌞ ≤⁻ ⌝ τ (‶ X) ⊣ Γ' ↪ ‶ X ↡ ∞

  s-ex-r= :
      (x-in : Γ ∋ X := B)
    → Γ ⊢ A ⌞ ≤⁻ ⌝ τ B ⊣ Γ' ↪ A' ↡ ∞
    → Γ ⊢ A ⌞ ≤⁻ ⌝ τ (‶ X) ⊣ Γ' ↪ (‶ X) ↡ ∞

  s-ex-typ-r= :
      (x-in : Γ ∋ X :=¹ B)
    → Γ ⊢ A ⌞ ≤ ⌝ τ B ⊣ Γ' ↪ A' ↡ ∞
    → Γ ⊢ A ⌞ ≤ ⌝ τ (‶ X) ⊣ Γ' ↪ (‶ X) ↡ ∞

  s-arr :
      Γ₁ ⊢ C ⌞ ⋆ ≤ ⌝ τ A ⊣ Γ₂ ↪ A' ↡ ∞
    → Γ₂ ⊢ B ⌞ ≤ ⌝ τ D ⊣ Γ₃ ↪ D' ↡ ∞
    → Γ₁ ⊢ A `→ B ⌞ ≤ ⌝ τ (C `→ D) ⊣ Γ₃ ↪ (C `→ D) ↡ ∞

  s-term-c :
--      (cloA : Γ ⊢c A)
-- comment this one, if we restrict such condition on the typing
      (⊢e : 𝕣 Γ ⊢ τ A ⇒ e ⇒ A' ↡ ∞)
    → Γ ⊢ B ⌞ ≤⁺ ⌝ Σ ⊣ Γ' ↪ D ↡ j
    → Γ ⊢ (A `→ B) ⌞ ≤⁺ ⌝ ([ e ]↝ Σ) ⊣ Γ' ↪ A' `→ D ↡ (𝕔 j)

  s-term-o :
      (opnA : Γ ⊢o² A)
    → (⊢e : 𝕣 Γ ⊢ □ ⇒ e ⇒ C ↡ Z)
    → Γ ⊢ C ⌞ ≤⁻ ⌝ τ A ⊣ Γ₁ ↪ A' ↡ ∞
    → Γ₁ ⊢ B ⌞ ≤⁺ ⌝ Σ ⊣ Γ₂ ↪ D ↡ j
    → Γ ⊢ A `→ B ⌞ ≤⁺ ⌝ ([ e ]↝ Σ) ⊣ Γ₂ ↪ C `→ D ↡ (𝕚 j)

  s-∀ :
      Γ ,∙ ⊢ A ⌞ ≤ ⌝ τ B ⊣ Γ' ,∙ ↪ C ↡ ∞
    → Γ ⊢ `∀ A ⌞ ≤ ⌝ τ (`∀ B) ⊣ Γ' ↪ `∀ C ↡ ∞

  s-∀l :
      Γ ,^ ⊢ A ⌞ ≤⁺ ⌝ ([ e' ]↝ Σ') ⊣ Γ' ,= B ↪ (C `→ D) ↡ j
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (st₁ : ⟦ B ⟧ C ⇘ C')
    → (st₂ : ⟦ B ⟧ D ⇘ D')
    → Γ ⊢ `∀ A ⌞ ≤⁺ ⌝ ([ e ]↝ Σ) ⊣ Γ' ↪ C' `→ D' ↡ j
