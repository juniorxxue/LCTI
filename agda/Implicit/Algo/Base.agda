module Implicit.Algo.Base where

open import Implicit.Language.All

open import Implicit.Algo.Syntax public
open import Implicit.Algo.Shift public
open import Implicit.Algo.Subst public
open import Implicit.Algo.OpenClose public
open import Implicit.Algo.Lookup public
open import Implicit.Algo.Split public
-- open import Implicit.Algo.Polarity public

infix 3 _⊢_⌞_⌝_⊣_
data _⊢_⌞_⌝_⊣_ : Env n m → Type m → Polar → Type m → Env n m → Set where
  s-int :
      (cloΓ : SubClosed Γ)
    → Γ ⊢ Int ⌞ ≤ ⌝ Int ⊣ Γ

  s-var-∙ :
      (cloΓ : SubClosed Γ)
    → Γ ∋∙ X
    → Γ ⊢ (‶ X) ⌞ ≤ ⌝ (‶ X) ⊣ Γ

  s-ex-l^ :
      (x-in : Γ ∋^² X)
    → (cloA : Γ ⊢c¹ A)
    → (inst : [ A / X ] Γ ⟹ Δ)
    → Γ ⊢ ‶ X ⌞ ≤⁺ ⌝ A ⊣ Δ

  s-ex-r^ :
      (x-in : Γ ∋^² X)
    → (cloA : Γ ⊢c¹ A)
    → (inst : [ A / X ] Γ ⟹ Δ)
    → Γ ⊢ A ⌞ ≤⁻ ⌝ (‶ X) ⊣ Δ

  s-ex-l= :
      (cloΓ : SubClosed Γ)
    → (x-in : Γ ∋ X :=² A)
    → Γ ⊢ ‶ X ⌞ ≤⁺ ⌝ A ⊣ Γ

  s-ex-r= :
      (cloΓ : SubClosed Γ)
    → (x-in : Γ ∋ X :=² A)
    → Γ ⊢ A ⌞ ≤⁻ ⌝ (‶ X) ⊣ Γ

  s-arr :
      Γ ⊢ C ⌞ ⋆ ≤ ⌝ A ⊣ Ω
    → Ω ⊢ B ⌞ ≤ ⌝ D ⊣ Δ
    → Γ ⊢ A `→ B ⌞ ≤ ⌝ (C `→ D) ⊣ Δ

  s-∀ :
      Γ ,∙ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ ,∙
    → Γ ⊢ `∀ A ⌞ ≤ ⌝ (`∀ B) ⊣ Δ

infix 3 _⊢_⇒_⇒_
infix 3 _⊢_≤⁺_⊣_↪_

data _⊢_⇒_⇒_ : Env n m → Context n m → Term n m → Type m → Set
data _⊢_≤⁺_⊣_↪_ : Env n m → Type m → Context n m → Env n m → Type m → Set

data _⊢_⇒_⇒_ where

  ⊢lit : ∀ {num : ℕ}
    → (cloΓ : TypClosed Γ)
    → Γ ⊢ □ ⇒ lit num ⇒ Int

  ⊢var :
      (cloΓ : TypClosed Γ)
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊢ □ ⇒ ` x ⇒ A

  ⊢ann :
      Γ ⊢ τ A ⇒ e ⇒ B
    → Γ ⊢ □ ⇒ e ⦂ A ⇒ A

  ⊢app :
      Γ ⊢ [ e₂ ]↝ Σ ⇒ e₁ ⇒ A `→ B
    → Γ ⊢ Σ ⇒ e₁ · e₂ ⇒ B

  ⊢lam₁ :
      Γ , A ⊢ τ B ⇒ e ⇒ C
    → Γ ⊢ τ (A `→ B) ⇒ ƛ e ⇒ A `→ C

  ⊢lam₂ :
      Γ ⊢ □ ⇒ e₂ ⇒ A
    → (up-c : ↑tmᶜ0 Σ ⇘ Σ')
    → Γ , A ⊢ Σ' ⇒ e ⇒ B
    → Γ ⊢ [ e₂ ]↝ Σ ⇒ ƛ e ⇒ A `→ B

  ⊢sub :
      Γ ⊢ □ ⇒ g ⇒ A
    → (ne : NonEmpty Σ)
    → (gc : GenericConsumer g)
    → (s : Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ B)
    → Γ ⊢ Σ ⇒ g ⇒ B

  ⊢tabs :
      Γ ,∙ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ □ ⇒ Λ e ⇒ `∀ A

data _⊢_≤⁺_⊣_↪_ where

  s-empty :
      (cloΓ : SubClosed Γ)
    → (cloA : Γ ⊢c A)
    → Γ ≫ A ⇘ A%
    → Γ ⊢ A ≤⁺ □ ⊣ Γ ↪ A%

  s-type :
      (ss : Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Γ')
    → Γ ⊢ A ≤⁺ (τ B) ⊣ Γ' ↪ B

  s-term-c :
      (cloA : Γ ⊢c A)
    → (ap : Γ ≫ A ⇘ A%)
    → (⊢e : 𝕣 Γ ⊢ τ A% ⇒ e ⇒ A')
    → Γ ⊢ B ≤⁺ Σ ⊣ Δ ↪ D
    → Γ ⊢ (A `→ B) ≤⁺ ([ e ]↝ Σ) ⊣ Δ ↪ A% `→ D

  s-term-o :
      (opnA : Γ ⊢o² A)
    → (⊢e : 𝕣 Γ ⊢ □ ⇒ e ⇒ C)
    → Γ ⊢ C ⌞ ≤⁻ ⌝ A ⊣ Ω
    → Ω ⊢ B ≤⁺ Σ ⊣ Δ ↪ D
    → Γ ⊢ A `→ B ≤⁺ ([ e ]↝ Σ) ⊣ Δ ↪ C `→ D

  s-∀l :
      Γ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Δ ,= B ↪ (C' `→ D')
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Γ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Δ ↪ C `→ D
