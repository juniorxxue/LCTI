module Implicit.Algo.Base where

open import Implicit.Language.All

open import Implicit.Algo.Constructs.Syntax public
open import Implicit.Algo.Constructs.Shift public
open import Implicit.Algo.Constructs.Subst public
open import Implicit.Algo.Constructs.Lookup public
open import Implicit.Algo.Constructs.Split public

infix 3 _⊢_⌞_⌝_⊣_
data _⊢_⌞_⌝_⊣_ : Env n m → Type m → Polar → Type m → Env n m → Set where
  s-int :
      (regΓ : SRegular Δ)
    → Δ ⊢ Int ⌞ ≤ ⌝ Int ⊣ Δ

  s-var-∙ :
      (regΓ : SRegular Δ)
    → Δ ∋∙ X
    → Δ ⊢ (‶ X) ⌞ ≤ ⌝ (‶ X) ⊣ Δ

  s-ex-l^ :
--      (x-in : Δ ∋^ X)
--    → (regA : Δ ⊢r A)
      (inst : [ A / X ] Δ ⟹ Ψ)
    → Δ ⊢ ‶ X ⌞ ≤⁺ ⌝ A ⊣ Ψ

  s-ex-r^ :
--      (x-in : Δ ∋^ X) -- implied by inst
--    → (regA : Γ ⊢r A) -- implied by the inst
      (inst : [ A / X ] Δ ⟹ Ψ)
    → Δ ⊢ A ⌞ ≤⁻ ⌝ (‶ X) ⊣ Ψ

  s-ex-l= :
      (regΓ : SRegular Δ)
    → (x-in : Δ ∋ X := A)
    → Δ ⊢ ‶ X ⌞ ≤⁺ ⌝ A ⊣ Δ

  s-ex-r= :
      (regΓ : SRegular Δ)
    → (x-in : Δ ∋ X := A)
    → Δ ⊢ A ⌞ ≤⁻ ⌝ (‶ X) ⊣ Δ

  s-arr :
      Δ ⊢ C ⌞ ⋆ ≤ ⌝ A ⊣ Ω
    → Ω ⊢ B ⌞ ≤ ⌝ D ⊣ Ψ
    → Δ ⊢ A `→ B ⌞ ≤ ⌝ (C `→ D) ⊣ Ψ

  s-∀ :
      Δ ,∙ ⊢ A ⌞ ≤ ⌝ B ⊣ Ψ ,∙
    → Δ ⊢ `∀ A ⌞ ≤ ⌝ (`∀ B) ⊣ Ψ

infix 3 _⊢_⇒_⇒_
infix 3 _⊢_≤⁺_⊣_↪_

data _⊢_⇒_⇒_ : Env n m → Context n m → Term n m → Type m → Set
data _⊢_≤⁺_⊣_↪_ : Env n m → Type m → Context n m → Env n m → Type m → Set

data _⊢_⇒_⇒_ where

  ⊢lit : ∀ {num : ℕ}
    → (regΓ : TRegular Γ)
    → Γ ⊢ □ ⇒ lit num ⇒ Int

  ⊢var :
      (regΓ : TRegular Γ)
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
      (regΓ : SRegular Δ)
    → (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊢ A ≤⁺ □ ⊣ Δ ↪ A%

  s-type :
      (ss : Δ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Ψ)
    → Δ ⊢ A ≤⁺ (τ B) ⊣ Ψ ↪ B

  s-term-c :
      (cloA : Δ ⊢c A)
    → (ap : Δ ≫ A ⇘ A%)
    → (⊢e : 𝕣 Δ ⊢ τ A% ⇒ e ⇒ A')
    → Δ ⊢ B ≤⁺ Σ ⊣ Ψ ↪ D
    → Δ ⊢ (A `→ B) ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ A% `→ D

  s-term-o :
      (opnA : Δ ⊢o A)
    → (⊢e : 𝕣 Δ ⊢ □ ⇒ e ⇒ C)
    → (ss : Δ ⊢ C ⌞ ≤⁻ ⌝ A ⊣ Ω)
    → Ω ⊢ B ≤⁺ Σ ⊣ Ψ ↪ D
    → Δ ⊢ A `→ B ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D

  s-∀l :
      Δ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,= B ↪ (C' `→ D')
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D
