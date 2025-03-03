module Implicit.Algo.Base where

open import Implicit.Language.All

open import Implicit.Algo.Syntax public
open import Implicit.Algo.Shift public
open import Implicit.Algo.Subst public
open import Implicit.Algo.OpenClose public
open import Implicit.Algo.Lookup public
open import Implicit.Algo.Split public
-- open import Implicit.Algo.Polarity public

infix 3 _⊢_⇒_⇒_
infix 3 _⊢_⌞_⌝_⊣_↪_

data _⊢_⇒_⇒_ : Env n m → Context n m → Term n m → Type m → Set
data _⊢_⌞_⌝_⊣_↪_ : Env n m → Type m → Polar → Context n m → Env n m → Type m → Set

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
    → (cloΣ : Γ ⊢cᶜ Σ)
    → (s : Γ ⋈ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Γ ⋈ ↪ B)
    → Γ ⊢ Σ ⇒ g ⇒ B

  ⊢tabs :
      Γ ,∙ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ □ ⇒ Λ e ⇒ `∀ A


data _⊢_⌞_⌝_⊣_↪_ where
  s-int :
      (cloΓ : SubClosed Γ)
    → Γ ⊢ Int ⌞ ≤ ⌝ τ Int ⊣ Γ ↪ Int

  s-empty :
      (cloΓ : SubClosed Γ)
    → (cloA : Γ ⊢c A)
    → Γ ≫² A ⇘ A%
    → Γ ⊢ A ⌞ ≤⁺ ⌝ □ ⊣ Γ ↪ A%

  s-var-∙ :
      (cloΓ : SubClosed Γ)
    → Γ ∋∙ X
    → Γ ⊢ (‶ X) ⌞ ≤ ⌝ τ (‶ X) ⊣ Γ ↪ ‶ X

  s-var-= :
      (cloΓ : SubClosed Γ)
    → Γ ∋=¹ X
    → Γ ⊢ (‶ X) ⌞ ≤ ⌝ τ (‶ X) ⊣ Γ ↪ ‶ X

  s-ex-typ-l=+ :
      (x-in : Γ ∋ X :=¹ B)
    → Γ ⊢ B ⌞ ≤⁺ ⌝ τ A ⊣ Γ' ↪ A'
    → Γ ⊢ ‶ X ⌞ ≤⁺ ⌝ τ A ⊣ Γ' ↪ A

  s-ex-typ-l=- :
      (x-in : Γ ∋ X :=¹ B)
    → Γ ⊢ B ⌞ ≤⁻ ⌝ τ A ⊣ Γ' ↪ A'
    → Γ ⊢ ‶ X ⌞ ≤⁻ ⌝ τ A ⊣ Γ' ↪ ‶ X

  s-ex-typ-r=+ :
      (x-in : Γ ∋ X :=¹ B)
    → Γ ⊢ A ⌞ ≤⁺ ⌝ τ B ⊣ Γ' ↪ B'
    → Γ ⊢ A ⌞ ≤⁺ ⌝ τ (‶ X) ⊣ Γ' ↪ ‶ X

  s-ex-typ-r=- :
      (x-in : Γ ∋ X :=¹ B)
    → Γ ⊢ A ⌞ ≤⁻ ⌝ τ B ⊣ Γ' ↪ B'
    → Γ ⊢ A ⌞ ≤⁻ ⌝ τ (‶ X) ⊣ Γ' ↪ A

  s-ex-l^ :
      (x-in : Γ ∋^² X)
    → (cloA : Γ ⊢c¹ A)
    → (inst : [ A / X ] Γ ⟹ Γ')
    → Γ ⊢ ‶ X ⌞ ≤⁺ ⌝ τ A ⊣ Γ' ↪ A

  s-ex-r^ :
      (x-in : Γ ∋^² X)
    → (cloA : Γ ⊢c¹ A)
    → (inst : [ A / X ] Γ ⟹ Γ')
    → Γ ⊢ A ⌞ ≤⁻ ⌝ τ (‶ X) ⊣ Γ' ↪ A

  s-ex-l= :
      (x-in : Γ ∋ X := B)
    → Γ ⊢ B ⌞ ≤⁺ ⌝ τ A ⊣ Γ' ↪ A'
    → Γ ⊢ ‶ X ⌞ ≤⁺ ⌝ τ A ⊣ Γ' ↪ A

  s-ex-r= :
      (x-in : Γ ∋ X := B)
    → Γ ⊢ A ⌞ ≤⁻ ⌝ τ B ⊣ Γ' ↪ A'
    → Γ ⊢ A ⌞ ≤⁻ ⌝ τ (‶ X) ⊣ Γ' ↪ A

  s-arr :
      Γ₁ ⊢ C ⌞ ⋆ ≤ ⌝ τ A ⊣ Γ₂ ↪ C'
    → Γ₂ ⊢ B ⌞ ≤ ⌝ τ D ⊣ Γ₃ ↪ D'
    → Γ₁ ⊢ A `→ B ⌞ ≤ ⌝ τ (C `→ D) ⊣ Γ₃ ↪ (C' `→ D')

  s-term-c :
      (cloA : Γ ⊢c A)
-- comment this one, if we restrict such condition on the typing
    → (ap : Γ ≫² A ⇘ A%)
    → (⊢e : 𝕣 Γ ⊢ τ A% ⇒ e ⇒ A')
    → Γ ⊢ B ⌞ ≤⁺ ⌝ Σ ⊣ Γ' ↪ D
    → Γ ⊢ (A `→ B) ⌞ ≤⁺ ⌝ ([ e ]↝ Σ) ⊣ Γ' ↪ A% `→ D

  s-term-o :
      (opnA : Γ ⊢o² A)
    → (⊢e : 𝕣 Γ ⊢ □ ⇒ e ⇒ C)
    → Γ ⊢ C ⌞ ≤⁻ ⌝ τ A ⊣ Γ₁ ↪ A'
    → Γ₁ ⊢ B ⌞ ≤⁺ ⌝ Σ ⊣ Γ₂ ↪ D
    → Γ ⊢ A `→ B ⌞ ≤⁺ ⌝ ([ e ]↝ Σ) ⊣ Γ₂ ↪ C `→ D

  s-∀ :
      Γ ,∙ ⊢ A ⌞ ≤ ⌝ τ B ⊣ Γ' ,∙ ↪ C
    → Γ ⊢ `∀ A ⌞ ≤ ⌝ τ (`∀ B) ⊣ Γ' ↪ `∀ C

  s-∀l :
      Γ ,^ ⊢ A ⌞ ≤⁺ ⌝ ([ e' ]↝ Σ') ⊣ Γ' ,= B ↪ (C' `→ D')
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Γ ⊢ `∀ A ⌞ ≤⁺ ⌝ ([ e ]↝ Σ) ⊣ Γ' ↪ C `→ D
