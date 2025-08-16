module Implicit.Algo2Interm.AlgoCounter.Base where

open import Implicit.Language.All
open import Implicit.Algo.Base

✫ : Counter m → Counter m
✫ Z = Z
✫ ∞ = ∞
✫ (𝕚 j) = j
✫ (𝕔 j) = j
✫ (𝕥₍ A ₎ j) = j


infix 3 _~pk'~_w/_↬_↡_

data _~pk'~_w/_↬_↡_ : Type (1 + m) → Context n (1 + m) → Fin (1 + m) → Type m → Counter (1 + m) → Set where
  pk-type : A ~~pk~~ B w/ k ↪ C
          → A ~pk'~ (Context n (1 + m) ∋⦂ τ B) w/ k ↬ C ↡ ∞
  pk-term-𝕚 : B ~pk'~ Σ w/ k ↬ C ↡ j
          → A `→ B ~pk'~ [ e ]↝ Σ w/ k ↬ C ↡ 𝕚 j
  pk-term-𝕔 : B ~pk'~ Σ w/ k ↬ C ↡ j
          → A `→ B ~pk'~ [ e ]↝ Σ w/ k ↬ C ↡ 𝕔 j
  pk-∀l-𝕚   : A ~pk'~ [ e' ]↝ Σ' w/ (#S k) ↬ C' ↡ 𝕚 j'
          → (upΣ : ↑tyᶜ0 Σ ⇘ Σ')
          → (upj : ↑tyʲ0 j ⇘ j')
          → (upe : ↑tyᵉ0 e ⇘ e')
          → (upC : ↑ty0 C ⇘ C')
          → `∀ A ~pk'~ [ e ]↝ Σ w/ k ↬ C ↡ 𝕚 j
  pk-∀l-𝕔   : A ~pk'~ [ e' ]↝ Σ' w/ (#S k) ↬ C' ↡ 𝕔 j'
          → (upΣ : ↑tyᶜ0 Σ ⇘ Σ')
          → (upj : ↑tyʲ0 j ⇘ j')
          → (upe : ↑tyᵉ0 e ⇘ e')
          → (upC : ↑ty0 C ⇘ C')
          → `∀ A ~pk'~ [ e ]↝ Σ w/ k ↬ C ↡ 𝕔 j
  pk-tapp : A ~pk'~ Σ' w/ (#S k) ↬ C' ↡ j'
          → (upC : ↑ty0 C ⇘ C')
          → (upΣ : ↑tyᶜ0 Σ ⇘ Σ')
          → (upj : ↑tyʲ0 j ⇘ j')
          → `∀ A ~pk'~ (B ⓪↝ Σ) w/ k ↬ C ↡ (𝕥₍ B ₎ j)


-- degenerate version for negation
{-
infix 3 _~pk'~_w/_↡_

data _~pk'~_w/_↡_ : Type m → Context n m → Fin m → Counter m → Set where
  pk-type : (inA : k ε A)
          → A ~pk'~ (Context n m ∋⦂ τ B) w/ k ↡ ∞
  pk-term-𝕚 : B ~pk'~ Σ w/ k  ↡  j
          → A `→ B ~pk'~ [ e ]↝ Σ w/ k  ↡ 𝕚 j
  pk-term-𝕔 : B ~pk'~ Σ w/ k  ↡  j
          → A `→ B ~pk'~ [ e ]↝ Σ w/ k  ↡ 𝕔 j
  pk-∀l-𝕚   : A ~pk'~ [ e' ]↝ Σ' w/ (#S k) ↡ 𝕚 j'
          → (upΣ : ↑tyᶜ0 Σ ⇘ Σ')
          → (upj : ↑tyʲ0 j ⇘ j')
          → (upe : ↑tyᵉ0 e ⇘ e')
          → `∀ A ~pk'~ [ e ]↝ Σ w/ k ↡ 𝕚 j
  pk-∀l-𝕔   : A ~pk'~ [ e' ]↝ Σ' w/ (#S k) ↡ 𝕔 j'
          → (upΣ : ↑tyᶜ0 Σ ⇘ Σ')
          → (upj : ↑tyʲ0 j ⇘ j')
          → (upe : ↑tyᵉ0 e ⇘ e')
          → `∀ A ~pk'~ [ e ]↝ Σ w/ k ↡ 𝕔 j
  pk-tapp : A ~pk'~ Σ' w/ (#S k) ↡ j'
          → (upΣ : ↑tyᶜ0 Σ ⇘ Σ')
          → (upj : ↑tyʲ0 j ⇘ j')
          → `∀ A ~pk'~ (B ⓪↝ Σ) w/ k ↡ (𝕥₍ B ₎ j)

-}

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

  ⊢tabs-τ :
      Γ ,∙ ⊢ τ B ⇒ e ⇒ A ↡ ∞
    → Γ ⊢ τ (`∀ B) ⇒ Λ e ⇒ `∀ A ↡ ∞

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
      (cloA : Δ ⊢c A)
    → (ap : Δ ≫ A ⇘ A%)
    → (⊢e : 𝕣 Δ ⊢ τ A% ⇒ e ⇒ A' ↡ ∞)
    → Δ ⊢ B ≤⁺ Σ ⊣ Ψ ↪ D ↡ j
    → Δ ⊢ (A `→ B) ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ A% `→ D ↡ 𝕔 j

  s-term-o :
      (opnA : Δ ⊢o A)
    → (⊢e : 𝕣 Δ ⊢ □ ⇒ e ⇒ C ↡ Z)
    → (ss : Δ ⊢ C ⌞ ≤⁻ ⌝ A ⊣ Ω)
    → Ω ⊢ B ≤⁺ Σ ⊣ Ψ ↪ D ↡ j
    → Δ ⊢ A `→ B ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D ↡ 𝕚 j

  s-∀l-y-𝕚 :
      (pk : A ~pk'~ ([ e' ]↝ Σ') w/ #0 ↬ B ↡ (𝕚 j'))
    → Δ ,= B ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,= B ↪ C' `→ D' ↡ (𝕚 j')
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upj : ↑tyʲ0 j ⇘ j')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D ↡ 𝕚 j

  s-∀l-n-y-𝕚 :
      (¬pk : ¬ (A ~pk~ ([ e' ]↝ Σ') w/ #0))
    → Δ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,= B ↪ C' `→ D' ↡ 𝕚 j'
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upj : ↑tyʲ0 j ⇘ j')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D ↡ 𝕚 j

  s-∀l-n-n-𝕚 :
      (¬pk : ¬ (A ~pk~ ([ e' ]↝ Σ') w/ #0))
    → Δ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,^ ↪ C' `→ D' ↡ 𝕚 j'
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upj : ↑tyʲ0 j ⇘ j')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D ↡ 𝕚 j

  s-∀l-y-𝕔 :
      (pk : A ~pk'~ ([ e' ]↝ Σ') w/ #0 ↬ B ↡ (𝕔 j'))
    → Δ ,= B ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,= B ↪ C' `→ D' ↡ (𝕔 j')
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upj : ↑tyʲ0 j ⇘ j')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D ↡ 𝕔 j

  s-∀l-n-y-𝕔 :
      (¬pk : ¬ (A ~pk~ ([ e' ]↝ Σ') w/ #0))
    → Δ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,= B ↪ C' `→ D' ↡ 𝕔 j'
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upj : ↑tyʲ0 j ⇘ j')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D ↡ 𝕔 j

  s-∀l-n-n-𝕔 :
      (¬pk : ¬ (A ~pk~ ([ e' ]↝ Σ') w/ #0))
    → Δ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,^ ↪ C' `→ D' ↡ 𝕔 j'
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upj : ↑tyʲ0 j ⇘ j')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D ↡ 𝕔 j

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
