module Implicit.Algo.Base where

open import Implicit.Language

open import Implicit.Algo.Syntax public
open import Implicit.Algo.Shift public
open import Implicit.Algo.Subst public
open import Implicit.Algo.OpenClose public
open import Implicit.Algo.Lookup public
open import Implicit.Algo.Extension public
open import Implicit.Algo.Split public

private variable
  Ψ Ψ' Ψ₁ Ψ₂ Ψ₃ : SEnv n m
  Γ : Env n m
  Σ Σ' : Context n m
  e e₁ e₂ g e' : Term n m
  A B C D A' C' D' : Type m
  x : Fin n
  X k : Fin m

infix 8 𝕎 𝕄

𝕎 : Env n m → SEnv n m
𝕎 ∅ = ∅
𝕎 (Γ , A) = 𝕎 Γ , A
𝕎 (Γ ,∙) = 𝕎 Γ ,∙
𝕎 (Γ ,= A) = 𝕎 Γ ,= A

𝕄 : SEnv n m → Env n m
𝕄 ∅ = ∅
𝕄 (Ψ , A) = 𝕄 Ψ , A
𝕄 (Ψ ,∙) = 𝕄 Ψ ,∙
𝕄 (Ψ ,^) = 𝕄 Ψ ,= Int
𝕄 (Ψ ,= A) = 𝕄 Ψ ,= A

infix 3 _⊢_⇒_⇒_
infix 3 _⊢_≤⁺_⊣_↪_
infix 3 _⊢_≤⁻_⊣_↪_

data _⊢_⇒_⇒_ : Env n m → Context n m → Term n m → Type m → Set
data _⊢_≤⁺_⊣_↪_ : SEnv n m → Type m → Context n m → SEnv n m → Type m → Set
data _⊢_≤⁻_⊣_↪_ : SEnv n m → Type m → Context n m → SEnv n m → Type m → Set

data _⊢_⇒_⇒_ where

  ⊢lit : ∀ {num : ℕ}
    → Γ ⊢ □ ⇒ lit num ⇒ Int

  ⊢var :
      (x∈Γ : Γ ∋ x ⦂ A)
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
    → (s : 𝕎 Γ ⊢ A ≤⁺ Σ ⊣ 𝕎 Γ ↪ B)
    → Γ ⊢ Σ ⇒ g ⇒ B
    
  ⊢tabs :
      Γ ,∙ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ □ ⇒ Λ e ⇒ `∀ A

data _⊢_≤⁺_⊣_↪_ where

  s+-int :
      Ψ ⊢ Int ≤⁺ τ Int ⊣ Ψ ↪ Int

  s+-empty :
      (cloA : Ψ ⊢c A)
    → Ψ ⊢ A ≤⁺ □ ⊣ Ψ ↪ A

  s+-var :
      (cloX : Ψ ⊢c (‶ X))
    → Ψ ⊢ (‶ X) ≤⁺ τ (‶ X) ⊣ Ψ ↪ ‶ X

  s+-ex-l^ :
      (cloA : Ψ ⊢c A)
    → (x-in : X ^∈ Ψ)
    → (inst : [ A / X ] Ψ ⟹ Ψ')
    → Ψ ⊢ ‶ X ≤⁺ τ A ⊣ Ψ' ↪ A
 
  s+-ex-l= :
      (cloA : Ψ ⊢c A)
    → (x-in : X := B ∈ Ψ)
    → Ψ ⊢ B ≤⁺ τ A ⊣ Ψ' ↪ A'
    → Ψ ⊢ ‶ X ≤⁺ τ A ⊣ Ψ' ↪ A

  s+-ex-r= :
      (cloA : Ψ ⊢c A)
    → (x-in : X := B ∈ Ψ)
    → Ψ ⊢ A ≤⁺ τ B ⊣ Ψ' ↪ A'
    → Ψ ⊢ A ≤⁺ τ (‶ X) ⊣ Ψ' ↪ (‶ X)

  s+-arr :
      (cloC : Ψ₁ ⊢c C)
    → (cloD : Ψ₁ ⊢c D)
    → (s : Ψ₁ ⊢ C ≤⁻ τ A ⊣ Ψ₂ ↪ A')
    → Ψ₂ ⊢ B ≤⁺ τ D ⊣ Ψ₃ ↪ D'
    → Ψ₁ ⊢ A `→ B ≤⁺ τ (C `→ D) ⊣ Ψ₃ ↪ (C `→ D)

  s+-term-c :
      (cloA : Ψ ⊢c A)
    → (cloΣ : Ψ ⊢cᶜ Σ)
    → (⊢e : (𝕄 Ψ) ⊢ τ A ⇒ e ⇒ A')
    → Ψ ⊢ B ≤⁺ Σ ⊣ Ψ' ↪ D
    → Ψ ⊢ (A `→ B) ≤⁺ ([ e ]↝ Σ) ⊣ Ψ' ↪ A' `→ D

  s+-term-o :
      (opnA : Ψ ⊢o A)
    → (cloΣ : Ψ ⊢cᶜ Σ)    
    → (⊢e : (𝕄 Ψ) ⊢ □ ⇒ e ⇒ C)
    → (s : Ψ ⊢ C ≤⁻ τ A ⊣ Ψ₁ ↪ A')
    → Ψ₁ ⊢ B ≤⁺ Σ ⊣ Ψ₂ ↪ D
    → Ψ ⊢ A `→ B ≤⁺ ([ e ]↝ Σ) ⊣ Ψ₂ ↪ C `→ D

  s+-∀ :
      (cloB : Ψ ⊢c `∀ B)
    → Ψ ,∙ ⊢ A ≤⁺ τ B ⊣ Ψ' ,∙ ↪ C
    → Ψ ⊢ `∀ A ≤⁺ τ (`∀ B) ⊣ Ψ' ↪ `∀ C

  s+-∀l :
      (cloΣ : Ψ ⊢cᶜ Σ)
    → Ψ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ' ,= B ↪ (C `→ D)
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (st₁ : ⟦ B ⟧ C ⇘ C')
    → (st₂ : ⟦ B ⟧ D ⇘ D')
    → Ψ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ' ↪ C' `→ D'


data _⊢_≤⁻_⊣_↪_ where
  s--int :
      Ψ ⊢ Int ≤⁻ τ Int ⊣ Ψ ↪ Int

  s--var :
      (cloX : Ψ ⊢c (‶ X))
    → Ψ ⊢ (‶ X) ≤⁻ τ (‶ X) ⊣ Ψ ↪ ‶ X

  s--ex-r^ :
      (cloA : Ψ ⊢c A)
    → (x-in : X ^∈ Ψ)
    → (inst : [ A / X ] Ψ ⟹ Ψ')
    → Ψ ⊢ A ≤⁻ τ (‶ X) ⊣ Ψ' ↪ ‶ X

  s--ex-l= :
      (cloA : Ψ ⊢c A)
    → (x-in : X := B ∈ Ψ)
    → Ψ ⊢ B ≤⁻ τ A ⊣ Ψ' ↪ A'
    → Ψ ⊢ ‶ X ≤⁻ τ A ⊣ Ψ' ↪ A

  s--ex-r= :
      (cloA : Ψ ⊢c A)
    → (x-in : X := B ∈ Ψ)
    → Ψ ⊢ A ≤⁻ τ B ⊣ Ψ' ↪ A'
    → Ψ ⊢ A ≤⁻ τ (‶ X) ⊣ Ψ' ↪ (‶ X)

  s--arr :
      (cloA : Ψ₁ ⊢c A)
    → (cloB : Ψ₁ ⊢c B)
    → (s : Ψ₁ ⊢ C ≤⁺ τ A ⊣ Ψ₂ ↪ A')
    → Ψ₂ ⊢ B ≤⁻ τ D ⊣ Ψ₃ ↪ D'
    → Ψ₁ ⊢ A `→ B ≤⁻ τ (C `→ D) ⊣ Ψ₃ ↪ (C `→ D)

  s--∀ :
      (cloA : Ψ ⊢c `∀ A)
    → Ψ ,∙ ⊢ A ≤⁻ τ B ⊣ Ψ' ,∙ ↪ C
    → Ψ ⊢ `∀ A ≤⁻ τ (`∀ B) ⊣ Ψ' ↪ `∀ C
