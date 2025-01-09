module Implicit.Complete2 where
-- in the theorem statement, some closeness condition will be discarded

open import Implicit.Language
open import Implicit.Decl renaming (find to d-find)
open import Implicit.Algo
open import Implicit.Algo.Properties.Subsumption

infix 3 _⊢_~_

data _⊢_~_ : Env n m → Counter × Type m → Context n m → Set where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~I : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ □ ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ~ ([ e ]↝ Σ)

  ~C : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ τ A ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕔 j , A `→ B ⟩ ~ ([ e ]↝ Σ)

postulate
  ~weaken,0 : Γ ⊢ ⟨ j , B ⟩ ~ Σ
            → ↑tmᶜ0 Σ ⇘ Σ'
            → Γ , A ⊢ ⟨ j , B ⟩ ~ Σ'

infix 3 _⊢_≊_
data _⊢_≊_ : Env n m → Type m → Type m → Set where

  ≊-int : Γ ⊢ Int ≊ Int

  ≊-var : Γ ⊢ ‶ X ≊ ‶ X

  ≊-left : Γ ∋ X := A
         → Γ ⊢ ‶ X ≊ A

{-
  ≊-right : Γ ∋ X := A
          → Γ ⊢ A ≊ ‶ X
-}

  ≊-arr : Γ ⊢ A' ≊ A
        → Γ ⊢ B ≊ B'
        → Γ ⊢ A `→ B ≊ A' `→ B'

  ≊-∀ : Γ ,∙ ⊢ A ≊ B
      → Γ ⊢ `∀ A ≊ `∀ B

postulate
  ≊-weaken0 : Γ , T ⊢ A ≊ B
            → Γ ⊢ A ≊ B

≊-refl : Γ ⊢ A ≊ A
≊-refl {A = Int} = ≊-int
≊-refl {A = ‶ X} = ≊-var
≊-refl {A = A `→ A₁} = ≊-arr ≊-refl ≊-refl
≊-refl {A = `∀ A} = ≊-∀ ≊-refl

data JustTyp (Γ : Env n m) (Σ : Context n m) (e : Term n m) (A : Type m) : Set where
  typs : ∀ {B}
    → (⊢e : Γ ⊢ Σ ⇒ e ⇒ B)
    → (sim : Γ ⊢ A ≊ B)
    → JustTyp Γ Σ e A

data JustSub (Γ' : Env n m) (Σ : Context n m) (A : Type m) : Set where
  subs : ∀ {Γ B}
    → (ext : Γ ⊆ Γ') -- this will be changed later
    → (sub : Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Γ' ↪ B)
    → (sim : Γ ⊢ A ≊ B)
    → JustSub Γ' Σ A

complete : ∀ {Γ : Env n m} {Σ j e A}
  → Γ ⊢ j # e ⦂ A
  → Closed Γ
  → Γ ⊢ ⟨ j , A ⟩ ~ Σ
  → JustTyp Γ Σ e A

complete-≤ : Γ ⊢ j # A ≤ B
           → Γ ⊢ ⟨ j , B ⟩ ~ Σ
            → JustSub Γ Σ A

complete ⊢lit cloΓ j~Σ = {!!}
complete (⊢var x∈Γ) cloΓ j~Σ = {!!}
complete (⊢ann ⊢e) cloΓ j~Σ = {!!}
complete (⊢lam₁ ⊢e) cloΓ j~Σ = {!!}
complete (⊢lam₂ ⊢e) cloΓ j~Σ = {!!}
complete (⊢app₁ ⊢e ⊢e₁) cloΓ j~Σ = {!!}
complete (⊢app₂ ⊢e ⊢e₁) cloΓ j~Σ = {!!}
complete (⊢sub ⊢e B≤A j≢Z) cloΓ j~Σ = {!!}
complete (⊢tabs ⊢e) cloΓ j~Σ = {!!}
