module Implicit.Complete where

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

  ≊-right : Γ ∋ X := A
          → Γ ⊢ A ≊ ‶ X

  ≊-arr : Γ ⊢ A' ≊ A
        → Γ ⊢ B ≊ B'
        → Γ ⊢ A `→ B ≊ A' `→ B'

  ≊-∀ : Γ ,∙ ⊢ A ≊ B
      → Γ ⊢ `∀ A ≊ `∀ B

postulate
  ≊-weaken,0 : Γ , T ⊢ A ≊ B
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
    → (ext : Γ ⊆ Γ')
    → (sub : Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Γ' ↪ B)
    → (sim : Γ ⊢ A ≊ B)
    → JustSub Γ' Σ A

complete : Γ ⊢ j # e ⦂ A
         → Γ ⊢ ⟨ j , A ⟩ ~ Σ
         → JustTyp Γ Σ e A

complete-∞ : Γ ⊢ ∞ # e ⦂ A
           → Γ ⊢ τ A ⇒ e ⇒ A
complete-∞ ⊢e with complete ⊢e ~∞
... | typs ⊢e₁ sim with ⊢id0 ⊢e₁
... | refl = ⊢e₁

complete-≤ : Γ ⊢ j # A ≤ B
           → Γ ⊢ ⟨ j , B ⟩ ~ Σ
            --  → Ψ ⊆ (𝕎 Γ) x (exvar(Ψ) in B) × someCon(j) -- w
--            → (Γ ⊆ Δ) × (Exvar Γ B) ×
            → JustSub Γ Σ A

complete (⊢lit cloΣ) ~Z = typs (⊢lit cloΣ) ≊-int
complete (⊢var cloΣ x∈Γ) ~Z = typs (⊢var cloΣ x∈Γ) ≊-refl
complete (⊢ann ⊢e) ~Z with complete ⊢e ~∞
... | typs ⊢e₁ sim = typs (⊢ann ⊢e₁) ≊-refl
complete (⊢lam₁ ⊢e) ~∞ with complete ⊢e ~∞
... | typs ⊢e₁ sim = typs (⊢lam₁ ⊢e₁) (≊-arr ≊-refl (≊-weaken,0 sim))
complete (⊢lam₂ ⊢e) (~I ⊢e₁ j~Σ) with complete ⊢e (~weaken,0 j~Σ {!!})
... | typs ⊢e₂ sim = typs (⊢lam₂ ⊢e₁ {!!} ⊢e₂) (≊-arr ≊-refl (≊-weaken,0 sim))
complete (⊢app₁ ⊢e ⊢e₁) j~Σ with complete ⊢e (~C (complete-∞ ⊢e₁) j~Σ)
... | typs ⊢e₂ (≊-right x) = {!!}
... | typs ⊢e₂ (≊-arr sim sim₁) = typs (⊢app ⊢e₂) sim₁
complete (⊢app₂ ⊢e ⊢e₁) j~Σ = {!!}
complete (⊢sub ⊢e B≤A j≢Z) j~Σ = typs {! !} {!!}
complete (⊢tabs ⊢e) ~Z with complete ⊢e ~Z
... | typs ⊢e₁ sim = typs (⊢tabs ⊢e₁) (≊-∀ sim)

{-
complete (⊢lam₂ ⊢e) cloΓ clo-e (⊢c-arr cloA cloA₁) (~I ⊢e₁ j~Σ) with complete ⊢e (clo-S, cloΓ cloA) {!!} (⊢c-weaken,0 cloA₁) (~weaken,0 j~Σ {!!})
... | typs ⊢e₂ sim = typs (⊢lam₂ ⊢e₁ {!!} ⊢e₂) (≊-arr ≊-refl (≊-weaken0 sim))
complete (⊢app₁ ⊢e ⊢e₁) cloΓ clo-e cloA j~Σ with complete ⊢e cloΓ {!!} (⊢c-arr {!!} cloA) (~C {!!} j~Σ)
... | typs ⊢e' (≊-right x) = {!!}
... | typs ⊢e' (≊-arr sim sim₁) = typs (⊢app ⊢e') sim₁
complete (⊢app₂ ⊢e ⊢e₁) cloΓ clo-e cloA j~Σ with complete ⊢e cloΓ {!!} (⊢c-arr {!!} cloA) (~I {!!} {!!})
... | typs ⊢e' (≊-right x) = {!!}
... | typs ⊢e₂ (≊-arr sim sim₁) = typs (⊢app ⊢e₂) sim₁
complete (⊢sub ⊢e B≤A j≢Z) cloΓ clo-e cloA j~Σ = {!!}
complete (⊢tabs ⊢e) cloΓ clo-e cloA ~Z = {!!}
-}
