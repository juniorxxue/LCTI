module Implicit.Algo2Interm.Context2Counter where

open import Implicit.Language.All
open import Implicit.Interm.All
open import Implicit.Algo.All
open import Implicit.Algo2Interm.AlgoCounter.All

infix 3 _⊢_~t_
data _⊢_~t_ : Env n m → Counter × Type m → Context n m → Set where

  ~tZ : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~t □

  ~t∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~t τ A

  ~tI : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ Z # e ⦂ A)
    → Γ ⊢ ⟨ j , B ⟩ ~t Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ~t ([ e ]↝ Σ)

  ~tC : ∀ {Γ : Env n m} {j A B Σ e}
    (⊢e : Γ ⊢ ∞ # e ⦂ A)
    → Γ ⊢ ⟨ j , B ⟩ ~t Σ
    → Γ ⊢ ⟨ 𝕔 j , A `→ B ⟩ ~t ([ e ]↝ Σ)

infix 3 _⊢_~s_
data _⊢_~s_ : Env n m → Counter × Type m → Context n m → Set where

  ~sZ : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~s □

  ~s∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~s τ A

  ~sI : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : 𝕣 Γ ⊢ Z # e ⦂ A)
    → Γ ⊢ ⟨ j , B ⟩ ~s Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ~s ([ e ]↝ Σ)

  ~sC : ∀ {Γ : Env n m} {j A B Σ e}
    (⊢e : 𝕣 Γ ⊢ ∞ # e ⦂ A)
    → Γ ⊢ ⟨ j , B ⟩ ~s Σ
    → Γ ⊢ ⟨ 𝕔 j , A `→ B ⟩ ~s ([ e ]↝ Σ)


NonEmpty-NonZ : NonEmpty Σ
              → Γ ⊢ ⟨ j , A ⟩ ~t Σ
              → NonZ j
NonEmpty-NonZ ne-τ ~t∞ = nz-∞
NonEmpty-NonZ ne-app (~tI ⊢e j~Σ) = nz-I
NonEmpty-NonZ ne-app (~tC ⊢e j~Σ) = nz-C
