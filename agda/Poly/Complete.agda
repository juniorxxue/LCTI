module Poly.Complete where

open import Poly.Common
open import Poly.Decl
open import Poly.Algo

infix 3 _⊢_~_

data _⊢_~_ : Env n m → Counter × Type m → Context n m → Set

data _⊢_~_ where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~S⇒ : ∀ {Γ : Env n m} {j A B Σ e}
    → Γ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ S j , A `→ B ⟩ ~ ([ e ]↝ Σ)

complete : ∀ {Γ : Env n m} {Σ j e A}
  → Γ ⊢ j # e ⦂ A
  → Γ ⊢ ⟨ j , A ⟩ ~ Σ
  → Γ ⊢ Σ ⇒ e ⇒ A
  
complete-inf : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ Z # e ⦂ A
  → Γ ⊢ □ ⇒ e ⇒ A
complete-inf ⊢e = complete ⊢e ~Z  

complete-chk : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ ∞ # e ⦂ A
  → Γ ⊢ τ A ⇒ e ⇒ A
complete-chk ⊢e = complete ⊢e ~∞

complete ⊢lit j~Σ = {!!}
complete (⊢var x) j~Σ = {!!}
complete (⊢ann ⊢e) j~Σ = {!!}
complete (⊢lam₁ ⊢e) j~Σ = {!!}
complete (⊢lam₂ ⊢e) j~Σ = {!!}
complete (⊢app₁ ⊢e ⊢e₁) j~Σ = {!!}
complete (⊢app₂ ⊢e ⊢e₁) j~Σ = {!!}
complete (⊢sub ⊢e B≤A j≢Z) j~Σ = {!!}
complete (⊢tabs₁ ⊢e) j~Σ = {!!}
complete (⊢tapp ⊢e) j~Σ = {!!}
