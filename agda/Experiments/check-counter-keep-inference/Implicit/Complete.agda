module Implicit.Complete where

open import Implicit.Common
open import Implicit.Decl renaming (_:=_∈_ to _:=_∈d_)
open import Implicit.Algo renaming (_:=_∈_ to _:=_∈a_)
open import Implicit.Algo.Subsumption
open import Implicit.Algo.Postulates

infix 3 _⊢_~_

data _⊢_~_ : Env n m → Counter × Type m → Context n m × Type m → Set

data _⊢_~_ where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ ⟨ □ , A ⟩

  ~∞ : ∀ {Γ : Env n m} {A B}
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ ⟨ τ A , B ⟩

  ~I : ∀ {Γ : Env n m} {j A B B' Σ e}
    → (⊢e : Γ ⊢ □ ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ ⟨ Σ , B' ⟩ 
    → Γ ⊢ ⟨ I j , A `→ B ⟩ ~ ⟨ ([ e ]↝ Σ) , A `→ B' ⟩

  ~C : ∀ {Γ : Env n m} {j A B B' D Σ e}
    → (⊢e : Γ ⊢ τ A ⇒ e ⇒ D)
    → Γ ⊢ ⟨ j , B ⟩ ~ ⟨ Σ , B ⟩
    → Γ ⊢ ⟨ C j , A `→ B ⟩ ~ ⟨ ([ e ]↝ Σ) , A `→ B' ⟩ -- not sure the input

postulate

  ⊢d→⊢c : ∀ {Γ : Env n m} {e A j}
    → Γ ⊢ j # e ⦂ A
    → 𝕎 Γ ⊢c A

  ⊢m-w : ∀ {Γ : Env n m} {A e j}
    → Γ ⊢ j # e ⦂ A
    → 𝕄 (𝕎 Γ) ⊢ j # e ⦂ A

complete : ∀ {Γ : Env n m} {Σ j e A A'}
  → Γ ⊢ j # e ⦂ A
  → Γ ⊢ ⟨ j , A ⟩ ~ ⟨ Σ , A' ⟩
  → Γ ⊢ Σ ⇒ e ⇒ A'

complete-inf : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ Z # e ⦂ A
  → Γ ⊢ □ ⇒ e ⇒ A
complete-inf ⊢e = complete ⊢e ~Z  

complete-chk : ∀ {Γ : Env n m} {e A B}
  → Γ ⊢ ∞ # e ⦂ A
  → Γ ⊢ τ A ⇒ e ⇒ B
complete-chk ⊢e = complete ⊢e ~∞

complete ⊢lit ~Z = ⊢lit
complete (⊢var x) ~Z = ⊢var x
complete (⊢ann ⊢e) ~Z = ⊢ann (complete-chk ⊢e)
complete (⊢lam₁ ⊢e) ~∞ = ?
complete (⊢lam₂ ⊢e) ~j = {!!}
complete (⊢app₁ ⊢e ⊢e₁) ~j = {!!}
complete (⊢app₂ ⊢e ⊢e₁) ~j = {!!}
complete (⊢sub ⊢e B≤A j≢Z) ~j = {!!}
complete (⊢tabs ⊢e) ~j = {!!}
