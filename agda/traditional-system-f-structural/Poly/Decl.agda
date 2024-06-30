module Poly.Decl where

open import Poly.Common

data Counter : Set where
  Z  : Counter
  ∞  : Counter
  S  : Counter → Counter
  Sτ : Counter → Counter

data NonZ : Counter → Set where
  nz-∞ : NonZ ∞
  nz-S : ∀ {j} → NonZ (S j)
  nz-Sτ : ∀ {j} → NonZ (Sτ j)

private
  variable
    Γ : Env n m

infix 3 _⊢m_#_
data _⊢m_#_ : Env n m → Counter → Type m → Set where
  s-zero : ∀ {A}
    → Γ ⊢m Z # A
  s-inf : ∀ {A}
    → Γ ⊢m ∞ # A
  s-arr : ∀ {A B j}
    → Γ ⊢m j # B
    → Γ ⊢m S j # A `→ B
  s-∀ : ∀ {A j}
    → Γ ,∙ ⊢m j # A
    → Γ ⊢m (Sτ j) # `∀ A

infix 3 _⊢_#_⦂_
data _⊢_#_⦂_ : Env n m → Counter → Term n m → Type m → Set where
  ⊢lit : ∀ {i} → Γ ⊢ Z # (lit i) ⦂ Int
  ⊢var : ∀ {x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢ Z # ` x ⦂ A
  ⊢ann : ∀ {e A}
    → Γ ⊢ ∞ # e ⦂ A
    → Γ ⊢ Z # (e ⦂ A) ⦂ A
  ⊢lam₁ : ∀ {e A B}
    → Γ , A ⊢ ∞ # e ⦂ B
    → Γ ⊢ ∞ # ƛ e ⦂ A `→ B
  ⊢lam₂ : ∀ {e j A B}
    → Γ , A ⊢ j # e ⦂ B
    → Γ ⊢ S j # ƛ e ⦂ A `→ B
  ⊢app₁ : ∀ {e₁ e₂ A B}
    → Γ ⊢ Z # e₁ ⦂ A `→ B
    → Γ ⊢ ∞ # e₂ ⦂ A
    → Γ ⊢ Z # e₁ · e₂ ⦂ B
  ⊢app₂ : ∀ {e₁ e₂ j A B}
    → Γ ⊢ S j # e₁ ⦂ A `→ B
    → Γ ⊢ Z # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B
  ⊢sub : ∀ {e j A}
    → Γ ⊢ Z # e ⦂ A
    → Γ ⊢m j # A
    → (j≢Z : NonZ j)
    → Γ ⊢ j # e ⦂ A
  ⊢tabs₁ : ∀ {e A}
    → Γ ,∙ ⊢ Z # e ⦂ A
    → Γ ⊢ Z # Λ e ⦂ `∀ A
  ⊢tabs₂ : ∀ {e A}
    → Γ ,∙ ⊢ ∞ # e ⦂ A
    → Γ ⊢ ∞ # Λ e ⦂ `∀ A
  ⊢tabs₃ : ∀ {e j A}
    → Γ ,∙ ⊢ j # e ⦂ A
    → Γ ⊢ Sτ j # Λ e ⦂ `∀ A
  ⊢tapp : ∀ {e j A B B'}
    → Γ ⊢ Sτ j # e ⦂ `∀ B
    → (st : [ A ]ˢ B ⇨ B')
    → Γ ⊢ j # e [ A ] ⦂ B'


⊢sub' : ∀ {e j A}
  → Γ ⊢ Z # e ⦂ A
  → Γ ⊢m j # A
  → Γ ⊢ j # e ⦂ A
⊢sub' {j = Z} ⊢e jA = ⊢e
⊢sub' {j = ∞} ⊢e jA = ⊢sub ⊢e jA nz-∞
⊢sub' {j = S j} ⊢e jA = ⊢sub ⊢e jA nz-S
⊢sub' {j = Sτ j} ⊢e jA = ⊢sub ⊢e jA nz-Sτ
  
