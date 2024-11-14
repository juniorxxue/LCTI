module Implicit.Algo.Split where

open import Implicit.Language
open import Implicit.Algo.Syntax

data Apps : ℕ → ℕ → Set where
  nil  : Apps n m
  _∷a_ : Term n m → Apps n m → Apps n m

data AppsType : ℕ → Set where
  nil  : AppsType m
  _∷a_ : Type m → AppsType m → AppsType m
  `∀_  : AppsType (1 + m) → AppsType m

infix 4 ⟦_,_⟧→⟦_,_,_,_⟧

data ⟦_,_⟧→⟦_,_,_,_⟧ : Context n m → Type m → Apps n m → Context n m → AppsType m → Type m → Set where

  none-□ : ∀ {A}
    → ⟦ (Context n m ∋⦂ □) , A ⟧→⟦ nil , □ , nil , A ⟧

  none-τ : ∀ {A B}
    → ⟦ (Context n m ∋⦂ τ A) , B ⟧→⟦ nil , τ A , nil , B ⟧

  have-e : ∀ {Σ : Context n m} {e A B e̅ A' B' B̅}
    → ⟦ Σ , B ⟧→⟦ e̅ , A' , B̅ , B' ⟧
    → ⟦ ([ e ]↝ Σ) , A `→ B ⟧→⟦ e ∷a e̅ , A' , A ∷a B̅ , B' ⟧

infix 4 ⟦_,_⟧→s⟦_,_⟧
data ⟦_,_⟧→s⟦_,_⟧ : Context n m → Type m → Context n m → Type m → Set where

  none-□ : ∀ {A}
    → ⟦ (Context n m ∋⦂ □) , A ⟧→s⟦ □ , A ⟧

  none-τ : ∀ {A B}
    → ⟦ (Context n m ∋⦂ τ A) , B ⟧→s⟦ τ A , B ⟧

  have-e : ∀ {Σ : Context n m} {e A B Σ' B'}
    → ⟦ Σ , B ⟧→s⟦ Σ' , B' ⟧
    → ⟦ ([ e ]↝ Σ) , A `→ B ⟧→s⟦ Σ' , B' ⟧
