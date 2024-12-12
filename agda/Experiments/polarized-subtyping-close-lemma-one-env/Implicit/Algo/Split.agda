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

private variable
  x : Fin n
  e e' : Term n m
  e̅ e̅' : Apps n m
  Σ Σ' : Context n m
  A : Type m

infix 3 _↑tmᵃ_⇘_
data _↑tmᵃ_⇘_ : Apps n m → Fin (1 + n) → Apps (1 + n) m → Set where
  nil : (Apps n m ∋⦂ nil) ↑tmᵃ x ⇘ nil
  _∷a_ :
      e ↑tm x ⇘ e'
    → e̅ ↑tmᵃ x ⇘ e̅'
    → (e ∷a e̅) ↑tmᵃ x ⇘ (e' ∷a e̅')

infix 4 ↑tmᵃ0_⇘_
↑tmᵃ0_⇘_ : Apps n m → Apps (1 + n) m → Set
↑tmᵃ0_⇘_ e = _↑tmᵃ_⇘_ e #0

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

infix 4 ⟦_⟧⇒⟦_,_⟧
data ⟦_⟧⇒⟦_,_⟧ : Context n m → Apps n m → Context n m → Set where

  none-□ : ⟦ (Context n m ∋⦂ □) ⟧⇒⟦ nil , □ ⟧
  
  none-τ : ⟦ (Context n m ∋⦂ τ A) ⟧⇒⟦ nil , τ A ⟧
  
  have-e : ⟦ Σ ⟧⇒⟦ e̅ , Σ' ⟧
         → ⟦ [ e ]↝ Σ ⟧⇒⟦ e ∷a e̅ , Σ' ⟧


infix 4 _⊕_:=_
data _⊕_:=_ : Apps n m → Context n m → Context n m → Set where

  ⊕nil : nil ⊕ Σ := Σ
  
  ⊕cons-e : e̅ ⊕ Σ := Σ'
          → (e ∷a e̅) ⊕ Σ := [ e ]↝ Σ'
