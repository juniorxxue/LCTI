module Implicit.Algo.Constructs.Split where

open import Implicit.Language.All
open import Implicit.Algo.Constructs.Syntax

infix 4 ⟦_,_⟧→⟦_,_⟧
data ⟦_,_⟧→⟦_,_⟧ : Context n m → Type m → Context n m → Type m → Set where

  none-□ : ∀ {A}
    → ⟦ (Context n m ∋⦂ □) , A ⟧→⟦ □ , A ⟧

  none-τ : ∀ {A B}
    → ⟦ (Context n m ∋⦂ τ A) , B ⟧→⟦ τ A , B ⟧

  have-e : ∀ {Σ : Context n m} {e A B Σ' B'}
    → ⟦ Σ , B ⟧→⟦ Σ' , B' ⟧
    → ⟦ ([ e ]↝ Σ) , A `→ B ⟧→⟦ Σ' , B' ⟧

-- share the same argument, however first end with □, second end with any Σ'
-- used for proving general subsumption
infix 3 _≊_
data _≊_ : Context n m → Context n m → Set where
  ≊Z : (Context n m ∋⦂ □) ≊ τ A
  ≊S : Σ ≊ Σ'
     → [ e ]↝ Σ ≊ [ e ]↝ Σ'
