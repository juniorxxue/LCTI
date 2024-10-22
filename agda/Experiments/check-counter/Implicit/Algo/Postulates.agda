module Implicit.Algo.Postulates where

open import Implicit.Common
open import Implicit.Algo


infix 4 ⟦_⟧⇒⟦_,_⟧

data ⟦_⟧⇒⟦_,_⟧ : Context n m → Apps n m → Context n m → Set where

  none-□ :
      ⟦ (Context n m ∋⦂ □) ⟧⇒⟦ nil , □ ⟧

  none-τ : ∀ {A}
    → ⟦ (Context n m ∋⦂ τ A) ⟧⇒⟦ nil , τ A ⟧

  have-e : ∀ {Σ Σ' : Context n m} {e es}
    → ⟦ Σ ⟧⇒⟦ es , Σ' ⟧
    → ⟦ [ e ]↝ Σ ⟧⇒⟦ e ∷a es , Σ' ⟧

postulate
  Σsplit-weaken0 : ∀ {Σ : Context n m} {a̅ Σ'}
    → ⟦ Σ ⟧⇒⟦ a̅ , Σ' ⟧
    → ⟦ ↑Σ0 Σ ⟧⇒⟦ up0 a̅ , ↑Σ0 Σ' ⟧

infix 4 _⊕_:=_

data _⊕_:=_ : Apps n m → Context n m → Context n m → Set where

  ⊕nil : ∀ {Σ : Context n m}
    → nil ⊕ Σ := Σ

  ⊕cons-e : ∀ {Σ : Context n m} {e a̅ Σ'}
    → a̅ ⊕ Σ := Σ'
    → (e ∷a a̅) ⊕ Σ := [ e ]↝ Σ'
    
postulate

  ⊕-weaken0 : ∀ {Σ : Context n m} {es Σ'}
    → es ⊕ Σ' := Σ
    → (up0 es) ⊕ (↑Σ0 Σ') := ↑Σ0 Σ

  s-weaken0 : ∀ {Ψ Ψ' : SEnv n m} {Σ A B B'}
    → Ψ ⊢ B ≤ Σ ⊣ Ψ' ↪ B'
    → Ψ , A ⊢ B ≤ ↑Σ0 Σ ⊣ Ψ' , A ↪ B'

  s-strengthen0 : ∀ {Ψ Ψ' : SEnv n m} {Σ A B B'}
    → Ψ , A ⊢ B ≤ ↑Σ0 Σ ⊣ Ψ' , A ↪ B'
    → Ψ ⊢ B ≤ Σ ⊣ Ψ' ↪ B'

  s-closed-r : ∀ {Ψ : SEnv n m} {Γ A B Σ}
    → 𝕎 Γ ⊢ A ≤ Σ ⊣ Ψ ↪ B
    → 𝕎 Γ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ B

  s-closed-l : ∀ {Ψ : SEnv n m} {Γ A B Σ}
    → Ψ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ B
    → 𝕎 Γ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ B

  𝕎-open : ∀ {Γ : Env n m} {A}
    → ¬ (𝕎 Γ ⊢o A)  

  ⊢a→⊢c : ∀ {Γ : Env n m} {Σ e A}
    → Γ ⊢ Σ ⇒ e ⇒ A
    → 𝕎 Γ ⊢c A

  ⊢a→⊢c-τ : ∀ {Γ : Env n m} {e A B}
    → Γ ⊢ τ B ⇒ e ⇒ A
    → 𝕎 Γ ⊢c B

  ⊢a→⊢c-weaken : ∀ {Γ : Env n m} {Σ e A B}
    → Γ , B ⊢ Σ ⇒ e ⇒ A
    → 𝕎 Γ ⊢c A

