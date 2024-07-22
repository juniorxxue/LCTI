module Poly.Complete where

open import Poly.Common
open import Poly.Decl
open import Poly.Algo
open import Poly.Algo.Subsumption

infix 3 _⊢_~_

data _⊢_~_ : Env n m → Counter × Type m → Context n m → Set

data _⊢_~_ where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~S : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ □ ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ S j , A `→ B ⟩ ~ ([ e ]↝ Σ) -- got a deeper undersantding of it, how the S will be eliminated, at least in two places in STLC

postulate
  ~weaken0 : ∀ {Γ : Env n m} {Σ A B j}
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ , A ⊢ ⟨ j , B ⟩ ~ ↑Σ0 Σ
{-    
  subsumption0 : ∀ {Γ : Env n m} {Σ A e}
    → Γ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ A ≤ Σ
    → Γ ⊢ Σ ⇒ e ⇒ A
-}    

complete : ∀ {Γ : Env n m} {Σ j e A}
  → Γ ⊢ j # e ⦂ A
  → Γ ⊢ ⟨ j , A ⟩ ~ Σ
  → Γ ⊢ Σ ⇒ e ⇒ A

complete-≤ : ∀ {Γ : Env n m} {Σ j A}
--  → Γ ⊢m j # A
  → Γ ⊢ ⟨ j , A ⟩ ~ Σ
  → Γ ⊢ A ≤ Σ
  
complete-inf : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ Z # e ⦂ A
  → Γ ⊢ □ ⇒ e ⇒ A
complete-inf ⊢e = complete ⊢e ~Z  

complete-chk : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ ∞ # e ⦂ A
  → Γ ⊢ τ A ⇒ e ⇒ A
complete-chk ⊢e = complete ⊢e ~∞

complete ⊢lit ~Z = ⊢lit
complete (⊢var x) ~Z = ⊢var x
complete (⊢ann ⊢e) ~Z = ⊢ann (complete-chk ⊢e)
complete (⊢lam₁ ⊢e) ~∞ = ⊢lam₁ (complete-chk ⊢e)
complete (⊢lam₂ ⊢e) (~S ⊢e₁ j~Σ) = ⊢lam₂ ⊢e₁ (complete ⊢e (~weaken0 j~Σ))
complete (⊢app₁ ⊢e ⊢e₁) ~Z = ⊢app (subsumption0 (complete-inf ⊢e) (s-arr s-empty (complete-chk ⊢e₁)))
complete (⊢app₂ ⊢e ⊢e₁) j~Σ = ⊢app (complete ⊢e (~S (complete-inf ⊢e₁) j~Σ))
complete (⊢sub ⊢e j≢Z) j~Σ = subsumption0 (complete-inf ⊢e) (complete-≤ j~Σ)
complete (⊢tabs₁ ⊢e) ~Z = ⊢tabs₁ (complete-inf ⊢e)
complete (⊢tapp ⊢e st) j~Σ = ⊢tapp (subsumption0 (complete-inf ⊢e) (s-∀-t st (complete-≤ j~Σ))) st

complete-≤ ~Z = s-empty
complete-≤ ~∞ = s-refl
complete-≤ (~S ⊢e j~Σ) = s-arr (complete-≤ j~Σ) (subsumption0 ⊢e s-refl)
