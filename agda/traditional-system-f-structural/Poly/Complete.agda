module Poly.Complete where

open import Poly.Common
open import Poly.Decl
open import Poly.Algo
-- open import Poly.Algo.Subsumption

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

  ~Sτ : ∀ {Γ : Env n m} {j A Σ Σ'} {B : Type (1 + m)}
    → (↑Σ' : ty-in-con Σ ↑ #0 ⇨ Σ')
    → Γ ,∙ ⊢ ⟨ j , B ⟩ ~ Σ'
    → Γ ⊢ ⟨ Sτ j , `∀ B ⟩ ~ (⟦ A ⟧↝ Σ)

{-
  ~Sτ : ∀ {Γ : Env n m} {j A Σ B'} {B : Type (1 + m)}
    → Γ ⊢ ⟨ j , B' ⟩ ~ Σ    
    → [ A ]ˢ B ⇨ B'
    → Γ ⊢ ⟨ Sτ j , `∀ B ⟩ ~ (⟦ A ⟧↝ Σ)
-}    

-- we have two eliminations for Sτ
-- we only provide the first one, we want to show that the second one can be subsumed.
~subsume : ∀ {Γ : Env n m} {j Σ Σ' A B B'}
  → [ A ]ˢ B ⇨ B'
  → Γ ⊢ ⟨ j , B' ⟩ ~ Σ
  ---------------------------
  → ty-in-con Σ ↑ #0 ⇨ Σ'
  → Γ ,∙ ⊢ ⟨ j , B ⟩ ~ Σ'
~subsume st ~Z ↑empty = ~Z
~subsume st ~∞ (↑type x) = {!~∞!}
~subsume st (~S ⊢e j~Σ) ↑Σ = {!!}
~subsume st (~Sτ ↑Σ' j~Σ) (↑tapp x ↑Σ₁) = {!!}

~subsume' : ∀ {Γ : Env n m} {j Σ A B B'}
  → [ A ]ˢ B ⇨ B'
  → Γ ⊢ ⟨ j , B' ⟩ ~ Σ
  ---------------------------
  → ∃[ Σ' ] Γ ,∙ ⊢ ⟨ j , B ⟩ ~ Σ'
~subsume' st ~Z = ⟨ □ , ~Z ⟩
~subsume' {B = B} st ~∞ = ⟨ τ B , ~∞ ⟩
~subsume' st (~S ⊢e j~Σ) = {!!}
~subsume' st (~Sτ ↑Σ' j~Σ) = {!!}

postulate
  ~weaken0 : ∀ {Γ : Env n m} {Σ A B j}
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ , A ⊢ ⟨ j , B ⟩ ~ ↑Σ0 Σ
  subsumption0 : ∀ {Γ : Env n m} {Σ A e}
    → Γ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ A ≤ Σ
    → Γ ⊢ Σ ⇒ e ⇒ A

complete : ∀ {Γ : Env n m} {Σ j e A}
  → Γ ⊢ j # e ⦂ A
  → Γ ⊢ ⟨ j , A ⟩ ~ Σ
  → Γ ⊢ Σ ⇒ e ⇒ A

complete-≤ : ∀ {Γ : Env n m} {Σ j A}
  → Γ ⊢m j # A
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
complete (⊢app₂ ⊢e ⊢e₁) j~Σ = ⊢app {!!} -- requires a general subsumption
complete (⊢sub ⊢e x j≢Z) j~Σ = subsumption0 (complete-inf ⊢e) (complete-≤ x j~Σ)
complete (⊢tabs₁ ⊢e) ~Z = ⊢tabs₁ (complete-inf ⊢e)
complete (⊢tabs₂ ⊢e) ~∞ = ⊢tabs₂ (complete-chk ⊢e)
complete (⊢tabs₃ ⊢e) (~Sτ x j~Σ) = ⊢tabs₃ yx (complete ⊢e j~Σ)
complete (⊢tapp ⊢e st) j~Σ with ~subsume' st j~Σ
... | ⟨ Σ' , j~Σ' ⟩ = ⊢tapp (complete ⊢e (~Sτ {!!} j~Σ')) st
-- ⊢tapp (complete ⊢e {!!}) {!!}

complete-≤ s-zero ~Z = s-empty
complete-≤ s-inf ~∞ = s-refl
complete-≤ (s-arr jA) (~S ⊢e j~Σ) = s-arr (complete-≤ jA j~Σ) (subsumption0 ⊢e s-refl)
complete-≤ (s-∀ st jA) (~Sτ x j~Σ) = s-∀ {!!} (complete-≤ jA {!!})
