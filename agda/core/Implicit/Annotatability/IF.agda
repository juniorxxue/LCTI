module Implicit.Annotatability.IF where

open import Implicit.Language.All
open import Implicit.Decl.All
open import Implicit.Decl.Typing

-- not occur only at the end
infix 3 _¬ε'_
data _¬ε'_ : Fin m → Type m → Set where
  ¬ε'-int : k ¬ε' Int
  ¬ε'-var : k ≢ X
          → k ¬ε' ‶ X
  ¬ε'-arr-l : k ε A
          → k ¬ε' (A `→ B)
  ¬ε'-arr-r : k ¬ε A
            → k ¬ε' B
            → k ¬ε' (A `→ B)
  ¬ε'-∀ : #S k ¬ε' A
        → k ¬ε' (`∀ A)


data wf : Type m → Set where
  wf-int : wf (Type m ∋⦂ Int)
  wf-var : wf (‶ X)
  wf-arr : wf A
         → wf B
         → wf (A `→ B)
  wf-∀   : wf A
         → #0 ¬ε' A
         → wf (`∀ A)

data wfg : Env n m → Set where
  wf-∅ : wfg ∅
  wf-, : wf A
       → wfg Γ
       → wfg (Γ , A)
  wf-^ : wfg Γ
       → wfg (Γ ,^)
  wf-,∙ : wfg Γ
        → wfg (Γ ,∙)
  wf-,= : wfg Γ
        → wf A
        → wfg (Γ ,= A)
  wf-⋈ : wfg Γ
       → wfg (Γ ⋈)

infix 3 _⊢_𝕄_
data _⊢_𝕄_ : Env n m → Type m → Type m → Set where
  𝕄-arr : Γ ⊢ A `→ B 𝕄 A `→ B
  M-∀ : Γ ⊢r T
      → wf T
      → (st : ⟦ T ⟧ A ⇘ A*)
      → Γ ⊢ A* 𝕄 B `→ C
--      → (rst : #0 ¬ε' A)
      → Γ ⊢ `∀ A 𝕄 B `→ C

infix 3 _⊢_⦂_⟶_
data _⊢_⦂_⟶_ : Env n m → Term n m → Type m → Term n m → Set where

  ela-lit : (regΓ : TRegular Γ)
          → (wfg : wfg Γ)
          → Γ ⊢ (lit n) ⦂ Int ⟶ (lit n)
  ela-var : (regΓ : TRegular Γ)
          → (wfg : wfg Γ)
          → Γ ∋ x ⦂ A
          → Γ ⊢ ` x ⦂ A ⟶ ` x
  ela-lam : Γ , A ⊢ e ⦂ B ⟶ e'
          → Γ ⊢ ƛ e ⦂ A `→ B ⟶ ƛ e'
  ela-app : Γ ⊢ e₁ ⦂ A ⟶ e₁'
           → Γ ⊢ A 𝕄 B `→ C
           → Γ ⊢ e₂ ⦂ B ⟶ e₂'
           → Γ ⊢ e₁ · e₂ ⦂ C ⟶ e₁' · (e₂' ⦂ B)
  -- two extra rules
  ela-∀i  : Γ ,∙ ⊢ e' ⦂ A ⟶ e₁
         → (upe : ↑tyᵉ0 e ⇘ e')
         → Γ ⊢ e ⦂ `∀ A ⟶ Λ (e₁ ⦂ A)


annotatability : Γ ⊢ e ⦂ A ⟶ e'
               → Γ ⊢ ∞ # e' ⦂ A
annotatability (ela-lit regΓ wfg₁) = {!!}
annotatability (ela-var regΓ wfg₁ x) = {!!}
annotatability (ela-lam ⊢e) = ⊢lam₁ (annotatability ⊢e)
annotatability (ela-app ⊢e x ⊢e₁) = {!!}
annotatability (ela-∀i ⊢e upe) = ⊢sub (⊢tabs (⊢ann (annotatability ⊢e))) {!!} gc-tlam nz-∞

