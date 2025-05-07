module Implicit.Interm.Properties.PExtension where

open import Implicit.Language.All
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.PRegularity

postulate
  s-⊆-prv : Γ ⊢ j # A ⌞ ≤ ⌝ B
          → Γ ⊆ Δ
          → Δ ⊢ j # A ⌞ ≤ ⌝ B

infix 3 _⊆t_

data _⊆t_ : Env n m → Env n m → Set where
  empty : ∅ ⊆t ∅
  tvar : Γ ⊆t Δ
       → (regA : Γ ⊢r A)
       → Γ , A ⊆t Δ , A
  uvar :
      Γ ⊆t Δ
    → Γ ,∙ ⊆t Δ ,∙
  evar :
      Γ ⊆t Δ
    → Γ ,^ ⊆t Δ ,^
  evar-sol :
      Γ ⊆t Δ
    → (regA : Δ ⊢r A)
    → Γ ,^ ⊆t Δ ,= A
  svar :
      Γ ⊆t Δ
    → (regA : Γ ⊢r A)
    → Γ ,= A ⊆t Δ ,= A
  mark : Γ ⊆t Δ
       → Γ ⋈ ⊆t Δ ⋈


postulate
  ⊆t-∋⦂ : Γ ∋ x ⦂ A
        → Γ ⊆t Δ
        → Δ ∋ x ⦂ A

postulate
  ⊆t-∋∙ : Γ ∋∙ X
        → Γ ⊆t Δ
        → Δ ∋∙ X

postulate
  ⊆t-∋= : Γ ∋= k
         → Γ ⊆t Δ
         → Δ ∋= k

postulate
  ⊆t-⊢r : Γ ⊢r A
        → Γ ⊆t Δ
        → Δ ⊢r A

postulate
  ⊆t-⊢c : Γ ⊢c A
        → Γ ⊆t Δ
        → Δ ⊢c A

postulate
  ⊆t-tregular : TRegular Γ
              → Γ ⊆t Δ
              → TRegular Δ

postulate
  ⊆t-sregular : SRegular Γ
              → Γ ⊆t Δ
              → SRegular Δ

postulate
  ⊆t-⊢c-≫ : Γ ≫ A ⇘ B
          → Γ ⊆t Δ
          → Γ ⊢c A
          → Δ ≫ A ⇘ B

postulate
  s-⊆-prv-gen : Γ ⊢ j # A ⌞ ≤ ⌝ B
           → Γ ⊆t Δ
           → Δ ⊢ j # A ⌞ ≤ ⌝ B

postulate
  t-⊆-prv-gen : Γ ⊢ j # e ⦂ A
          → Γ ⊆t Δ
          → Δ ⊢ j # e ⦂ A

postulate
  ⊆-refl-tregular : TRegular Γ
                  → Γ ⊆t Γ

postulate
  ⊆-refl-sregular : SRegular Γ
                  → Γ ⊆t Γ

postulate
  ⊆-⊆t : Γ ⊆ Δ
       → Γ ⊆t Δ

postulate
  ⊆-⊆t-𝕣 : Γ ⊆ Δ
        → 𝕣 Γ ⊆t 𝕣 Δ

postulate
  t-⊆-prv : 𝕣 Γ ⊢ j # e ⦂ A
           → Γ ⊆ Δ
           → 𝕣 Δ ⊢ j # e ⦂ A
