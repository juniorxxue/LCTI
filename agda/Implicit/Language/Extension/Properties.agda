module Implicit.Language.Extension.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Extension.Base

open import Implicit.Language.Lookup

private variable
  Γ Γ' Γ'' Δ : Env n m
  A B C : Type m
  X k : Fin m
  x : Fin n
  

⊆-refl : Γ ⊆ Γ
⊆-refl {Γ = ∅} = base
⊆-refl {Γ = Γ , A} = var ⊆-refl
⊆-refl {Γ = Γ ,∙} = uvar ⊆-refl
⊆-refl {Γ = Γ ,^} = evar ⊆-refl
⊆-refl {Γ = Γ ,= A} = svar ⊆-refl

⊆-trans : Γ ⊆ Γ'
        → Γ' ⊆ Γ''
        → Γ ⊆ Γ''
⊆-trans base base = base
⊆-trans (uvar ⊆1) (uvar ⊆2) = uvar (⊆-trans ⊆1 ⊆2)
⊆-trans (var ⊆1) (var ⊆2) = var (⊆-trans ⊆1 ⊆2)
⊆-trans (evar ⊆1) (evar ⊆2) = evar (⊆-trans ⊆1 ⊆2)
⊆-trans (evar ⊆1) (evar-sol ⊆2) = evar-sol (⊆-trans ⊆1 ⊆2)
⊆-trans (evar-sol ⊆1) (svar ⊆2) = evar-sol (⊆-trans ⊆1 ⊆2)
⊆-trans (svar ⊆1) (svar ⊆2) = svar (⊆-trans ⊆1 ⊆2)

⟹-⊆ : [ A / X ] Γ ⟹ Γ'
     → Γ ⊆ Γ'
⟹-⊆ (⟹^0 sf) = evar-sol ⊆-refl
⟹-⊆ (⟹,S s) = var (⟹-⊆ s)
⟹-⊆ (⟹^S x s) = evar (⟹-⊆ x)
⟹-⊆ (⟹∙S x s) = uvar (⟹-⊆ x)
⟹-⊆ (⟹=S up s) = svar (⟹-⊆ s)

----------------------------------------------------------------------
--+                             Lookup                             +--
----------------------------------------------------------------------

⊆-in⦂ : Γ ∋ x ⦂ A
     → Γ ⊆ Δ
     → Δ ∋ x ⦂ A
⊆-in⦂ Z (var ss) = Z
⊆-in⦂ (S, xinΓ) (var ss) = S, (⊆-in⦂ xinΓ ss)
⊆-in⦂ (S∙ xinΓ up) (uvar ss) = S∙ (⊆-in⦂ xinΓ ss) up
⊆-in⦂ (S^ xinΓ up) (evar ss) = S^ (⊆-in⦂ xinΓ ss) up
⊆-in⦂ (S^ xinΓ up) (evar-sol ss) = S= (⊆-in⦂ xinΓ ss) up
⊆-in⦂ (S= xinΓ x) (svar ss) = S= (⊆-in⦂ xinΓ ss) x

⊆-in:= : Γ ∋ k := C
       → Γ ⊆ Γ'
       → Γ' ∋ k := C
⊆-in:= (Z x) (svar ss) = Z x
⊆-in:= (S, inΓ) (var ss) = S, (⊆-in:= inΓ ss)
⊆-in:= (S^ inΓ x) (evar ss) = S^ (⊆-in:= inΓ ss) x
⊆-in:= (S^ inΓ x) (evar-sol {A = A} ss) = S= (⊆-in:= inΓ ss) x
⊆-in:= (S∙ inΓ x) (uvar ss) = S∙ (⊆-in:= inΓ ss) x
⊆-in:= (S= inΓ st) (svar ss) = S= (⊆-in:= inΓ ss) st

⊆-in= : Γ ∋= k
      → Γ ⊆ Γ'
      → Γ' ∋= k
⊆-in= Z (svar ss) = Z
⊆-in= (S, inΓ) (var ss) = S, (⊆-in= inΓ ss)
⊆-in= (S^ inΓ) (evar ss) = S^ (⊆-in= inΓ ss)
⊆-in= (S^ inΓ) (evar-sol ss) = S= (⊆-in= inΓ ss)
⊆-in= (S∙ inΓ) (uvar ss) = S∙ (⊆-in= inΓ ss)
⊆-in= (S= inΓ) (svar ss) = S= (⊆-in= inΓ ss)

⊆-in∙ : Γ ∋∙ k
      → Γ ⊆ Γ'
      → Γ' ∋∙ k
⊆-in∙ Z (uvar ss) = Z
⊆-in∙ (S^ inΓ) (evar ss) = S^ (⊆-in∙ inΓ ss)
⊆-in∙ (S^ inΓ) (evar-sol ss) = S= (⊆-in∙ inΓ ss)
⊆-in∙ (S∙ inΓ) (uvar ss) = S∙ (⊆-in∙ inΓ ss)
⊆-in∙ (S, inΓ) (var ss) = S, (⊆-in∙ inΓ ss)
⊆-in∙ (S= inΓ) (svar ss) = S= (⊆-in∙ inΓ ss)
