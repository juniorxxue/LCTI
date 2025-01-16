module Implicit.Language.Extension.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Extension.Base

open import Implicit.Language.Lookup
open import Implicit.Language.OpenClose

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

⊆-id : Γ ⊆ Δ
     → Δ ⊆ Γ
     → Γ ≡ Δ
⊆-id base ext2 = refl
⊆-id (uvar ext1) (uvar ext2) rewrite ⊆-id ext1 ext2 = refl
⊆-id (var ext1) (var ext2) rewrite ⊆-id ext1 ext2 = refl
⊆-id (evar ext1) (evar ext2) rewrite ⊆-id ext1 ext2 = refl
⊆-id (svar ext1) (svar ext2) rewrite ⊆-id ext1 ext2 = refl

inst-⊆ : [ A / X ] Γ ⟹ Γ' ↪ B
     → Γ ⊆ Γ'
inst-⊆ (⟹^0 sf) = evar-sol ⊆-refl
inst-⊆ (⟹,S s) = var (inst-⊆ s)
inst-⊆ (⟹^S s up1 up2) = evar (inst-⊆ s)
inst-⊆ (⟹∙S s up1 up2) = uvar (inst-⊆ s)
inst-⊆ (⟹=S s up1 up2) = svar (inst-⊆ s)

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

----------------------------------------------------------------------
--+                           Closeness                            +--
----------------------------------------------------------------------

⊆-closed : Γ ⊢c A
         → Γ ⊆ Γ'
         → Γ' ⊢c A
⊆-closed ⊢c-int ss = ⊢c-int
⊆-closed (⊢c-var-∙ x) ss = ⊢c-var-∙ (⊆-in∙ x ss)
⊆-closed (⊢c-var-= x) ss = ⊢c-var-= (⊆-in= x ss)
⊆-closed (⊢c-arr clo clo₁) ss = ⊢c-arr (⊆-closed clo ss) (⊆-closed clo₁ ss)
⊆-closed (⊢c-∀ clo) ss = ⊢c-∀ (⊆-closed clo (uvar ss))

{-
⊆-closedΓ : Closed Γ
          → Γ ⊆ Δ
          → Closed Δ
⊆-closedΓ clo-Z base = clo-Z
⊆-closedΓ (clo-S, clo cloA) (var ext) = clo-S, (⊆-closedΓ clo ext) (⊆-closed cloA ext)
⊆-closedΓ (clo-S∙ clo) (uvar ext) = clo-S∙ (⊆-closedΓ clo ext)
⊆-closedΓ (clo-S^ clo) (evar ext) = clo-S^ (⊆-closedΓ clo ext)
⊆-closedΓ (clo-S^ clo) (evar-sol ext) = clo-S= {!!} {!!}
⊆-closedΓ (clo-S= clo cloA) ext = {!!}
-}
