module Implicit.Language.Extension.Properties where

open import Implicit.Language.Base

open import Implicit.Language.Lookup.All
open import Implicit.Language.EnvOps.All
open import Implicit.Language.OpenClose.All

open import Implicit.Language.Extension.Base

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
⊆-in⦂ (S^ xinΓ up) (evar-sol ss cloA) = S= (⊆-in⦂ xinΓ ss) up
⊆-in⦂ (S= xinΓ x) (svar ss) = S= (⊆-in⦂ xinΓ ss) x

⊆-in:= : Γ ∋ k := C
       → Γ ⊆ Γ'
       → Γ' ∋ k := C
⊆-in:= (Z x) (svar ss) = Z x
⊆-in:= (S, inΓ) (var ss) = S, (⊆-in:= inΓ ss)
⊆-in:= (S^ inΓ x) (evar ss) = S^ (⊆-in:= inΓ ss) x
⊆-in:= (S^ inΓ x) (evar-sol {A = A} ss cloA) = S= (⊆-in:= inΓ ss) x
⊆-in:= (S∙ inΓ x) (uvar ss) = S∙ (⊆-in:= inΓ ss) x
⊆-in:= (S= inΓ st) (svar ss) = S= (⊆-in:= inΓ ss) st

⊆-in= : Γ ∋= k
      → Γ ⊆ Γ'
      → Γ' ∋= k
⊆-in= Z (svar ss) = Z
⊆-in= (S, inΓ) (var ss) = S, (⊆-in= inΓ ss)
⊆-in= (S^ inΓ) (evar ss) = S^ (⊆-in= inΓ ss)
⊆-in= (S^ inΓ) (evar-sol ss cloA) = S= (⊆-in= inΓ ss)
⊆-in= (S∙ inΓ) (uvar ss) = S∙ (⊆-in= inΓ ss)
⊆-in= (S= inΓ) (svar ss) = S= (⊆-in= inΓ ss)

⊆-in∙ : Γ ∋∙ k
      → Γ ⊆ Γ'
      → Γ' ∋∙ k
⊆-in∙ Z (uvar ss) = Z
⊆-in∙ (S^ inΓ) (evar ss) = S^ (⊆-in∙ inΓ ss)
⊆-in∙ (S^ inΓ) (evar-sol ss cloA) = S= (⊆-in∙ inΓ ss)
⊆-in∙ (S∙ inΓ) (uvar ss) = S∙ (⊆-in∙ inΓ ss)
⊆-in∙ (S, inΓ) (var ss) = S, (⊆-in∙ inΓ ss)
⊆-in∙ (S= inΓ) (svar ss) = S= (⊆-in∙ inΓ ss)


----------------------------------------------------------------------
--+                           closeness                            +--
----------------------------------------------------------------------

⊆-cloA : Γ ⊢c A
       → Γ ⊆ Δ
       → Δ ⊢c A
⊆-cloA ⊢c-int ss = ⊢c-int
⊆-cloA (⊢c-var-∙ x) ss = ⊢c-var-∙ (⊆-in∙ x ss)
⊆-cloA (⊢c-var-= x) ss = ⊢c-var-= (⊆-in= x ss)
⊆-cloA (⊢c-arr clo clo₁) ss = ⊢c-arr (⊆-cloA clo ss) (⊆-cloA clo₁ ss)
⊆-cloA (⊢c-∀ clo) ss = ⊢c-∀ (⊆-cloA clo (uvar ss))

⊆-closed : Closed Γ
         → Γ ⊆ Δ
         → Closed Δ
⊆-closed clo-Z base = clo-Z
⊆-closed (clo-S, cloΓ cloA) (var ext) = clo-S, (⊆-closed cloΓ ext) (⊆-cloA cloA ext)
⊆-closed (clo-S∙ cloΓ) (uvar ext) = clo-S∙ (⊆-closed cloΓ ext)
⊆-closed (clo-S^ cloΓ) (evar ext) = clo-S^ (⊆-closed cloΓ ext)
⊆-closed (clo-S^ cloΓ) (evar-sol ext cloA) = clo-S= (⊆-closed cloΓ ext) cloA
⊆-closed (clo-S= cloΓ cloA) (svar ext) = clo-S= (⊆-closed cloΓ ext) (⊆-cloA cloA ext)

----------------------------------------------------------------------
--+                         refl and trans                         +--
----------------------------------------------------------------------


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
⊆-trans (evar ⊆1) (evar-sol ⊆2 cloA) = evar-sol (⊆-trans ⊆1 ⊆2) cloA
⊆-trans (evar-sol ⊆1 cloA) (svar ⊆2) = evar-sol (⊆-trans ⊆1 ⊆2) (⊆-cloA cloA ⊆2)
⊆-trans (svar ⊆1) (svar ⊆2) = svar (⊆-trans ⊆1 ⊆2)

⊆-id : Γ ⊆ Δ
     → Δ ⊆ Γ
     → Γ ≡ Δ
⊆-id base ext2 = refl
⊆-id (uvar ext1) (uvar ext2) rewrite ⊆-id ext1 ext2 = refl
⊆-id (var ext1) (var ext2) rewrite ⊆-id ext1 ext2 = refl
⊆-id (evar ext1) (evar ext2) rewrite ⊆-id ext1 ext2 = refl
⊆-id (svar ext1) (svar ext2) rewrite ⊆-id ext1 ext2 = refl

inst-⊆ : [ A / X ] Γ ⟹ Γ'
       → Γ ⊢c A
       → Γ ⊆ Γ'
inst-⊆ (⟹^0 up) cloA = evar-sol ⊆-refl (⊢c-strengthen^0 cloA up)
inst-⊆ (⟹^S inst up1) cloA = evar (inst-⊆ inst (⊢c-strengthen^0 cloA up1))
inst-⊆ (⟹∙S inst up1) cloA = uvar (inst-⊆ inst (⊢c-strengthen∙0 cloA up1))
inst-⊆ (⟹,S inst) cloA = var (inst-⊆ inst (⊢c-strengthen,0 cloA))
inst-⊆ (⟹=S inst up1) cloA = svar (inst-⊆ inst (⊢c-strengthen=0 cloA up1))

⊆/x-∙-eq : Γ ∋∙ X
          → Γ ⊆ Δ w/v X
          → Γ ≡ Δ
⊆/x-∙-eq Z ext-Z∙ = refl
⊆/x-∙-eq (S, inΓ) (ext-S, ext) rewrite ⊆/x-∙-eq inΓ ext = refl
⊆/x-∙-eq (S∙ inΓ) (ext-S∙ ext) rewrite ⊆/x-∙-eq inΓ ext = refl
⊆/x-∙-eq (S= inΓ) (ext-S= ext) rewrite ⊆/x-∙-eq inΓ ext = refl
⊆/x-∙-eq (S^ inΓ) (ext-S^ ext) rewrite ⊆/x-∙-eq inΓ ext = refl

⊆/x-∙ : Γ ∋∙ X
       → Γ ⊆ Γ w/v X
⊆/x-∙ Z = ext-Z∙
⊆/x-∙ (S, inΓ) = ext-S, (⊆/x-∙ inΓ)
⊆/x-∙ (S∙ inΓ) = ext-S∙ (⊆/x-∙ inΓ)
⊆/x-∙ (S= inΓ) = ext-S= (⊆/x-∙ inΓ)
⊆/x-∙ (S^ inΓ) = ext-S^ (⊆/x-∙ inΓ)

⊆/x-=-eq : Γ ∋= X
          → Γ ⊆ Δ w/v X
          → Γ ≡ Δ
⊆/x-=-eq Z ext-Z= = refl
⊆/x-=-eq (S, inΓ) (ext-S, ext) rewrite ⊆/x-=-eq inΓ ext = refl
⊆/x-=-eq (S∙ inΓ) (ext-S∙ ext) rewrite ⊆/x-=-eq inΓ ext = refl
⊆/x-=-eq (S= inΓ) (ext-S= ext) rewrite ⊆/x-=-eq inΓ ext = refl
⊆/x-=-eq (S^ inΓ) (ext-S^ ext) rewrite ⊆/x-=-eq inΓ ext = refl

⊆/x-= : Γ ∋= X
       → Γ ⊆ Γ w/v X
⊆/x-= Z = ext-Z=
⊆/x-= (S, inΓ) = ext-S, (⊆/x-= inΓ)
⊆/x-= (S∙ inΓ) = ext-S∙ (⊆/x-= inΓ)
⊆/x-= (S^ inΓ) = ext-S^ (⊆/x-= inΓ)
⊆/x-= (S= inΓ) = ext-S= (⊆/x-= inΓ)

⊆/-close-eq : Γ ⊢c A
             → Γ ⊆ Δ w/t A
             → Γ ≡ Δ
⊆/-close-eq ⊢c-int ext-int = refl
⊆/-close-eq (⊢c-var-∙ inΓ) (ext-var x) = ⊆/x-∙-eq inΓ x
⊆/-close-eq (⊢c-var-= inΓ) (ext-var x) = ⊆/x-=-eq inΓ x
⊆/-close-eq (⊢c-arr cloA cloA₁) (ext-arr ext ext₁) with ⊆/-close-eq cloA ext
... | refl = ⊆/-close-eq cloA₁ ext₁
⊆/-close-eq (⊢c-∀ cloA) (ext-∀ ext) with ⊆/-close-eq cloA ext
... | refl = refl

⊆/-close : Γ ⊢c A
          → Γ ⊆ Γ w/t A
⊆/-close ⊢c-int = ext-int
⊆/-close (⊢c-var-∙ inΓ) = ext-var (⊆/x-∙ inΓ)
⊆/-close (⊢c-var-= inΓ) = ext-var (⊆/x-= inΓ)
⊆/-close (⊢c-arr cloA cloA₁) = ext-arr (⊆/-close cloA) (⊆/-close cloA₁)
⊆/-close (⊢c-∀ cloA) = ext-∀ (⊆/-close cloA)

inst-⊆/x : [ A / X ] Γ ⟹ Δ
         → Γ ⊢c A
         → Γ ⊆ Δ w/v X
inst-⊆/x (⟹^0 up) cloA = ext-Z^ (⊢c-strengthen^0 cloA up)
inst-⊆/x (⟹^S inst up1) cloA = ext-S^ (inst-⊆/x inst (⊢c-strengthen^0 cloA up1))
inst-⊆/x (⟹∙S inst up1) cloA = ext-S∙ (inst-⊆/x inst (⊢c-strengthen∙0 cloA up1))
inst-⊆/x (⟹,S inst) cloA = ext-S, (inst-⊆/x inst (⊢c-strengthen,0 cloA))
inst-⊆/x (⟹=S inst up1) cloA = ext-S= (inst-⊆/x inst (⊢c-strengthen=0 cloA up1))
