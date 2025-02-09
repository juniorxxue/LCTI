module Implicit.Language.Ground.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.OpenClose.All
open import Implicit.Language.Norm.All
open import Implicit.Language.EnvOps.All
open import Implicit.Language.Ground.Base

postulate

  grd-invar,0 : Γ , T₁ ≫ A ⇘ A%
             → Γ , T₂ ≫ A ⇘ A%

  grde-invar,0 : Γ , T₁ ≫ᵉ e ⇘ e%
              → Γ , T₂ ≫ᵉ e ⇘ e%


grd-total : Γ ⊢c A
         → ∃[ A% ](Γ ≫ A ⇘ A%)
grd-total ⊢c-int = ⟨ Int , grd-int ⟩
grd-total (⊢c-var-∙ {X = X} inΓ) = ⟨ ‶ X , grd-var∙ inΓ ⟩
grd-total (⊢c-var-= inΓ) with ∋:=-total inΓ
... | ⟨ A , AinΓ ⟩ = ⟨ A , grd-var= AinΓ ⟩
grd-total (⊢c-arr cloA cloA₁) = ⟨ grd-total cloA .proj₁ `→ grd-total cloA₁ .proj₁ ,
                                   grd-arr (grd-total cloA .proj₂) (grd-total cloA₁ .proj₂) ⟩
grd-total (⊢c-∀ cloA) = ⟨ `∀ grd-total cloA .proj₁ ,
                           grd-∀ (grd-total cloA .proj₂) ⟩

grd-unique : Γ ≫ A ⇘ A%
          → Γ ≫ A ⇘ B%
          → A% ≡ B%
grd-unique grd-int grd-int = refl
grd-unique (grd-var= x) (grd-var= x₁) = ∋:=-unique x x₁
grd-unique (grd-var= x) (grd-var∙ x₁) = ⊥-elim (∙∈-:=∈-false x₁ x)
grd-unique (grd-var∙ x) (grd-var= x₁) = ⊥-elim (∙∈-:=∈-false x x₁)
grd-unique (grd-var∙ x) (grd-var∙ x₁) = refl
grd-unique (grd-arr apA apA₁) (grd-arr apB apB₁) with grd-unique apA apB | grd-unique apA₁ apB₁
... | refl | refl = refl
grd-unique (grd-∀ apA) (grd-∀ apB) with grd-unique apA apB
... | refl = refl


grd-∋∙ : Γ ∋∙ X
      → Γ ≫ᵍ Γ%
      → Γ% ∋∙ X
grd-∋∙ Z (grd-S∙ apΓ) = Z
grd-∋∙ (S, inΓ) (grd-S, apΓ apA) = S, (grd-∋∙ inΓ apΓ)
grd-∋∙ (S∙ inΓ) (grd-S∙ apΓ) = S∙ (grd-∋∙ inΓ apΓ)
grd-∋∙ (S= inΓ) (grd-S= apΓ x) = S= (grd-∋∙ inΓ apΓ)
grd-∋∙ (S^ inΓ) (grd-S^ apΓ) = S^ (grd-∋∙ inΓ apΓ)

grd-∋∙-rev : Γ% ∋∙ X
          → Γ ≫ᵍ Γ%
          → Γ ∋∙ X
grd-∋∙-rev Z (grd-S∙ apΓ) = Z
grd-∋∙-rev (S, inΓ%) (grd-S, apΓ apA) = S, (grd-∋∙-rev inΓ% apΓ)
grd-∋∙-rev (S∙ inΓ%) (grd-S∙ apΓ) = S∙ (grd-∋∙-rev inΓ% apΓ)
grd-∋∙-rev (S= inΓ%) (grd-S= apΓ x) = S= (grd-∋∙-rev inΓ% apΓ)
grd-∋∙-rev (S^ inΓ%) (grd-S^ apΓ) = S^ (grd-∋∙-rev inΓ% apΓ)

grd-∋= : Γ ∋= X
      → Γ ≫ᵍ Γ%
      → Γ% ∋= X
grd-∋= Z (grd-S= apΓ x) = Z
grd-∋= (S, inΓ) (grd-S, apΓ apA) = S, (grd-∋= inΓ apΓ)
grd-∋= (S∙ inΓ) (grd-S∙ apΓ) = S∙ (grd-∋= inΓ apΓ)
grd-∋= (S= inΓ) (grd-S= apΓ x) = S= (grd-∋= inΓ apΓ)
grd-∋= (S^ inΓ) (grd-S^ apΓ) = S^ (grd-∋= inΓ apΓ)



grd-close-prv : Γ ⊢c A
             → Γ ≫ᵍ Γ%
             → Γ% ⊢c A
grd-close-prv ⊢c-int apΓ = ⊢c-int
grd-close-prv (⊢c-var-∙ inΓ) apΓ = ⊢c-var-∙ (grd-∋∙ inΓ apΓ)
grd-close-prv (⊢c-var-= inΓ) apΓ = ⊢c-var-= (grd-∋= inΓ apΓ)
grd-close-prv (⊢c-arr cloA cloA₁) apΓ = ⊢c-arr (grd-close-prv cloA apΓ) (grd-close-prv cloA₁ apΓ)
grd-close-prv (⊢c-∀ cloA) apΓ = ⊢c-∀ (grd-close-prv cloA (grd-S∙ apΓ))

grd-closeA : Γ ⊢c A
          → Γ ≫ᵍ Γ%
          → Norm Γ%
          → Γ% ≫ A ⇘ A%
          → Γ% ⊢n A%
grd-closeA ⊢c-int cloΓ apΓ grd-int = ⊢n-int
grd-closeA (⊢c-var-∙ inΓ) cloΓ apΓ (grd-var= x) = ⊥-elim (∙∈-:=∈-false (grd-∋∙ inΓ cloΓ) x)
grd-closeA (⊢c-var-∙ inΓ) cloΓ apΓ (grd-var∙ x) = ⊢n-var-∙ x
grd-closeA (⊢c-var-= inΓ) cloΓ apΓ (grd-var= x) = ∋:=-norm apΓ x
grd-closeA (⊢c-var-= inΓ) cloΓ apΓ (grd-var∙ x) = ⊥-elim (∙∈-=∈-false x (grd-∋= inΓ cloΓ))
grd-closeA (⊢c-arr cloA cloA₁) cloΓ apΓ (grd-arr apA apA₁) = ⊢n-arr (grd-closeA cloA cloΓ apΓ apA)
                                                                  (grd-closeA cloA₁ cloΓ apΓ apA₁)
grd-closeA (⊢c-∀ cloA) cloΓ apΓ (grd-∀ apA) = ⊢n-∀ (grd-closeA cloA (grd-S∙ cloΓ) (nom-S∙ apΓ) apA)

grd-closed : Closed Γ
          → Γ ≫ᵍ Γ%
          → Norm Γ%
grd-closed clo-Z grd-Z = nom-Z
grd-closed (clo-S, cloΓ cloA) (grd-S, apΓ apA) = nom-S, (grd-closed cloΓ apΓ) (grd-closeA cloA apΓ (grd-closed cloΓ apΓ) apA)
grd-closed (clo-S∙ cloΓ) (grd-S∙ apΓ) = nom-S∙ (grd-closed cloΓ apΓ)
grd-closed (clo-S^ cloΓ) (grd-S^ apΓ) = nom-S^ (grd-closed cloΓ apΓ)
grd-closed (clo-S= cloΓ cloA) (grd-S= apΓ x) = nom-S= (grd-closed cloΓ apΓ) (grd-closeA cloA apΓ (grd-closed cloΓ apΓ) x)

postulate
  grd-weaken=0 : Γ ≫ A ⇘ A%
              → ↑ty0 A ⇘ A'
              → ↑ty0 A% ⇘ A%'
              → Γ ,= T ≫ A' ⇘ A%'

  grd-weaken∙0 : Γ ≫ A ⇘ A%
              → ↑ty0 A ⇘ A'
              → ↑ty0 A% ⇘ A%'
              → Γ ,∙ ≫ A' ⇘ A%'

  grd-weaken^0 : Γ ≫ A ⇘ A%
              → ↑ty0 A ⇘ A'
              → ↑ty0 A% ⇘ A%'
              → Γ ,^ ≫ A' ⇘ A%'

  grd-strengthen^0 : Γ ,^ ≫ A' ⇘ A%'
              → ↑ty0 A ⇘ A'
              → ↑ty0 A% ⇘ A%'
                  → Γ ≫ A ⇘ A%

  grd-strengthen∙0 : Γ ,∙ ≫ A' ⇘ A%'
              → ↑ty0 A ⇘ A'
              → ↑ty0 A% ⇘ A%'
                  → Γ ≫ A ⇘ A%

  grd-strengthen=0 : Γ ,= T ≫ A' ⇘ A%'
              → ↑ty0 A ⇘ A'
              → ↑ty0 A% ⇘ A%'
                  → Γ ≫ A ⇘ A%

  grd-weaken,0 : Γ ≫ A ⇘ A%
              → Γ , T ≫ A ⇘ A%

  grd-strengthen,0 : Γ , T ≫ A ⇘ A%
                  → Γ ≫ A ⇘ A%



grd-var=-ap : Γ ∋ X := A
           → Γ ≫ᵍ Γ%
           → Γ% ∋ X := A%
           → Γ% ≫ A ⇘ A%
grd-var=-ap (Z up) (grd-S= apΓ x) (Z up₁) = grd-weaken=0 x up up₁
grd-var=-ap (S, inΓ) (grd-S, apΓ apA) (S, inΓ%) = grd-weaken,0 (grd-var=-ap inΓ apΓ inΓ%)
grd-var=-ap (S∙ inΓ up) (grd-S∙ apΓ) (S∙ inΓ% up₁) = grd-weaken∙0 (grd-var=-ap inΓ apΓ inΓ%) up up₁
grd-var=-ap (S^ inΓ up) (grd-S^ apΓ) (S^ inΓ% up₁) = grd-weaken^0 (grd-var=-ap inΓ apΓ inΓ%) up up₁
grd-var=-ap (S= inΓ up) (grd-S= apΓ x) (S= inΓ% up₁) = grd-weaken=0 (grd-var=-ap inΓ apΓ inΓ%) up up₁


grd-↑ty-∙ : Γ ≫ A' ⇘ A%'
       → Γ ◀ k ∙⇘ Γ'
       → A ↑ty k ⇘ A'
       → Γ' ≫ A ⇘ A%
       → A% ↑ty k ⇘ A%'
grd-↑ty-∙ grd-int newΓ ↑ty-int grd-int = ↑ty-int
grd-↑ty-∙ (grd-var= x) newΓ ↑ty-var (grd-var= x₁) = ◀∙-∋:=' x newΓ x₁
grd-↑ty-∙ (grd-var= x) newΓ ↑ty-var (grd-var∙ x₁) = ⊥-elim (∙∈-=∈-false x₁ (◀∙-∋= (:=to= x) newΓ))
grd-↑ty-∙ (grd-var∙ x) newΓ ↑ty-var (grd-var= x₁) = ⊥-elim (∙∈-=∈-false (◀∙-∋∙ x newΓ) (:=to= x₁))
grd-↑ty-∙ (grd-var∙ x) newΓ ↑ty-var (grd-var∙ x₁) = ↑ty-var
grd-↑ty-∙ (grd-arr apA' apA'') newΓ (↑ty-arr upA upA₁) (grd-arr apA apA₁) = ↑ty-arr (grd-↑ty-∙ apA' newΓ upA apA) (grd-↑ty-∙ apA'' newΓ upA₁ apA₁)
grd-↑ty-∙ (grd-∀ apA') newΓ (↑ty-∀ upA) (grd-∀ apA) = ↑ty-∀ (grd-↑ty-∙ apA' (◀S∙ newΓ) upA apA)

grd-↑ty^ : Γ ≫ A' ⇘ A%'
       → Γ ◀ k ^⇘ Γ'
       → A ↑ty k ⇘ A'
       → Γ' ≫ A ⇘ A%
       → A% ↑ty k ⇘ A%'
grd-↑ty^ grd-int newΓ ↑ty-int grd-int = ↑ty-int
grd-↑ty^ (grd-var= x) newΓ ↑ty-var (grd-var= x₁) = ◀^-∋:=' x newΓ x₁
grd-↑ty^ (grd-var= x) newΓ ↑ty-var (grd-var∙ x₁) = ⊥-elim (∙∈-=∈-false x₁ (◀^-∋= (:=to= x) newΓ))
grd-↑ty^ (grd-var∙ x) newΓ ↑ty-var (grd-var= x₁) = ⊥-elim (∙∈-=∈-false (◀^-∋∙ x newΓ) (:=to= x₁))
grd-↑ty^ (grd-var∙ x) newΓ ↑ty-var (grd-var∙ x₁) = ↑ty-var
grd-↑ty^ (grd-arr apA' apA'') newΓ (↑ty-arr upA upA₁) (grd-arr apA apA₁) = ↑ty-arr (grd-↑ty^ apA' newΓ upA apA) (grd-↑ty^ apA'' newΓ upA₁ apA₁)
grd-↑ty^ (grd-∀ apA') newΓ (↑ty-∀ upA) (grd-∀ apA) = ↑ty-∀ (grd-↑ty^ apA' (◀S∙ newΓ) upA apA)

grd-↑ty= : Γ ≫ A' ⇘ A%'
       → Γ ◀ k =⇘ Γ'
       → A ↑ty k ⇘ A'
       → Γ' ≫ A ⇘ A%
       → A% ↑ty k ⇘ A%'
grd-↑ty= grd-int newΓ ↑ty-int grd-int = ↑ty-int
grd-↑ty= (grd-var= x) newΓ ↑ty-var (grd-var= x₁) = ◀=-∋:=' x newΓ x₁
grd-↑ty= (grd-var= x) newΓ ↑ty-var (grd-var∙ x₁) = ⊥-elim (∙∈-=∈-false x₁ (◀=-∋= (:=to= x) newΓ))
grd-↑ty= (grd-var∙ x) newΓ ↑ty-var (grd-var= x₁) = ⊥-elim (∙∈-=∈-false (◀=-∋∙ x newΓ) (:=to= x₁))
grd-↑ty= (grd-var∙ x) newΓ ↑ty-var (grd-var∙ x₁) = ↑ty-var
grd-↑ty= (grd-arr apA' apA'') newΓ (↑ty-arr upA upA₁) (grd-arr apA apA₁) = ↑ty-arr (grd-↑ty= apA' newΓ upA apA) (grd-↑ty= apA'' newΓ upA₁ apA₁)
grd-↑ty= (grd-∀ apA') newΓ (↑ty-∀ upA) (grd-∀ apA) = ↑ty-∀ (grd-↑ty= apA' (◀S∙ newΓ) upA apA)


grd-∋⦂ : Γ ∋ x ⦂ A
       → Closed Γ
       → Γ ≫ᵍ Γ%
       → Γ% ≫ A ⇘ A%
       → Γ% ∋ x ⦂ A%
grd-∋⦂ Z (clo-S, cloΓ cloA) (grd-S, apΓ apA₁) apA with grd-unique apA₁ (grd-strengthen,0 apA)
... | refl = Z
grd-∋⦂ (S, inΓ) (clo-S, cloΓ cloA) (grd-S, apΓ apA₁) apA = S, (grd-∋⦂ inΓ cloΓ apΓ (grd-strengthen,0 apA))
grd-∋⦂ (S∙ inΓ up) (clo-S∙ cloΓ) (grd-S∙ apΓ) apA with grd-total (grd-close-prv (∋⦂-closed cloΓ inΓ) apΓ)
... | ⟨ A% , apA' ⟩ = S∙ (grd-∋⦂ inΓ cloΓ apΓ apA') (grd-↑ty-∙ apA ◀Z up apA')
grd-∋⦂ (S^ inΓ up) (clo-S^ cloΓ) (grd-S^ apΓ) apA with grd-total (grd-close-prv (∋⦂-closed cloΓ inΓ) apΓ)
... | ⟨ A% , apA' ⟩ = S^ (grd-∋⦂ inΓ cloΓ apΓ apA') (grd-↑ty^ apA ◀Z up apA')
grd-∋⦂ (S= inΓ up) (clo-S= cloΓ cloA) (grd-S= apΓ x) apA with grd-total (grd-close-prv (∋⦂-closed cloΓ inΓ) apΓ)
... | ⟨ A% , apA' ⟩ = S= (grd-∋⦂ inΓ cloΓ apΓ apA') (grd-↑ty= apA ◀Z up apA')



grd-↑ty : Γ ≫ A ⇘ A%
       → k ¬εᵍ Γ
       → Shifted A k
       → Shifted A% k
grd-↑ty grd-int ninΓ sfd-int = sfd-int
grd-↑ty (grd-var= x) ninΓ (sfd-var x₁) = εᵍ-shifted ninΓ x
grd-↑ty (grd-var∙ x) ninΓ (sfd-var x₁) = sfd-var x₁
grd-↑ty (grd-arr apA apA₁) ninΓ (sfd-arr st st₁) = sfd-arr (grd-↑ty apA ninΓ st) (grd-↑ty apA₁ ninΓ st₁)
grd-↑ty (grd-∀ apA) ninΓ (sfd-∀ st) = sfd-∀ (grd-↑ty apA (S∙ ninΓ) st)
