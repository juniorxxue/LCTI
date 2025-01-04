module Implicit.Language.Lookup.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.Base
open import Implicit.Language.Shift
  
∋⦂-unique : Γ ∋ x ⦂ A
          → Γ ∋ x ⦂ B
          → A ≡ B
∋⦂-unique Z Z = refl
∋⦂-unique (S, in1) (S, in2) = ∋⦂-unique in1 in2
∋⦂-unique (S∙ in1 x) (S∙ in2 x₁) rewrite ∋⦂-unique in1 in2 = ↑ty-unique x x₁
∋⦂-unique (S^ in1 x) (S^ in2 up) rewrite ∋⦂-unique in1 in2 = ↑ty-unique x up
∋⦂-unique (S= in1 x) (S= in2 x₁) rewrite ∋⦂-unique in1 in2 = ↑ty-unique x x₁


inst-in : [ A / k ] Γ ⟹ Γ' ↪ B
        → Γ' ∋ k := B
inst-in (⟹^0 up) = Z up
inst-in (⟹^S inst up1 up2) = S^ (inst-in inst) up2
inst-in (⟹∙S inst up1 up2) = S∙ (inst-in inst) up2
inst-in (⟹,S inst) = S, (inst-in inst)
inst-in (⟹=S inst up1 up2) = S= (inst-in inst) up2

↑ty-ε : X ε A
      → A ↑ty k ⇘ A'
      → X #< k
      → inject₁ X ε A'
↑ty-ε ε-var ↑ty-var lt rewrite punchIn-inject lt = ε-var
↑ty-ε (ε-arr-l inA) (↑ty-arr up up₁) lt = ε-arr-l (↑ty-ε inA up lt)
↑ty-ε (ε-arr-r inA) (↑ty-arr up up₁) lt = ε-arr-r (↑ty-ε inA up₁ lt)
↑ty-ε (ε-∀ inA) (↑ty-∀ up) lt = ε-∀ (↑ty-ε inA up (s≤s lt))

↑ty-¬ε : X ¬ε A
      → A ↑ty k ⇘ A'
      → X #< k
      → inject₁ X ¬ε A'
↑ty-¬ε ¬ε-int ↑ty-int lt = ¬ε-int
↑ty-¬ε (¬ε-var x) ↑ty-var lt = ¬ε-var (punchIn-inject-neq lt x)
↑ty-¬ε (¬ε-arr ninA ninA₁) (↑ty-arr up up₁) lt = ¬ε-arr (↑ty-¬ε ninA up lt) (↑ty-¬ε ninA₁ up₁ lt)
↑ty-¬ε (¬ε-∀ ninA) (↑ty-∀ up) lt = ¬ε-∀ (↑ty-¬ε ninA up (s≤s lt))

:=to= : Γ ∋ k := A
      → Γ ∋= k
:=to= (Z up) = Z
:=to= (S, inΓ) = S, (:=to= inΓ)
:=to= (S^ inΓ up) = S^ (:=to= inΓ)
:=to= (S∙ inΓ up) = S∙ (:=to= inΓ)
:=to= (S= inΓ up) = S= (:=to= inΓ)

----------------------------------------------------------------------
--+                 properties about Γ extension                  +--
----------------------------------------------------------------------

▶^-∋:= : Γ ∋ X := A
     → Γ ▶ k ,^⇘ Γ'
     → A ↑ty k ⇘ A'
     → Γ' ∋ punchIn k X := A'
▶^-∋:= (Z up) ▶Z upA = S^ (Z up) upA
▶^-∋:= (Z up) (▶S= newΓ x) upA = Z (↑ty-comm0 up upA x)
▶^-∋:= (S, inΓ) ▶Z upA = S^ (S, inΓ) upA
▶^-∋:= (S, inΓ) (▶S, newΓ x) upA = S, (▶^-∋:= inΓ newΓ upA)
▶^-∋:= (S∙ inΓ up) ▶Z upA = S^ (S∙ inΓ up) upA
▶^-∋:= (S∙ {A = A} inΓ up) (▶S∙ {k = k} newΓ) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S∙ (▶^-∋:= inΓ newΓ upA') (↑ty-comm0 up upA upA')
▶^-∋:= (S^ inΓ up) ▶Z upA = S^ (S^ inΓ up) upA
▶^-∋:= (S^ {A = A} inΓ up) (▶S^ {k = k} newΓ) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S^ (▶^-∋:= inΓ newΓ upA') (↑ty-comm0 up upA upA')
▶^-∋:= (S= inΓ up) ▶Z upA = S^ (S= inΓ up) upA
▶^-∋:= (S= {A = A} inΓ up) (▶S= {k = k} newΓ x) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S= (▶^-∋:= inΓ newΓ upA') (↑ty-comm0 up upA upA')

▶∙-∋:= : Γ ∋ X := A
     → Γ ▶ k ,∙⇘ Γ'
     → A ↑ty k ⇘ A'
     → Γ' ∋ punchIn k X := A'
▶∙-∋:= (Z up) ▶Z upA = S∙ (Z up) upA
▶∙-∋:= (Z up) (▶S= newΓ x) upA = Z (↑ty-comm0 up upA x)
▶∙-∋:= (S, inΓ) ▶Z upA = S∙ (S, inΓ) upA
▶∙-∋:= (S, inΓ) (▶S, newΓ x) upA = S, (▶∙-∋:= inΓ newΓ upA)
▶∙-∋:= (S∙ inΓ up) ▶Z upA = S∙ (S∙ inΓ up) upA
▶∙-∋:= (S∙ {A = A} inΓ up) (▶S∙ {k = k} newΓ) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S∙ (▶∙-∋:= inΓ newΓ upA') (↑ty-comm0 up upA upA')
▶∙-∋:= (S^ inΓ up) ▶Z upA = S∙ (S^ inΓ up) upA
▶∙-∋:= (S^ {A = A} inΓ up) (▶S^ {k = k} newΓ) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S^ (▶∙-∋:= inΓ newΓ upA') (↑ty-comm0 up upA upA')
▶∙-∋:= (S= inΓ up) ▶Z upA = S∙ (S= inΓ up) upA
▶∙-∋:= (S= {A = A} inΓ up) (▶S= {k = k} newΓ x) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S= (▶∙-∋:= inΓ newΓ upA') (↑ty-comm0 up upA upA')

▶=-∋:= : Γ ∋ X := A
       → Γ ▶ k ,= T ⇘ Γ'
       → A ↑ty k ⇘ A'
       → Γ' ∋ punchIn k X := A'
▶=-∋:= (Z up) ▶Z upA = S= (Z up) upA
▶=-∋:= (Z up) (▶S= newΓ x x₁) upA = Z (↑ty-comm0 up upA x₁)
▶=-∋:= (S, inΓ) ▶Z upA = S= (S, inΓ) upA
▶=-∋:= (S, inΓ) (▶S, newΓ x) upA = S, (▶=-∋:= inΓ newΓ upA)
▶=-∋:= (S∙ inΓ up) ▶Z upA = S= (S∙ inΓ up) upA
▶=-∋:= (S∙ {A = A} inΓ up) (▶S∙ {k = k} newΓ x) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S∙ (▶=-∋:= inΓ newΓ upA') (↑ty-comm0 up upA upA')
▶=-∋:= (S^ inΓ up) ▶Z upA = S= (S^ inΓ up) upA
▶=-∋:= (S^ {A = A} inΓ up) (▶S^ {k = k} newΓ x) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S^ (▶=-∋:= inΓ newΓ upA') (↑ty-comm0 up upA upA')
▶=-∋:= (S= inΓ up) ▶Z upA = S= (S= inΓ up) upA
▶=-∋:= (S= {A = A} inΓ up) (▶S= {k = k} newΓ x x₁) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S= (▶=-∋:= inΓ newΓ upA') (↑ty-comm0 up upA upA')


▶,-∋:= : Γ ∋ X := A
       → Γ ▶ k , T ⇘ Γ'
       → Γ' ∋ X := A
▶,-∋:= (Z up) ▶Z = S, (Z up)
▶,-∋:= (Z up) (▶S= newΓ x) = Z up
▶,-∋:= (S, inΓ) ▶Z = S, (S, inΓ)
▶,-∋:= (S, inΓ) (▶S, newΓ) = S, (▶,-∋:= inΓ newΓ)
▶,-∋:= (S∙ inΓ up) ▶Z = S, (S∙ inΓ up)
▶,-∋:= (S∙ inΓ up) (▶S∙ newΓ x) = S∙ (▶,-∋:= inΓ newΓ) up
▶,-∋:= (S^ inΓ up) ▶Z = S, (S^ inΓ up)
▶,-∋:= (S^ inΓ up) (▶S^ newΓ x) = S^ (▶,-∋:= inΓ newΓ) up
▶,-∋:= (S= inΓ up) ▶Z = S, (S= inΓ up)
▶,-∋:= (S= inΓ up) (▶S= newΓ x) = S= (▶,-∋:= inΓ newΓ) up


▶,-∋∙ : Γ ∋∙ X
      → Γ ▶ k , T ⇘ Γ'
      → Γ' ∋∙ X
▶,-∋∙ Z ▶Z = S, Z
▶,-∋∙ Z (▶S∙ extΓ x) = Z
▶,-∋∙ (S, inΓ) ▶Z = S, (S, inΓ)
▶,-∋∙ (S, inΓ) (▶S, extΓ) = S, (▶,-∋∙ inΓ extΓ)
▶,-∋∙ (S∙ inΓ) ▶Z = S, (S∙ inΓ)
▶,-∋∙ (S∙ inΓ) (▶S∙ extΓ x) = S∙ (▶,-∋∙ inΓ extΓ)
▶,-∋∙ (S= inΓ) ▶Z = S, (S= inΓ)
▶,-∋∙ (S= inΓ) (▶S= extΓ x) = S= (▶,-∋∙ inΓ extΓ)
▶,-∋∙ (S^ inΓ) ▶Z = S, (S^ inΓ)
▶,-∋∙ (S^ inΓ) (▶S^ extΓ x) = S^ (▶,-∋∙ inΓ extΓ)

▶,-∋= : Γ ∋= X
      → Γ ▶ k , T ⇘ Γ'
      → Γ' ∋= X
▶,-∋= Z ▶Z = S, Z
▶,-∋= Z (▶S= extΓ x) = Z
▶,-∋= (S, inΓ) ▶Z = S, (S, inΓ)
▶,-∋= (S, inΓ) (▶S, extΓ) = S, (▶,-∋= inΓ extΓ)
▶,-∋= (S∙ inΓ) ▶Z = S, (S∙ inΓ)
▶,-∋= (S∙ inΓ) (▶S∙ extΓ x) = S∙ (▶,-∋= inΓ extΓ)
▶,-∋= (S= inΓ) ▶Z = S, (S= inΓ)
▶,-∋= (S= inΓ) (▶S= extΓ x) = S= (▶,-∋= inΓ extΓ)
▶,-∋= (S^ inΓ) ▶Z = S, (S^ inΓ)
▶,-∋= (S^ inΓ) (▶S^ extΓ x) = S^ (▶,-∋= inΓ extΓ)

▶^-∋∙ : Γ ∋∙ X
      → Γ ▶ k ,^⇘ Γ'
      → Γ' ∋∙ punchIn k X
▶^-∋∙ Z ▶Z = S^ Z
▶^-∋∙ Z (▶S∙ newΓ) = Z
▶^-∋∙ (S, inΓ) ▶Z = S^ (S, inΓ)
▶^-∋∙ (S, inΓ) (▶S, newΓ x) = S, (▶^-∋∙ inΓ newΓ)
▶^-∋∙ (S∙ inΓ) ▶Z = S^ (S∙ inΓ)
▶^-∋∙ (S∙ inΓ) (▶S∙ newΓ) = S∙ (▶^-∋∙ inΓ newΓ)
▶^-∋∙ (S= inΓ) ▶Z = S^ (S= inΓ)
▶^-∋∙ (S= inΓ) (▶S= newΓ x) = S= (▶^-∋∙ inΓ newΓ)
▶^-∋∙ (S^ inΓ) ▶Z = S^ (S^ inΓ)
▶^-∋∙ (S^ inΓ) (▶S^ newΓ) = S^ (▶^-∋∙ inΓ newΓ)

▶^-∋= : Γ ∋= X
      → Γ ▶ k ,^⇘ Γ'
      → Γ' ∋= punchIn k X
▶^-∋= Z ▶Z = S^ Z
▶^-∋= Z (▶S= newΓ x) = Z
▶^-∋= (S, inΓ) ▶Z = S^ (S, inΓ)
▶^-∋= (S, inΓ) (▶S, newΓ x) = S, (▶^-∋= inΓ newΓ)
▶^-∋= (S∙ inΓ) ▶Z = S^ (S∙ inΓ)
▶^-∋= (S∙ inΓ) (▶S∙ newΓ) = S∙ (▶^-∋= inΓ newΓ)
▶^-∋= (S= inΓ) ▶Z = S^ (S= inΓ)
▶^-∋= (S= inΓ) (▶S= newΓ x) = S= (▶^-∋= inΓ newΓ)
▶^-∋= (S^ inΓ) ▶Z = S^ (S^ inΓ)
▶^-∋= (S^ inΓ) (▶S^ newΓ) = S^ (▶^-∋= inΓ newΓ)


▶∙-∋∙ : Γ ∋∙ X
      → Γ ▶ k ,∙⇘ Γ'
      → Γ' ∋∙ punchIn k X
▶∙-∋∙ Z ▶Z = S∙ Z
▶∙-∋∙ Z (▶S∙ newΓ) = Z
▶∙-∋∙ (S, inΓ) ▶Z = S∙ (S, inΓ)
▶∙-∋∙ (S, inΓ) (▶S, newΓ x) = S, (▶∙-∋∙ inΓ newΓ)
▶∙-∋∙ (S∙ inΓ) ▶Z = S∙ (S∙ inΓ)
▶∙-∋∙ (S∙ inΓ) (▶S∙ newΓ) = S∙ (▶∙-∋∙ inΓ newΓ)
▶∙-∋∙ (S= inΓ) ▶Z = S∙ (S= inΓ)
▶∙-∋∙ (S= inΓ) (▶S= newΓ x) = S= (▶∙-∋∙ inΓ newΓ)
▶∙-∋∙ (S^ inΓ) ▶Z = S∙ (S^ inΓ)
▶∙-∋∙ (S^ inΓ) (▶S^ newΓ) = S^ (▶∙-∋∙ inΓ newΓ)

▶∙-∋= : Γ ∋= X
      → Γ ▶ k ,∙⇘ Γ'
      → Γ' ∋= punchIn k X
▶∙-∋= Z ▶Z = S∙ Z
▶∙-∋= Z (▶S= newΓ x) = Z
▶∙-∋= (S, inΓ) ▶Z = S∙ (S, inΓ)
▶∙-∋= (S, inΓ) (▶S, newΓ x) = S, (▶∙-∋= inΓ newΓ)
▶∙-∋= (S∙ inΓ) ▶Z = S∙ (S∙ inΓ)
▶∙-∋= (S∙ inΓ) (▶S∙ newΓ) = S∙ (▶∙-∋= inΓ newΓ)
▶∙-∋= (S^ inΓ) ▶Z = S∙ (S^ inΓ)
▶∙-∋= (S^ inΓ) (▶S^ newΓ) = S^ (▶∙-∋= inΓ newΓ)
▶∙-∋= (S= inΓ) ▶Z = S∙ (S= inΓ)
▶∙-∋= (S= inΓ) (▶S= newΓ x) = S= (▶∙-∋= inΓ newΓ)

▶=-∋∙ : Γ ∋∙ X
      → Γ ▶ k ,= T ⇘ Γ'
      → Γ' ∋∙ punchIn k X
▶=-∋∙ Z ▶Z = S= Z
▶=-∋∙ Z (▶S∙ newΓ x) = Z
▶=-∋∙ (S, inΓ) ▶Z = S= (S, inΓ)
▶=-∋∙ (S, inΓ) (▶S, newΓ x) = S, (▶=-∋∙ inΓ newΓ)
▶=-∋∙ (S∙ inΓ) ▶Z = S= (S∙ inΓ)
▶=-∋∙ (S∙ inΓ) (▶S∙ newΓ x) = S∙ (▶=-∋∙ inΓ newΓ)
▶=-∋∙ (S= inΓ) ▶Z = S= (S= inΓ)
▶=-∋∙ (S= inΓ) (▶S= newΓ x x₁) = S= (▶=-∋∙ inΓ newΓ)
▶=-∋∙ (S^ inΓ) ▶Z = S= (S^ inΓ)
▶=-∋∙ (S^ inΓ) (▶S^ newΓ x) = S^ (▶=-∋∙ inΓ newΓ)


▶=-∋= : Γ ∋= X
      → Γ ▶ k ,= T ⇘ Γ'
      → Γ' ∋= punchIn k X
▶=-∋= Z ▶Z = S= Z
▶=-∋= Z (▶S= newΓ x x₁) = Z
▶=-∋= (S, inΓ) ▶Z = S= (S, inΓ)
▶=-∋= (S, inΓ) (▶S, newΓ x) = S, (▶=-∋= inΓ newΓ)
▶=-∋= (S∙ inΓ) ▶Z = S= (S∙ inΓ)
▶=-∋= (S∙ inΓ) (▶S∙ newΓ x) = S∙ (▶=-∋= inΓ newΓ)
▶=-∋= (S= inΓ) ▶Z = S= (S= inΓ)
▶=-∋= (S= inΓ) (▶S= newΓ x x₁) = S= (▶=-∋= inΓ newΓ)
▶=-∋= (S^ inΓ) ▶Z = S= (S^ inΓ)
▶=-∋= (S^ inΓ) (▶S^ newΓ x) = S^ (▶=-∋= inΓ newΓ)

