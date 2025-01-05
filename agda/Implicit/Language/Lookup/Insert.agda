module Implicit.Language.Lookup.Insert where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.Base
open import Implicit.Language.Shift

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

▶∙-∋∙-rev : Γ' ∋∙ punchIn k X
          → Γ ▶ k ,∙⇘ Γ'
          → Γ ∋∙ X
▶∙-∋∙-rev {k = #0} (S∙ inΓ) ▶Z = inΓ
▶∙-∋∙-rev {k = #S k} {#0} Z (▶S∙ newΓ) = Z
▶∙-∋∙-rev {k = #S k} {#0} (S, inΓ) (▶S, newΓ x) = S, (▶∙-∋∙-rev inΓ newΓ)
▶∙-∋∙-rev {k = #S k} {#S X} (S, inΓ) (▶S, newΓ x) = S, (▶∙-∋∙-rev inΓ newΓ)
▶∙-∋∙-rev {k = #S k} {#S X} (S∙ inΓ) (▶S∙ newΓ) = S∙ (▶∙-∋∙-rev inΓ newΓ)
▶∙-∋∙-rev {k = #S k} {#S X} (S= inΓ) (▶S= newΓ x) = S= (▶∙-∋∙-rev inΓ newΓ)
▶∙-∋∙-rev {k = #S k} {#S X} (S^ inΓ) (▶S^ newΓ) = S^ (▶∙-∋∙-rev inΓ newΓ)

▶∙-∋=-rev : Γ' ∋= punchIn k X
          → Γ ▶ k ,∙⇘ Γ'
          → Γ ∋= X
▶∙-∋=-rev {k = #0} (S∙ inΓ) ▶Z = inΓ
▶∙-∋=-rev {k = #S k} {#0} Z (▶S= x newΓ) = Z
▶∙-∋=-rev {k = #S k} {#0} (S, inΓ) (▶S, newΓ x) = S, (▶∙-∋=-rev inΓ newΓ)
▶∙-∋=-rev {k = #S k} {#S X} (S, inΓ) (▶S, newΓ x) = S, (▶∙-∋=-rev inΓ newΓ)
▶∙-∋=-rev {k = #S k} {#S X} (S∙ inΓ) (▶S∙ newΓ) = S∙ (▶∙-∋=-rev inΓ newΓ)
▶∙-∋=-rev {k = #S k} {#S X} (S= inΓ) (▶S= newΓ x) = S= (▶∙-∋=-rev inΓ newΓ)
▶∙-∋=-rev {k = #S k} {#S X} (S^ inΓ) (▶S^ newΓ) = S^ (▶∙-∋=-rev inΓ newΓ)

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
