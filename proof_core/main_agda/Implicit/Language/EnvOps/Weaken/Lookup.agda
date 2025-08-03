module Implicit.Language.EnvOps.Weaken.Lookup where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Regular.All
open import Implicit.Language.Lookup.All

open import Implicit.Language.EnvOps.Weaken.Base

∋⦂-weaken : Γ ∋ x ⦂ A
          → Γ ▶ k ⇘ Γ' w/ mA
          → A ↑ty k ⇘ A'
           → Γ' ∋ x ⦂ A'
∋⦂-weaken Z ▶Z^ upA = S^ Z upA
∋⦂-weaken Z ▶Z∙ upA = S∙ Z upA
∋⦂-weaken Z (▶Z= regA) upA = S= Z upA
∋⦂-weaken Z (▶S, new up) upA
  with refl ← ↑ty-unique up upA = Z
∋⦂-weaken (S, inΓ) ▶Z^ upA = S^ (S, inΓ) upA
∋⦂-weaken (S, inΓ) ▶Z∙ upA = S∙ (S, inΓ) upA
∋⦂-weaken (S, inΓ) (▶Z= regA) upA = S= (S, inΓ) upA
∋⦂-weaken (S, inΓ) (▶S, new up) upA = S, (∋⦂-weaken inΓ new upA)
∋⦂-weaken (S∙ inΓ up) ▶Z^ upA = S^ (S∙ inΓ up) upA
∋⦂-weaken (S∙ inΓ up) ▶Z∙ upA = S∙ (S∙ inΓ up) upA
∋⦂-weaken (S∙ inΓ up) (▶Z= regA) upA = S= (S∙ inΓ up) upA
∋⦂-weaken {k = #S k} (S∙ {A = A} inΓ up) (▶S∙ new upmA) upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = S∙ (∋⦂-weaken inΓ new upA') (↑ty-comm0 up upA upA')
∋⦂-weaken (S^ inΓ up) ▶Z^ upA = S^ (S^ inΓ up) upA
∋⦂-weaken (S^ inΓ up) ▶Z∙ upA = S∙ (S^ inΓ up) upA
∋⦂-weaken (S^ inΓ up) (▶Z= regA) upA = S= (S^ inΓ up) upA
∋⦂-weaken {k = #S k} (S^ {A = A}  inΓ up) (▶S^ new upmA) upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = S^ (∋⦂-weaken inΓ new upA') (↑ty-comm0 up upA upA')
∋⦂-weaken (S= inΓ up) ▶Z^ upA = S^ (S= inΓ up) upA
∋⦂-weaken (S= inΓ up) ▶Z∙ upA = S∙ (S= inΓ up) upA
∋⦂-weaken (S= inΓ up) (▶Z= regA) upA = S= (S= inΓ up) upA
∋⦂-weaken {k = #S k} (S= {A = A} inΓ up) (▶S= new upmA upB) upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = S= (∋⦂-weaken inΓ new upA') (↑ty-comm0 up upA upA')
∋⦂-weaken (S⋈ inΓ) ▶Z^ upA = S^ (S⋈ inΓ) upA
∋⦂-weaken (S⋈ inΓ) ▶Z∙ upA = S∙ (S⋈ inΓ) upA
∋⦂-weaken (S⋈ inΓ) (▶Z= regA) upA = S= (S⋈ inΓ) upA
∋⦂-weaken (S⋈ inΓ) (▶S⋈ new) upA = S⋈ (∋⦂-weaken inΓ new upA)

∋:=-weaken : Γ ∋ X := A
           → A ↑ty k ⇘ A'
           → Γ ▶ k ⇘ Γ' w/ mA
           → Γ' ∋ punchIn k X := A'
∋:=-weaken (Z up) upA ▶Z^ = S^ (Z up) upA
∋:=-weaken (Z up) upA ▶Z∙ = S∙ (Z up) upA
∋:=-weaken (Z up) upA (▶Z= regA) = S= (Z up) upA
∋:=-weaken (Z up) upA (▶S= new upmA upB) = Z (↑ty-comm0 up upA upB)
∋:=-weaken (S∙ inΓ up) upA ▶Z^ = S^ (S∙ inΓ up) upA
∋:=-weaken (S∙ inΓ up) upA ▶Z∙ = S∙ (S∙ inΓ up) upA
∋:=-weaken (S∙ inΓ up) upA (▶Z= regA) = S= (S∙ inΓ up) upA
∋:=-weaken {k = #S k} (S∙ {A = A} inΓ up) upA (▶S∙ new upmA)
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = S∙ (∋:=-weaken inΓ upA' new) (↑ty-comm0 up upA upA')
∋:=-weaken (S^ inΓ up) upA ▶Z^ = S^ (S^ inΓ up) upA
∋:=-weaken (S^ inΓ up) upA ▶Z∙ = S∙ (S^ inΓ up) upA
∋:=-weaken (S^ inΓ up) upA (▶Z= regA) = S= (S^ inΓ up) upA
∋:=-weaken {k = #S k} (S^ {A = A} inΓ up) upA (▶S^ new upmA)
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = S^ (∋:=-weaken inΓ upA' new) (↑ty-comm0 up upA upA')
∋:=-weaken (S= inΓ up) upA ▶Z^ = S^ (S= inΓ up) upA
∋:=-weaken (S= inΓ up) upA ▶Z∙ = S∙ (S= inΓ up) upA
∋:=-weaken (S= inΓ up) upA (▶Z= regA) = S= (S= inΓ up) upA
∋:=-weaken {k = #S k} (S= {A = A} inΓ up) upA (▶S= new upmA upB)
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = S= (∋:=-weaken inΓ upA' new) (↑ty-comm0 up upA upA')
∋:=-weaken (S, inΓ) upA ▶Z^ = S^ (S, inΓ) upA
∋:=-weaken (S, inΓ) upA ▶Z∙ = S∙ (S, inΓ) upA
∋:=-weaken (S, inΓ) upA (▶Z= regA) = S= (S, inΓ) upA
∋:=-weaken (S, inΓ) upA (▶S, new up) = S, (∋:=-weaken inΓ upA new)
∋:=-weaken (S⋈ inΓ) upA ▶Z^ = S^ (S⋈ inΓ) upA
∋:=-weaken (S⋈ inΓ) upA ▶Z∙ = S∙ (S⋈ inΓ) upA
∋:=-weaken (S⋈ inΓ) upA (▶Z= regA) = S= (S⋈ inΓ) upA
∋:=-weaken (S⋈ inΓ) upA (▶S⋈ new) = S⋈ (∋:=-weaken inΓ upA new)

∋=-weaken : Γ ∋= X
          → Γ ▶ k ⇘ Γ' w/ mA
          → Γ' ∋= punchIn k X
∋=-weaken Z ▶Z^ = S^ Z
∋=-weaken Z ▶Z∙ = S∙ Z
∋=-weaken Z (▶Z= regA) = S= Z
∋=-weaken Z (▶S= new upmA upB) = Z
∋=-weaken (S∙ inΓ) ▶Z^ = S^ (S∙ inΓ)
∋=-weaken (S∙ inΓ) ▶Z∙ = S∙ (S∙ inΓ)
∋=-weaken (S∙ inΓ) (▶Z= regA) = S= (S∙ inΓ)
∋=-weaken (S∙ inΓ) (▶S∙ new upmA) = S∙ (∋=-weaken inΓ new)
∋=-weaken (S^ inΓ) ▶Z^ = S^ (S^ inΓ)
∋=-weaken (S^ inΓ) ▶Z∙ = S∙ (S^ inΓ)
∋=-weaken (S^ inΓ) (▶Z= regA) = S= (S^ inΓ)
∋=-weaken (S^ inΓ) (▶S^ new upmA) = S^ (∋=-weaken inΓ new)
∋=-weaken (S= inΓ) ▶Z^ = S^ (S= inΓ)
∋=-weaken (S= inΓ) ▶Z∙ = S∙ (S= inΓ)
∋=-weaken (S= inΓ) (▶Z= regA) = S= (S= inΓ)
∋=-weaken (S= inΓ) (▶S= new upmA upB) = S= (∋=-weaken inΓ new)
∋=-weaken (S, inΓ) ▶Z^ = S^ (S, inΓ)
∋=-weaken (S, inΓ) ▶Z∙ = S∙ (S, inΓ)
∋=-weaken (S, inΓ) (▶Z= regA) = S= (S, inΓ)
∋=-weaken (S, inΓ) (▶S, new up) = S, (∋=-weaken inΓ new)
∋=-weaken (S⋈ inΓ) ▶Z^ = S^ (S⋈ inΓ)
∋=-weaken (S⋈ inΓ) ▶Z∙ = S∙ (S⋈ inΓ)
∋=-weaken (S⋈ inΓ) (▶Z= regA) = S= (S⋈ inΓ)
∋=-weaken (S⋈ inΓ) (▶S⋈ new) = S⋈ (∋=-weaken inΓ new)

∋^-weaken : Γ ∋^ X
          → Γ ▶ k ⇘ Γ' w/ mA
          → Γ' ∋^ punchIn k X
∋^-weaken Z ▶Z^ = S^ Z
∋^-weaken Z ▶Z∙ = S∙ Z
∋^-weaken Z (▶Z= regA) = S= Z
∋^-weaken Z (▶S^ new upmA) = Z
∋^-weaken (S∙ inΓ) ▶Z^ = S^ (S∙ inΓ)
∋^-weaken (S∙ inΓ) ▶Z∙ = S∙ (S∙ inΓ)
∋^-weaken (S∙ inΓ) (▶Z= regA) = S= (S∙ inΓ)
∋^-weaken (S∙ inΓ) (▶S∙ new upmA) = S∙ (∋^-weaken inΓ new)
∋^-weaken (S= inΓ) ▶Z^ = S^ (S= inΓ)
∋^-weaken (S= inΓ) ▶Z∙ = S∙ (S= inΓ)
∋^-weaken (S= inΓ) (▶Z= regA) = S= (S= inΓ)
∋^-weaken (S= inΓ) (▶S= new upmA upB) = S= (∋^-weaken inΓ new)
∋^-weaken (S^ inΓ) ▶Z^ = S^ (S^ inΓ)
∋^-weaken (S^ inΓ) ▶Z∙ = S∙ (S^ inΓ)
∋^-weaken (S^ inΓ) (▶Z= regA) = S= (S^ inΓ)
∋^-weaken (S^ inΓ) (▶S^ new upmA) = S^ (∋^-weaken inΓ new)
∋^-weaken (S, inΓ) ▶Z^ = S^ (S, inΓ)
∋^-weaken (S, inΓ) ▶Z∙ = S∙ (S, inΓ)
∋^-weaken (S, inΓ) (▶Z= regA) = S= (S, inΓ)
∋^-weaken (S, inΓ) (▶S, new up) = S, (∋^-weaken inΓ new)
∋^-weaken (S⋈ inΓ) ▶Z^ = S^ (S⋈ inΓ)
∋^-weaken (S⋈ inΓ) ▶Z∙ = S∙ (S⋈ inΓ)
∋^-weaken (S⋈ inΓ) (▶Z= regA) = S= (S⋈ inΓ)
∋^-weaken (S⋈ inΓ) (▶S⋈ new) = S⋈ (∋^-weaken inΓ new)

∋∙-weaken : Γ ∋∙ X
          → Γ ▶ k ⇘ Γ' w/ mA
          → Γ' ∋∙ punchIn k X
∋∙-weaken Z ▶Z^ = S^ Z
∋∙-weaken Z ▶Z∙ = S∙ Z
∋∙-weaken Z (▶Z= regA) = S= Z
∋∙-weaken Z (▶S∙ new upmA) = Z
∋∙-weaken (S, inΓ) ▶Z^ = S^ (S, inΓ)
∋∙-weaken (S, inΓ) ▶Z∙ = S∙ (S, inΓ)
∋∙-weaken (S, inΓ) (▶Z= regA) = S= (S, inΓ)
∋∙-weaken (S, inΓ) (▶S, new up) = S, (∋∙-weaken inΓ new)
∋∙-weaken (S∙ inΓ) ▶Z^ = S^ (S∙ inΓ)
∋∙-weaken (S∙ inΓ) ▶Z∙ = S∙ (S∙ inΓ)
∋∙-weaken (S∙ inΓ) (▶Z= regA) = S= (S∙ inΓ)
∋∙-weaken (S∙ inΓ) (▶S∙ new upmA) = S∙ (∋∙-weaken inΓ new)
∋∙-weaken (S= inΓ) ▶Z^ = S^ (S= inΓ)
∋∙-weaken (S= inΓ) ▶Z∙ = S∙ (S= inΓ)
∋∙-weaken (S= inΓ) (▶Z= regA) = S= (S= inΓ)
∋∙-weaken (S= inΓ) (▶S= new upmA upB) = S= (∋∙-weaken inΓ new)
∋∙-weaken (S^ inΓ) ▶Z^ = S^ (S^ inΓ)
∋∙-weaken (S^ inΓ) ▶Z∙ = S∙ (S^ inΓ)
∋∙-weaken (S^ inΓ) (▶Z= regA) = S= (S^ inΓ)
∋∙-weaken (S^ inΓ) (▶S^ new upmA) = S^ (∋∙-weaken inΓ new)
∋∙-weaken (S⋈ inΓ) ▶Z^ = S^ (S⋈ inΓ)
∋∙-weaken (S⋈ inΓ) ▶Z∙ = S∙ (S⋈ inΓ)
∋∙-weaken (S⋈ inΓ) (▶Z= regA) = S= (S⋈ inΓ)
∋∙-weaken (S⋈ inΓ) (▶S⋈ new) = S⋈ (∋∙-weaken inΓ new)
