module Implicit.Language.EnvOps.InsertUVar where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.Base
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Ground.Base
open import Implicit.Language.EnvOps.Base


infix 3 _▶_,∙⇘_
data _▶_,∙⇘_ : Env n m → Fin (1 + m) → Env n (1 + m) → Set where
  ▶Z : Γ ▶ #0 ,∙⇘ Γ ,∙
  ▶S, : Γ ▶ k ,∙⇘ Γ'
      → A ↑ty k ⇘ A'
      → Γ , A ▶ k ,∙⇘ Γ' , A'
  ▶S^ : Γ ▶ k ,∙⇘ Γ'
      → Γ ,^ ▶ #S k ,∙⇘ Γ' ,^
  ▶S∙ : Γ ▶ k ,∙⇘ Γ'
      → Γ ,∙ ▶ #S k ,∙⇘ Γ' ,∙
  ▶S= : Γ ▶ k ,∙⇘ Γ'
      → B ↑ty k ⇘ B'
      → Γ ,= B ▶ #S k ,∙⇘ Γ' ,= B'
  ▶S≝ : Γ ▶ k ,∙⇘ Γ'
      → B ↑ty k ⇘ B'
      → Γ ,≝ B ▶ #S k ,∙⇘ Γ' ,≝ B'
  ▶S⋈ : Γ ▶ k ,∙⇘ Γ'
      → Γ ⋈ ▶ k ,∙⇘ Γ' ⋈


∋:=-weaken∙ : Γ ∋ X := A
     → Γ ▶ k ,∙⇘ Γ'
     → A ↑ty k ⇘ A'
     → Γ' ∋ punchIn k X := A'
∋:=-weaken∙ (Z up) ▶Z upA = S∙ (Z up) upA
∋:=-weaken∙ (Z up) (▶S= newΓ x) upA = Z (↑ty-comm0 up upA x)
∋:=-weaken∙ (S, inΓ) ▶Z upA = S∙ (S, inΓ) upA
∋:=-weaken∙ (S, inΓ) (▶S, newΓ x) upA = S, (∋:=-weaken∙ inΓ newΓ upA)
∋:=-weaken∙ (S∙ inΓ up) ▶Z upA = S∙ (S∙ inΓ up) upA
∋:=-weaken∙ (S∙ {A = A} inΓ up) (▶S∙ {k = k} newΓ) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S∙ (∋:=-weaken∙ inΓ newΓ upA') (↑ty-comm0 up upA upA')
∋:=-weaken∙ (S^ inΓ up) ▶Z upA = S∙ (S^ inΓ up) upA
∋:=-weaken∙ (S^ {A = A} inΓ up) (▶S^ {k = k} newΓ) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S^ (∋:=-weaken∙ inΓ newΓ upA') (↑ty-comm0 up upA upA')
∋:=-weaken∙ (S= inΓ up) ▶Z upA = S∙ (S= inΓ up) upA
∋:=-weaken∙ (S= {A = A} inΓ up) (▶S= {k = k} newΓ x) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S= (∋:=-weaken∙ inΓ newΓ upA') (↑ty-comm0 up upA upA')
∋:=-weaken∙ (S≝ inΓ up) ▶Z upA = S∙ (S≝ inΓ up) upA
∋:=-weaken∙ (S≝ {A = A} inΓ up) (▶S≝ {k = k} newΓ x) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S≝ (∋:=-weaken∙ inΓ newΓ upA') (↑ty-comm0 up upA upA')


∋∙-weaken∙ : Γ ∋∙ X
      → Γ ▶ k ,∙⇘ Γ'
      → Γ' ∋∙ punchIn k X
∋∙-weaken∙ Z ▶Z = S∙ Z
∋∙-weaken∙ Z (▶S∙ newΓ) = Z
∋∙-weaken∙ (S, inΓ) ▶Z = S∙ (S, inΓ)
∋∙-weaken∙ (S, inΓ) (▶S, newΓ x) = S, (∋∙-weaken∙ inΓ newΓ)
∋∙-weaken∙ (S∙ inΓ) ▶Z = S∙ (S∙ inΓ)
∋∙-weaken∙ (S∙ inΓ) (▶S∙ newΓ) = S∙ (∋∙-weaken∙ inΓ newΓ)
∋∙-weaken∙ (S= inΓ) ▶Z = S∙ (S= inΓ)
∋∙-weaken∙ (S= inΓ) (▶S= newΓ x) = S= (∋∙-weaken∙ inΓ newΓ)
∋∙-weaken∙ (S≝ inΓ) ▶Z = S∙ (S≝ inΓ)
∋∙-weaken∙ (S≝ inΓ) (▶S≝ newΓ x) = S≝ (∋∙-weaken∙ inΓ newΓ)
∋∙-weaken∙ (S^ inΓ) ▶Z = S∙ (S^ inΓ)
∋∙-weaken∙ (S^ inΓ) (▶S^ newΓ) = S^ (∋∙-weaken∙ inΓ newΓ)
∋∙-weaken∙ (S⋈ inΓ) ▶Z = S∙ (S⋈ inΓ)
∋∙-weaken∙ (S⋈ inΓ) (▶S⋈ newΓ) = S⋈ (∋∙-weaken∙ inΓ newΓ)

∋=-weaken∙ : Γ ∋= X
      → Γ ▶ k ,∙⇘ Γ'
      → Γ' ∋= punchIn k X
∋=-weaken∙ Z ▶Z = S∙ Z
∋=-weaken∙ Z (▶S= newΓ x) = Z
∋=-weaken∙ (S, inΓ) ▶Z = S∙ (S, inΓ)
∋=-weaken∙ (S, inΓ) (▶S, newΓ x) = S, (∋=-weaken∙ inΓ newΓ)
∋=-weaken∙ (S∙ inΓ) ▶Z = S∙ (S∙ inΓ)
∋=-weaken∙ (S∙ inΓ) (▶S∙ newΓ) = S∙ (∋=-weaken∙ inΓ newΓ)
∋=-weaken∙ (S^ inΓ) ▶Z = S∙ (S^ inΓ)
∋=-weaken∙ (S^ inΓ) (▶S^ newΓ) = S^ (∋=-weaken∙ inΓ newΓ)
∋=-weaken∙ (S= inΓ) ▶Z = S∙ (S= inΓ)
∋=-weaken∙ (S= inΓ) (▶S= newΓ x) = S= (∋=-weaken∙ inΓ newΓ)
∋=-weaken∙ (S≝ inΓ) ▶Z = S∙ (S≝ inΓ)
∋=-weaken∙ (S≝ inΓ) (▶S≝ newΓ x) = S≝ (∋=-weaken∙ inΓ newΓ)

∋≝-weaken∙ : Γ ∋≝ X
      → Γ ▶ k ,∙⇘ Γ'
      → Γ' ∋≝ punchIn k X
∋≝-weaken∙ Z ▶Z = S∙ Z
∋≝-weaken∙ Z (▶S≝ newΓ x) = Z
∋≝-weaken∙ (S, inΓ) ▶Z = S∙ (S, inΓ)
∋≝-weaken∙ (S, inΓ) (▶S, newΓ x) = S, (∋≝-weaken∙ inΓ newΓ)
∋≝-weaken∙ (S∙ inΓ) ▶Z = S∙ (S∙ inΓ)
∋≝-weaken∙ (S∙ inΓ) (▶S∙ newΓ) = S∙ (∋≝-weaken∙ inΓ newΓ)
∋≝-weaken∙ (S^ inΓ) ▶Z = S∙ (S^ inΓ)
∋≝-weaken∙ (S^ inΓ) (▶S^ newΓ) = S^ (∋≝-weaken∙ inΓ newΓ)
∋≝-weaken∙ (S= inΓ) ▶Z = S∙ (S= inΓ)
∋≝-weaken∙ (S= inΓ) (▶S= newΓ x) = S= (∋≝-weaken∙ inΓ newΓ)
∋≝-weaken∙ (S≝ inΓ) ▶Z = S∙ (S≝ inΓ)
∋≝-weaken∙ (S≝ inΓ) (▶S≝ newΓ x) = S≝ (∋≝-weaken∙ inΓ newΓ)
∋≝-weaken∙ (S⋈ inΓ) ▶Z = S∙ (S⋈ inΓ)
∋≝-weaken∙ (S⋈ inΓ) (▶S⋈ new) = S⋈ (∋≝-weaken∙ inΓ new)



⊢r-weaken∙ : Γ ⊢r A
           → Γ ▶ k ,∙⇘ Γ'
           → A ↑ty k ⇘ A'
           → Γ' ⊢r A'
⊢r-weaken∙ ⊢r-int new ↑ty-int = ⊢r-int
⊢r-weaken∙ (⊢r-var-∙ inΓ) new ↑ty-var = ⊢r-var-∙ (∋∙-weaken∙ inΓ new)
⊢r-weaken∙ (⊢r-var-≝ inΓ) new ↑ty-var = ⊢r-var-≝ (∋≝-weaken∙ inΓ new)
⊢r-weaken∙ (⊢r-arr regA regA₁) new (↑ty-arr upA upA₁) = ⊢r-arr (⊢r-weaken∙ regA new upA) (⊢r-weaken∙ regA₁ new upA₁)
⊢r-weaken∙ (⊢r-∀ regA) new (↑ty-∀ upA) = ⊢r-∀ (⊢r-weaken∙ regA (▶S∙ new) upA)
