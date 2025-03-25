module Implicit.Language.EnvOps.InsertSVar where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.Base
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Ground.Base
open import Implicit.Language.EnvOps.Base

infix 3 _▶_,=_⇘_
data _▶_,=_⇘_ : Env n m → Fin (1 + m) → Type m → Env n (1 + m) → Set where
  ▶Z  : (regA : Γ ⊢r A)
      → Γ ▶ #0 ,= A ⇘ Γ ,= A
  ▶S, : Γ ▶ k ,= A ⇘ Γ'
      → (up : B ↑ty k ⇘ B')
      → Γ , B ▶ k ,= A ⇘ Γ' , B'
  ▶S^ : Γ ▶ k ,= A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → Γ ,^ ▶ #S k ,= A' ⇘ Γ' ,^
  ▶S∙ : Γ ▶ k ,= A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → Γ ,∙ ▶ #S k ,= A' ⇘ Γ' ,∙
  ▶S= : Γ ▶ k ,= A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → B ↑ty k ⇘ B'
      → Γ ,= B ▶ #S k ,= A' ⇘ Γ' ,= B'
  ▶S⋈ : Γ ▶ k ,= A ⇘ Γ'
      → Γ ⋈ ▶ k ,= A ⇘ Γ' ⋈


∋:=-weaken= : Γ ∋ X := A
       → Γ ▶ k ,= T ⇘ Γ'
       → A ↑ty k ⇘ A'
       → Γ' ∋ punchIn k X := A'
∋:=-weaken= (Z up) (▶Z cloA) upA = S= (Z up) upA
∋:=-weaken= (Z up) (▶S= newΓ x x₁) upA = Z (↑ty-comm0 up upA x₁)
∋:=-weaken= (S, inΓ) (▶Z cloA) upA = S= (S, inΓ) upA
∋:=-weaken= (S, inΓ) (▶S, newΓ x) upA = S, (∋:=-weaken= inΓ newΓ upA)
∋:=-weaken= (S∙ inΓ up) (▶Z cloA) upA = S= (S∙ inΓ up) upA
∋:=-weaken= (S∙ {A = A} inΓ up) (▶S∙ {k = k} newΓ x) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S∙ (∋:=-weaken= inΓ newΓ upA') (↑ty-comm0 up upA upA')
∋:=-weaken= (S^ inΓ up) (▶Z cloA) upA = S= (S^ inΓ up) upA
∋:=-weaken= (S^ {A = A} inΓ up) (▶S^ {k = k} newΓ x) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S^ (∋:=-weaken= inΓ newΓ upA') (↑ty-comm0 up upA upA')
∋:=-weaken= (S= inΓ up) (▶Z cloA) upA = S= (S= inΓ up) upA
∋:=-weaken= (S= {A = A} inΓ up) (▶S= {k = k} newΓ x x₁) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S= (∋:=-weaken= inΓ newΓ upA') (↑ty-comm0 up upA upA')

∋∙-weaken= : Γ ∋∙ X
      → Γ ▶ k ,= T ⇘ Γ'
      → Γ' ∋∙ punchIn k X
∋∙-weaken= Z (▶Z cloA) = S= Z
∋∙-weaken= Z (▶S∙ newΓ x) = Z
∋∙-weaken= (S, inΓ) (▶Z cloA) = S= (S, inΓ)
∋∙-weaken= (S, inΓ) (▶S, newΓ x) = S, (∋∙-weaken= inΓ newΓ)
∋∙-weaken= (S∙ inΓ) (▶Z cloA) = S= (S∙ inΓ)
∋∙-weaken= (S∙ inΓ) (▶S∙ newΓ x) = S∙ (∋∙-weaken= inΓ newΓ)
∋∙-weaken= (S= inΓ) (▶Z cloA) = S= (S= inΓ)
∋∙-weaken= (S= inΓ) (▶S= newΓ x x₁) = S= (∋∙-weaken= inΓ newΓ)
∋∙-weaken= (S^ inΓ) (▶Z cloA) = S= (S^ inΓ)
∋∙-weaken= (S^ inΓ) (▶S^ newΓ x) = S^ (∋∙-weaken= inΓ newΓ)
∋∙-weaken= (S⋈ inΓ) (▶Z regA) = S= (S⋈ inΓ)
∋∙-weaken= (S⋈ inΓ) (▶S⋈ newΓ) = S⋈ (∋∙-weaken= inΓ newΓ)


∋=-weaken= : Γ ∋= X
      → Γ ▶ k ,= T ⇘ Γ'
      → Γ' ∋= punchIn k X
∋=-weaken= Z (▶Z cloA) = S= Z
∋=-weaken= Z (▶S= newΓ x x₁) = Z
∋=-weaken= (S, inΓ) (▶Z cloA) = S= (S, inΓ)
∋=-weaken= (S, inΓ) (▶S, newΓ x) = S, (∋=-weaken= inΓ newΓ)
∋=-weaken= (S∙ inΓ) (▶Z cloA) = S= (S∙ inΓ)
∋=-weaken= (S∙ inΓ) (▶S∙ newΓ x) = S∙ (∋=-weaken= inΓ newΓ)
∋=-weaken= (S= inΓ) (▶Z cloA) = S= (S= inΓ)
∋=-weaken= (S= inΓ) (▶S= newΓ x x₁) = S= (∋=-weaken= inΓ newΓ)
∋=-weaken= (S^ inΓ) (▶Z cloA) = S= (S^ inΓ)
∋=-weaken= (S^ inΓ) (▶S^ newΓ x) = S^ (∋=-weaken= inΓ newΓ)

⊢r-weaken= : Γ ⊢r A
           → Γ ▶ k ,= T ⇘ Γ'
           → A ↑ty k ⇘ A'
           → Γ' ⊢r A'
⊢r-weaken= ⊢r-int new ↑ty-int = ⊢r-int
⊢r-weaken= (⊢r-var-∙ inΓ) new ↑ty-var = ⊢r-var-∙ (∋∙-weaken= inΓ new)
⊢r-weaken= (⊢r-arr regA regA₁) new (↑ty-arr upA upA₁) = ⊢r-arr (⊢r-weaken= regA new upA) (⊢r-weaken= regA₁ new upA₁)
⊢r-weaken= {T = T} (⊢r-∀ regA) new (↑ty-∀ upA)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢r-∀ (⊢r-weaken= regA (▶S∙ new upT) upA)
