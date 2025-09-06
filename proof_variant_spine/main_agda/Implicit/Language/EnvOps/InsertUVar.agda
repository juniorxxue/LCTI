module Implicit.Language.EnvOps.InsertUVar where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Subst.All
open import Implicit.Language.Lookup.All

open import Implicit.Language.Regular.All
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
  ▶S⋈ : Γ ▶ k ,∙⇘ Γ'
      → Γ ⋈ ▶ k ,∙⇘ Γ' ⋈


▶∙-∋∙ : Γ ▶ k ,∙⇘ Γ'
      → Γ' ∋∙ k
▶∙-∋∙ ▶Z = Z
▶∙-∋∙ (▶S, new x) = S, (▶∙-∋∙ new)
▶∙-∋∙ (▶S^ new) = S^ (▶∙-∋∙ new)
▶∙-∋∙ (▶S∙ new) = S∙ (▶∙-∋∙ new)
▶∙-∋∙ (▶S= new x) = S= (▶∙-∋∙ new)
▶∙-∋∙ (▶S⋈ new) = S⋈ (▶∙-∋∙ new)


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


⊢r-weaken∙ : Γ ⊢r A
           → Γ ▶ k ,∙⇘ Γ'
           → A ↑ty k ⇘ A'
           → Γ' ⊢r A'
⊢r-weaken∙ ⊢r-int new ↑ty-int = ⊢r-int
⊢r-weaken∙ (⊢r-var-∙ inΓ) new ↑ty-var = ⊢r-var-∙ (∋∙-weaken∙ inΓ new)
⊢r-weaken∙ (⊢r-arr regA regA₁) new (↑ty-arr upA upA₁) = ⊢r-arr (⊢r-weaken∙ regA new upA) (⊢r-weaken∙ regA₁ new upA₁)
⊢r-weaken∙ (⊢r-∀ regA) new (↑ty-∀ upA) = ⊢r-∀ (⊢r-weaken∙ regA (▶S∙ new) upA)



▶∙-punchOut-helper : Γ ∋∙ X
                   → Γ ▶ #0 ,∙⇘ Γ'
                   → Γ' ∋∙ #S X
▶∙-punchOut-helper inΓ ▶Z = S∙ inΓ
▶∙-punchOut-helper (S, inΓ) (▶S, new x) = S, (▶∙-punchOut-helper inΓ new)
▶∙-punchOut-helper (S⋈ inΓ) (▶S⋈ new) = S⋈ (▶∙-punchOut-helper inΓ new)

▶∙-punchOut : (¬p : k ≢ X)
            → Γ ∋∙ punchOut ¬p
            → Γ ▶ k ,∙⇘ Γ'
            → Γ' ∋∙ X
▶∙-punchOut {k = #0} {X = #0} ¬p inΓ new = ⊥-elim (¬p refl)
▶∙-punchOut {k = #0} {X = #S X} ¬p inΓ ▶Z = S∙ inΓ
▶∙-punchOut {k = #0} {X = #S X} ¬p (S, inΓ) (▶S, new x) = S, (▶∙-punchOut-helper inΓ new)
▶∙-punchOut {k = #0} {X = #S X} ¬p (S⋈ inΓ) (▶S⋈ new) = S⋈ (▶∙-punchOut-helper inΓ new)
▶∙-punchOut {k = #S k} {X = #0} ¬p (S, inΓ) (▶S, new x) = S, (▶∙-punchOut ¬p inΓ new)
▶∙-punchOut {k = #S k} {X = #0} ¬p inΓ (▶S∙ new) = Z
▶∙-punchOut {k = #S k} {X = #0} ¬p (S⋈ inΓ) (▶S⋈ new) = S⋈ (▶∙-punchOut ¬p inΓ new)
▶∙-punchOut {k = #S k} {X = #S X} ¬p (S, inΓ) (▶S, new x) = S, (▶∙-punchOut ¬p inΓ new)
▶∙-punchOut {k = #S k} {X = #S X} ¬p (S^ inΓ) (▶S^ new) = S^ (▶∙-punchOut (λ x → ¬p (cong #S x)) inΓ new)
▶∙-punchOut {k = #S k} {X = #S X} ¬p (S∙ inΓ) (▶S∙ new) = S∙ (▶∙-punchOut (λ x → ¬p (cong #S x)) inΓ new)
▶∙-punchOut {k = #S k} {X = #S X} ¬p (S= inΓ) (▶S= new x) = S= (▶∙-punchOut (λ x₁ → ¬p (cong #S x₁)) inΓ new)
▶∙-punchOut {k = #S k} {X = #S X} ¬p (S⋈ inΓ) (▶S⋈ new) = S⋈ (▶∙-punchOut ¬p inΓ new)

