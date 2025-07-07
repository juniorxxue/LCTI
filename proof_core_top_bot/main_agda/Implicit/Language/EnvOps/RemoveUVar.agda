module Implicit.Language.EnvOps.RemoveUVar where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.All
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Ground.Base
open import Implicit.Language.Occur.All

-- remove type variable a from k-th posititon
infix 3 _◀_∙⇘_
data _◀_∙⇘_ : Env n (1 + m) → Fin (1 + m) → Env n m → Set where
  ◀Z  : Γ ,∙ ◀ #0 ∙⇘ Γ
  ◀S, : Γ ◀ k ∙⇘ Γ'
      → A ↑ty k ⇘ A'
      → Γ , A' ◀ k ∙⇘ Γ' , A
  ◀S^ : Γ ◀ k ∙⇘ Γ'
      → Γ ,^ ◀ #S k ∙⇘ Γ' ,^
  ◀S∙ : Γ ◀ k ∙⇘ Γ'
      → Γ ,∙ ◀ #S k ∙⇘ Γ' ,∙
  ◀S= : Γ ◀ k ∙⇘ Γ'
      → A ↑ty k ⇘ A'
      → Γ ,= A' ◀ #S k ∙⇘ Γ' ,= A
  ◀S⋈ : Γ ◀ k ∙⇘ Γ'
      → Γ ⋈ ◀ k ∙⇘ Γ' ⋈

◀∙-∋∙ : Γ ◀ k ∙⇘ Γ'
      → Γ ∋∙ k
◀∙-∋∙ ◀Z = Z
◀∙-∋∙ (◀S, new x) = S, (◀∙-∋∙ new)
◀∙-∋∙ (◀S^ new) = S^ (◀∙-∋∙ new)
◀∙-∋∙ (◀S∙ new) = S∙ (◀∙-∋∙ new)
◀∙-∋∙ (◀S= new x) = S= (◀∙-∋∙ new)
◀∙-∋∙ (◀S⋈ new) = S⋈ (◀∙-∋∙ new)

∋∙-strengthen∙' : (¬p : k ≢ X)
                → Γ' ∋∙ punchOut ¬p
                → Γ ◀ k ∙⇘ Γ'
                → Γ ∋∙ X
∋∙-strengthen∙' {k = #0} {X = #0} ¬p inΓ new = ⊥-elim (¬p refl)
∋∙-strengthen∙' {k = #0} {X = #S X} ¬p inΓ ◀Z = S∙ inΓ
∋∙-strengthen∙' {k = #0} {X = #S X} ¬p (S, inΓ) (◀S, new x) = S, (∋∙-strengthen∙' (λ ()) inΓ new)
∋∙-strengthen∙' {k = #0} {X = #S X} ¬p (S⋈ inΓ) (◀S⋈ new) = S⋈ (∋∙-strengthen∙' (λ ()) inΓ new)
∋∙-strengthen∙' {k = #S k} {X = #0} ¬p (S, inΓ) (◀S, new x) = S, (∋∙-strengthen∙' ¬p inΓ new)
∋∙-strengthen∙' {k = #S k} {X = #0} ¬p Z (◀S∙ new) = Z
∋∙-strengthen∙' {k = #S k} {X = #0} ¬p (S⋈ inΓ) (◀S⋈ new) = S⋈ (∋∙-strengthen∙' ¬p inΓ new)
∋∙-strengthen∙' {k = #S k} {X = #S X} ¬p (S, inΓ) (◀S, new x) = S, (∋∙-strengthen∙' ¬p inΓ new)
∋∙-strengthen∙' {k = #S k} {X = #S X} ¬p (S^ inΓ) (◀S^ new) = S^ (∋∙-strengthen∙' (λ x → ¬p (cong #S x)) inΓ new)
∋∙-strengthen∙' {k = #S k} {X = #S X} ¬p (S∙ inΓ) (◀S∙ new) = S∙ (∋∙-strengthen∙' (λ x → ¬p (cong #S x)) inΓ new)
∋∙-strengthen∙' {k = #S k} {X = #S X} ¬p (S= inΓ) (◀S= new x) = S= (∋∙-strengthen∙' (λ x₁ → ¬p (cong #S x₁)) inΓ new)
∋∙-strengthen∙' {k = #S k} {X = #S X} ¬p (S⋈ inΓ) (◀S⋈ new) = S⋈ (∋∙-strengthen∙' ¬p inΓ new)


∋∙-strengthen∙ : Γ ∋∙ punchIn k X
      → Γ ◀ k ∙⇘ Γ'
      → Γ' ∋∙ X
∋∙-strengthen∙ {k = #0} (S, inΓ) (◀S, newΓ x) = S, (∋∙-strengthen∙ inΓ newΓ)
∋∙-strengthen∙ {k = #0} (S∙ inΓ) ◀Z = inΓ
∋∙-strengthen∙ {k = #S k} {#0} Z (◀S∙ newΓ) = Z
∋∙-strengthen∙ {k = #S k} {#0} (S, inΓ) (◀S, newΓ x) = S, (∋∙-strengthen∙ inΓ newΓ)
∋∙-strengthen∙ {k = #S k} {#S X} (S, inΓ) (◀S, newΓ x) = S, (∋∙-strengthen∙ inΓ newΓ)
∋∙-strengthen∙ {k = #S k} {#S X} (S∙ inΓ) (◀S∙ newΓ) = S∙ (∋∙-strengthen∙ inΓ newΓ)
∋∙-strengthen∙ {k = #S k} {#S X} (S= inΓ) (◀S= newΓ x) = S= (∋∙-strengthen∙ inΓ newΓ)
∋∙-strengthen∙ {k = #S k} {#S X} (S^ inΓ) (◀S^ newΓ) = S^ (∋∙-strengthen∙ inΓ newΓ)
∋∙-strengthen∙ (S⋈ inΓ) (◀S⋈ newΓ) = S⋈ (∋∙-strengthen∙ inΓ newΓ)

∋=-strengthen∙ : Γ ∋= punchIn k X
      → Γ ◀ k ∙⇘ Γ'
      → Γ' ∋= X
∋=-strengthen∙ {k = #0} (S, inΓ) (◀S, newΓ x) = S, (∋=-strengthen∙ inΓ newΓ)
∋=-strengthen∙ {k = #0} (S∙ inΓ) ◀Z = inΓ
∋=-strengthen∙ {k = #S k} {#0} Z (◀S= newΓ x) = Z
∋=-strengthen∙ {k = #S k} {#0} (S, inΓ) (◀S, newΓ x) = S, (∋=-strengthen∙ inΓ newΓ)
∋=-strengthen∙ {k = #S k} {#S X} (S, inΓ) (◀S, newΓ x) = S, (∋=-strengthen∙ inΓ newΓ)
∋=-strengthen∙ {k = #S k} {#S X} (S∙ inΓ) (◀S∙ newΓ) = S∙ (∋=-strengthen∙ inΓ newΓ)
∋=-strengthen∙ {k = #S k} {#S X} (S= inΓ) (◀S= newΓ x) = S= (∋=-strengthen∙ inΓ newΓ)
∋=-strengthen∙ {k = #S k} {#S X} (S^ inΓ) (◀S^ newΓ) = S^ (∋=-strengthen∙ inΓ newΓ)
{-
◀∙-∋:=' : Γ ∋ punchIn k X := A'
        → Γ ◀ k ∙⇘ Γ'
        → Γ' ∋ X := A
        → A ↑ty k ⇘ A'
◀∙-∋:=' {k = #0} {#0} (S, inΓ) (◀S, newΓ x) (S, inΓ') = ◀∙-∋:=' inΓ newΓ inΓ'
◀∙-∋:=' {k = #0} {#0} (S∙ (Z up₂) up) ◀Z (Z up₁) with ↑ty-unique up₁ up₂
... | refl = up
◀∙-∋:=' {k = #0} {#0} (S∙ (S, inΓ) up) ◀Z (S, inΓ') with ∋:=-unique inΓ inΓ'
... | refl = up
◀∙-∋:=' {k = #0} {#S X} (S, inΓ) (◀S, newΓ x) (S, inΓ') = ◀∙-∋:=' inΓ newΓ inΓ'
◀∙-∋:=' {k = #0} {#S X} (S∙ inΓ up) ◀Z inΓ' with ∋:=-unique inΓ inΓ'
... | refl = up
◀∙-∋:=' {k = #S k} {#0} (Z up) (◀S= newΓ x) (Z up₁) = ↑ty-comm' z≤n x up up₁
◀∙-∋:=' {k = #S k} {#0} (S, inΓ) (◀S, newΓ x) (S, inΓ') = ◀∙-∋:=' inΓ newΓ inΓ'
◀∙-∋:=' {k = #S k} {#S X} (S, inΓ) (◀S, newΓ x) (S, inΓ') = ◀∙-∋:=' inΓ newΓ inΓ'
◀∙-∋:=' {k = #S k} {#S X} (S∙ inΓ up) (◀S∙ newΓ) (S∙ inΓ' up₁) = ↑ty-comm' z≤n (◀∙-∋:=' inΓ newΓ inΓ') up up₁
◀∙-∋:=' {k = #S k} {#S X} (S^ inΓ up) (◀S^ newΓ) (S^ inΓ' up₁) = ↑ty-comm' z≤n (◀∙-∋:=' inΓ newΓ inΓ') up up₁
◀∙-∋:=' {k = #S k} {#S X} (S= inΓ up) (◀S= newΓ x) (S= inΓ' up₁) = ↑ty-comm' z≤n (◀∙-∋:=' inΓ newΓ inΓ') up up₁
-}

⊢r-strengthen∙ : Γ ⊢r A'
               → Γ ◀ k ∙⇘ Γ'
               → A ↑ty k ⇘ A'
               → Γ' ⊢r A
⊢r-strengthen∙ ⊢r-int new ↑ty-int = ⊢r-int
⊢r-strengthen∙ ⊢r-top new ↑ty-top = ⊢r-top
⊢r-strengthen∙ ⊢r-bot new ↑ty-bot = ⊢r-bot
⊢r-strengthen∙ (⊢r-var-∙ inΓ) new ↑ty-var = ⊢r-var-∙ (∋∙-strengthen∙ inΓ new)
⊢r-strengthen∙ (⊢r-arr regA regA₁) new (↑ty-arr upA upA₁) = ⊢r-arr (⊢r-strengthen∙ regA new upA)
                                                                   (⊢r-strengthen∙ regA₁ new upA₁)
⊢r-strengthen∙ (⊢r-∀ regA) new (↑ty-∀ upA) = ⊢r-∀ (⊢r-strengthen∙ regA (◀S∙ new) upA)
