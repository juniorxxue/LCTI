module Implicit.Language.EnvOps.RemoveSVar where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.Base
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Ground.Base

-- remove solution entry, without doing subst
infix 3 _◀_=⇘_
data _◀_=⇘_ : Env n (1 + m) → Fin (1 + m) → Env n m → Set where
  ◀Z  : Γ ,= T ◀ #0 =⇘ Γ
  ◀S, : Γ ◀ k =⇘ Γ'
      → B ↑ty k ⇘ B'
      → Γ , B' ◀ k =⇘ Γ' , B
  ◀S^ : Γ ◀ k =⇘ Γ'
      → Γ ,^ ◀ #S k =⇘ Γ' ,^
  ◀S∙ : Γ ◀ k =⇘ Γ'
      → Γ ,∙ ◀ #S k =⇘ Γ' ,∙
  ◀S= : Γ ◀ k =⇘ Γ'
      → A ↑ty k ⇘ A'
      → Γ ,= A' ◀ #S k =⇘ Γ' ,= A
  ◀S⋈ : Γ ◀ k =⇘ Γ'
      → Γ ⋈ ◀ k =⇘ Γ' ⋈

∋∙-strengthen= : Γ ∋∙ punchIn k X
      → Γ ◀ k =⇘ Γ'
      → Γ' ∋∙ X
∋∙-strengthen= {k = #0} {#0} (S, inΓ) (◀S, newΓ x) = S, (∋∙-strengthen= inΓ newΓ)
∋∙-strengthen= {k = #0} {#0} (S= inΓ) ◀Z = inΓ
∋∙-strengthen= {k = #0} {#S X} (S, inΓ) (◀S, newΓ x) = S, (∋∙-strengthen= inΓ newΓ)
∋∙-strengthen= {k = #0} {#S X} (S= inΓ) ◀Z = inΓ
∋∙-strengthen= {k = #S k} {#0} Z (◀S∙ newΓ) = Z
∋∙-strengthen= {k = #S k} {#0} (S, inΓ) (◀S, newΓ x) = S, (∋∙-strengthen= inΓ newΓ)
∋∙-strengthen= {k = #S k} {#S X} (S, inΓ) (◀S, newΓ x) = S, (∋∙-strengthen= inΓ newΓ)
∋∙-strengthen= {k = #S k} {#S X} (S∙ inΓ) (◀S∙ newΓ) = S∙ (∋∙-strengthen= inΓ newΓ)
∋∙-strengthen= {k = #S k} {#S X} (S= inΓ) (◀S= newΓ x) = S= (∋∙-strengthen= inΓ newΓ)
∋∙-strengthen= {k = #S k} {#S X} (S^ inΓ) (◀S^ newΓ) = S^ (∋∙-strengthen= inΓ newΓ)
∋∙-strengthen= (S⋈ inΓ) (◀S⋈ newΓ) = S⋈ (∋∙-strengthen= inΓ newΓ)

∋=-strengthen= : Γ ∋= punchIn k X
      → Γ ◀ k =⇘ Γ'
      → Γ' ∋= X
∋=-strengthen= {k = #0} {#0} (S= inΓ) ◀Z = inΓ
∋=-strengthen= {k = #0} {#S X} (S= inΓ) ◀Z = inΓ
∋=-strengthen= {k = #S k} {#0} Z (◀S= newΓ x) = Z
∋=-strengthen= {k = #S k} {#S X} (S∙ inΓ) (◀S∙ newΓ) = S∙ (∋=-strengthen= inΓ newΓ)
∋=-strengthen= {k = #S k} {#S X} (S^ inΓ) (◀S^ newΓ) = S^ (∋=-strengthen= inΓ newΓ)
∋=-strengthen= {k = #S k} {#S X} (S= inΓ) (◀S= newΓ x) = S= (∋=-strengthen= inΓ newΓ)

∋:=-strengthen=' : Γ ∋ punchIn k X := A'
        → Γ ◀ k =⇘ Γ'
        → Γ' ∋ X := A
        → A ↑ty k ⇘ A'
∋:=-strengthen=' {k = #0} {#0} (S= (Z up₂) up) ◀Z (Z up₁) with ↑ty-unique up₁ up₂
... | refl = up
∋:=-strengthen=' {k = #0} {#S X} (S= inΓ up) ◀Z inΓ' with ∋:=-unique inΓ inΓ'
... | refl = up
∋:=-strengthen=' {k = #S k} {#0} (Z up) (◀S= newΓ x) (Z up₁) = ↑ty-comm' z≤n x up up₁
∋:=-strengthen=' {k = #S k} {#S X} (S∙ inΓ up) (◀S∙ newΓ) (S∙ inΓ' up₁) = ↑ty-comm' z≤n (∋:=-strengthen=' inΓ newΓ inΓ') up up₁
∋:=-strengthen=' {k = #S k} {#S X} (S^ inΓ up) (◀S^ newΓ) (S^ inΓ' up₁) = ↑ty-comm' z≤n (∋:=-strengthen=' inΓ newΓ inΓ') up up₁
∋:=-strengthen=' {k = #S k} {#S X} (S= inΓ up) (◀S= newΓ x) (S= inΓ' up₁) = ↑ty-comm' z≤n (∋:=-strengthen=' inΓ newΓ inΓ') up up₁
