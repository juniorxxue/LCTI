module Implicit.Language.EnvOps.Remove where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.EnvOps.Base



◀^-∋∙ : Γ ∋∙ punchIn k X
      → Γ ◀ k ^⇘ Γ'
      → Γ' ∋∙ X
◀^-∋∙ {k = #0} (S, inΓ) (◀S, newΓ x) = S, (◀^-∋∙ inΓ newΓ)
◀^-∋∙ {k = #0} (S^ inΓ) ◀Z = inΓ
◀^-∋∙ {k = #S k} {#0} Z (◀S∙ newΓ) = Z
◀^-∋∙ {k = #S k} {#0} (S, inΓ) (◀S, newΓ x) = S, (◀^-∋∙ inΓ newΓ)
◀^-∋∙ {k = #S k} {#S X} (S, inΓ) (◀S, newΓ x) = S, (◀^-∋∙ inΓ newΓ)
◀^-∋∙ {k = #S k} {#S X} (S∙ inΓ) (◀S∙ newΓ) = S∙ (◀^-∋∙ inΓ newΓ)
◀^-∋∙ {k = #S k} {#S X} (S= inΓ) (◀S= newΓ x) = S= (◀^-∋∙ inΓ newΓ)
◀^-∋∙ {k = #S k} {#S X} (S^ inΓ) (◀S^ newΓ) = S^ (◀^-∋∙ inΓ newΓ)

◀∙-∋∙ : Γ ∋∙ punchIn k X
      → Γ ◀ k ∙⇘ Γ'
      → Γ' ∋∙ X
◀∙-∋∙ {k = #0} (S, inΓ) (◀S, newΓ x) = S, (◀∙-∋∙ inΓ newΓ)
◀∙-∋∙ {k = #0} (S∙ inΓ) ◀Z = inΓ
◀∙-∋∙ {k = #S k} {#0} Z (◀S∙ newΓ) = Z
◀∙-∋∙ {k = #S k} {#0} (S, inΓ) (◀S, newΓ x) = S, (◀∙-∋∙ inΓ newΓ)
◀∙-∋∙ {k = #S k} {#S X} (S, inΓ) (◀S, newΓ x) = S, (◀∙-∋∙ inΓ newΓ)
◀∙-∋∙ {k = #S k} {#S X} (S∙ inΓ) (◀S∙ newΓ) = S∙ (◀∙-∋∙ inΓ newΓ)
◀∙-∋∙ {k = #S k} {#S X} (S= inΓ) (◀S= newΓ x) = S= (◀∙-∋∙ inΓ newΓ)
◀∙-∋∙ {k = #S k} {#S X} (S^ inΓ) (◀S^ newΓ) = S^ (◀∙-∋∙ inΓ newΓ)

◀∙-∋= : Γ ∋= punchIn k X
      → Γ ◀ k ∙⇘ Γ'
      → Γ' ∋= X
◀∙-∋= {k = #0} (S, inΓ) (◀S, newΓ x) = S, (◀∙-∋= inΓ newΓ)
◀∙-∋= {k = #0} (S∙ inΓ) ◀Z = inΓ
◀∙-∋= {k = #S k} {#0} Z (◀S= newΓ x) = Z
◀∙-∋= {k = #S k} {#0} (S, inΓ) (◀S, newΓ x) = S, (◀∙-∋= inΓ newΓ)
◀∙-∋= {k = #S k} {#S X} (S, inΓ) (◀S, newΓ x) = S, (◀∙-∋= inΓ newΓ)
◀∙-∋= {k = #S k} {#S X} (S∙ inΓ) (◀S∙ newΓ) = S∙ (◀∙-∋= inΓ newΓ)
◀∙-∋= {k = #S k} {#S X} (S= inΓ) (◀S= newΓ x) = S= (◀∙-∋= inΓ newΓ)
◀∙-∋= {k = #S k} {#S X} (S^ inΓ) (◀S^ newΓ) = S^ (◀∙-∋= inΓ newΓ)


◀^-∋= : Γ ∋= punchIn k X
      → Γ ◀ k ^⇘ Γ'
      → Γ' ∋= X
◀^-∋= {k = #0} (S, inΓ) (◀S, newΓ x) = S, (◀^-∋= inΓ newΓ)
◀^-∋= {k = #0} (S^ inΓ) ◀Z = inΓ
◀^-∋= {k = #S k} {#0} Z (◀S= inΓ x) = Z
◀^-∋= {k = #S k} {#0} (S, inΓ) (◀S, newΓ x) = S, (◀^-∋= inΓ newΓ)
◀^-∋= {k = #S k} {#S X} (S, inΓ) (◀S, newΓ x) = S, (◀^-∋= inΓ newΓ)
◀^-∋= {k = #S k} {#S X} (S∙ inΓ) (◀S∙ newΓ) = S∙ (◀^-∋= inΓ newΓ)
◀^-∋= {k = #S k} {#S X} (S= inΓ) (◀S= newΓ x) = S= (◀^-∋= inΓ newΓ)
◀^-∋= {k = #S k} {#S X} (S^ inΓ) (◀S^ newΓ) = S^ (◀^-∋= inΓ newΓ)





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

◀^-∋:=' : Γ ∋ punchIn k X := A'
        → Γ ◀ k ^⇘ Γ'
        → Γ' ∋ X := A
        → A ↑ty k ⇘ A'
◀^-∋:=' {k = #0} {#0} (S, inΓ) (◀S, newΓ x) (S, inΓ') = ◀^-∋:=' inΓ newΓ inΓ'
◀^-∋:=' {k = #0} {#0} (S^ (Z up₂) up) ◀Z (Z up₁) with ↑ty-unique up₁ up₂
... | refl = up
◀^-∋:=' {k = #0} {#0} (S^ (S, inΓ) up) ◀Z (S, inΓ') with ∋:=-unique inΓ inΓ'
... | refl = up
◀^-∋:=' {k = #0} {#S X} (S, inΓ) (◀S, newΓ x) (S, inΓ') = ◀^-∋:=' inΓ newΓ inΓ'
◀^-∋:=' {k = #0} {#S X} (S^ inΓ up) ◀Z inΓ' with ∋:=-unique inΓ inΓ'
... | refl = up
◀^-∋:=' {k = #S k} {#0} (Z up) (◀S= newΓ x) (Z up₁) = ↑ty-comm' z≤n x up up₁
◀^-∋:=' {k = #S k} {#0} (S, inΓ) (◀S, newΓ x) (S, inΓ') = ◀^-∋:=' inΓ newΓ inΓ'
◀^-∋:=' {k = #S k} {#S X} (S, inΓ) (◀S, newΓ x) (S, inΓ') = ◀^-∋:=' inΓ newΓ inΓ'
◀^-∋:=' {k = #S k} {#S X} (S∙ inΓ up) (◀S∙ newΓ) (S∙ inΓ' up₁) = ↑ty-comm' z≤n (◀^-∋:=' inΓ newΓ inΓ') up up₁
◀^-∋:=' {k = #S k} {#S X} (S^ inΓ up) (◀S^ newΓ) (S^ inΓ' up₁) = ↑ty-comm' z≤n (◀^-∋:=' inΓ newΓ inΓ') up up₁
◀^-∋:=' {k = #S k} {#S X} (S= inΓ up) (◀S= newΓ x) (S= inΓ' up₁) = ↑ty-comm' z≤n (◀^-∋:=' inΓ newΓ inΓ') up up₁


