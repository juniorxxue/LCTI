module Implicit.Language.Lookup.Remove where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.Base
open import Implicit.Language.Shift


◀,-∋∙ : Γ ∋∙ X
      → Γ ◀ k ,⇘ Γ'
      → Γ' ∋∙ X
◀,-∋∙ Z (◀S∙ newΓ') = Z
◀,-∋∙ (S, inΓ) ◀Z = inΓ
◀,-∋∙ (S, inΓ) (◀S, newΓ') = S, (◀,-∋∙ inΓ newΓ')
◀,-∋∙ (S∙ inΓ) (◀S∙ newΓ') = S∙ (◀,-∋∙ inΓ newΓ')
◀,-∋∙ (S= inΓ) (◀S= newΓ') = S= (◀,-∋∙ inΓ newΓ')
◀,-∋∙ (S^ inΓ) (◀S^ newΓ') = S^ (◀,-∋∙ inΓ newΓ')


◀,-∋= : Γ ∋= X
       → Γ ◀ k ,⇘ Γ'
       → Γ' ∋= X
◀,-∋= Z (◀S= newΓ') = Z
◀,-∋= (S, inΓ) ◀Z = inΓ
◀,-∋= (S, inΓ) (◀S, newΓ') = S, (◀,-∋= inΓ newΓ')
◀,-∋= (S∙ inΓ) (◀S∙ newΓ') = S∙ (◀,-∋= inΓ newΓ')
◀,-∋= (S^ inΓ) (◀S^ newΓ') = S^ (◀,-∋= inΓ newΓ')
◀,-∋= (S= inΓ) (◀S= newΓ') = S= (◀,-∋= inΓ newΓ')

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

◀=-∋∙ : Γ ∋∙ punchIn k X
      → Γ ◀ k =⇘ Γ'
      → Γ' ∋∙ X
◀=-∋∙ {k = #0} {#0} (S, inΓ) (◀S, newΓ x) = S, (◀=-∋∙ inΓ newΓ)
◀=-∋∙ {k = #0} {#0} (S= inΓ) ◀Z = inΓ
◀=-∋∙ {k = #0} {#S X} (S, inΓ) (◀S, newΓ x) = S, (◀=-∋∙ inΓ newΓ)
◀=-∋∙ {k = #0} {#S X} (S= inΓ) ◀Z = inΓ
◀=-∋∙ {k = #S k} {#0} Z (◀S∙ newΓ) = Z
◀=-∋∙ {k = #S k} {#0} (S, inΓ) (◀S, newΓ x) = S, (◀=-∋∙ inΓ newΓ)
◀=-∋∙ {k = #S k} {#S X} (S, inΓ) (◀S, newΓ x) = S, (◀=-∋∙ inΓ newΓ)
◀=-∋∙ {k = #S k} {#S X} (S∙ inΓ) (◀S∙ newΓ) = S∙ (◀=-∋∙ inΓ newΓ)
◀=-∋∙ {k = #S k} {#S X} (S= inΓ) (◀S= newΓ x) = S= (◀=-∋∙ inΓ newΓ)
◀=-∋∙ {k = #S k} {#S X} (S^ inΓ) (◀S^ newΓ) = S^ (◀=-∋∙ inΓ newΓ)

◀=-∋= : Γ ∋= punchIn k X
      → Γ ◀ k =⇘ Γ'
      → Γ' ∋= X
◀=-∋= {k = #0} {#0} (S, inΓ) (◀S, newΓ x) = S, (◀=-∋= inΓ newΓ)
◀=-∋= {k = #0} {#0} (S= inΓ) ◀Z = inΓ
◀=-∋= {k = #0} {#S X} (S= inΓ) ◀Z = inΓ
◀=-∋= {k = #0} {#S X} (S, inΓ) (◀S, newΓ x) = S, (◀=-∋= inΓ newΓ)
◀=-∋= {k = #S k} {#0} Z (◀S= newΓ x) = Z
◀=-∋= {k = #S k} {#0} (S, inΓ) (◀S, newΓ x) = S, (◀=-∋= inΓ newΓ)
◀=-∋= {k = #S k} {#S X} (S, inΓ) (◀S, newΓ x) = S, (◀=-∋= inΓ newΓ)
◀=-∋= {k = #S k} {#S X} (S∙ inΓ) (◀S∙ newΓ) = S∙ (◀=-∋= inΓ newΓ)
◀=-∋= {k = #S k} {#S X} (S^ inΓ) (◀S^ newΓ) = S^ (◀=-∋= inΓ newΓ)
◀=-∋= {k = #S k} {#S X} (S= inΓ) (◀S= newΓ x) = S= (◀=-∋= inΓ newΓ)
