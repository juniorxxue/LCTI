module Implicit.Language.EnvOps.Remove where

open import Implicit.Language.Base
open import Implicit.Language.Shift
open import Implicit.Language.Lookup
open import Implicit.Language.EnvOps.Base

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


◀,-∋⦂ : Γ ∋ punchIn k x ⦂ A
      → Γ ◀ k ,⇘ Γ'
      → Γ' ∋ x ⦂ A
◀,-∋⦂ {k = #0} {#0} (S, inΓ) ◀Z = inΓ
◀,-∋⦂ {k = #0} {#0} (S∙ inΓ up) (◀S∙ newΓ) = S∙ (◀,-∋⦂ inΓ newΓ) up
◀,-∋⦂ {k = #0} {#0} (S^ inΓ up) (◀S^ newΓ) = S^ (◀,-∋⦂ inΓ newΓ) up
◀,-∋⦂ {k = #0} {#0} (S= inΓ up) (◀S= newΓ) = S= (◀,-∋⦂ inΓ newΓ) up
◀,-∋⦂ {k = #0} {#S x} (S, inΓ) ◀Z = inΓ
◀,-∋⦂ {k = #0} {#S x} (S^ inΓ up) (◀S^ newΓ) = S^ (◀,-∋⦂ inΓ newΓ) up
◀,-∋⦂ {k = #0} {#S x} (S∙ inΓ up) (◀S∙ newΓ) = S∙ (◀,-∋⦂ inΓ newΓ) up
◀,-∋⦂ {k = #0} {#S x} (S= inΓ up) (◀S= newΓ) = S= (◀,-∋⦂ inΓ newΓ) up
◀,-∋⦂ {k = #S k} {#0} Z (◀S, newΓ) = Z
◀,-∋⦂ {k = #S k} {#0} (S∙ inΓ up) (◀S∙ newΓ) = S∙ (◀,-∋⦂ inΓ newΓ) up
◀,-∋⦂ {k = #S k} {#0} (S^ inΓ up) (◀S^ newΓ) = S^ (◀,-∋⦂ inΓ newΓ) up
◀,-∋⦂ {k = #S k} {#0} (S= inΓ up) (◀S= newΓ) = S= (◀,-∋⦂ inΓ newΓ) up
◀,-∋⦂ {k = #S k} {#S x} (S, inΓ) (◀S, newΓ) = S, (◀,-∋⦂ inΓ newΓ)
◀,-∋⦂ {k = #S k} {#S x} (S∙ inΓ up) (◀S∙ newΓ) = S∙ (◀,-∋⦂ inΓ newΓ) up
◀,-∋⦂ {k = #S k} {#S x} (S^ inΓ up) (◀S^ newΓ) = S^ (◀,-∋⦂ inΓ newΓ) up
◀,-∋⦂ {k = #S k} {#S x} (S= inΓ up) (◀S= newΓ) = S= (◀,-∋⦂ inΓ newΓ) up

◀,-∋:= : Γ ∋ X := A
       → Γ ◀ k ,⇘ Γ'
       → Γ' ∋ X := A
◀,-∋:= (Z up) (◀S= newΓ) = Z up
◀,-∋:= (S, inΓ) ◀Z = inΓ
◀,-∋:= (S, inΓ) (◀S, newΓ) = S, (◀,-∋:= inΓ newΓ)
◀,-∋:= (S∙ inΓ up) (◀S∙ newΓ) = S∙ (◀,-∋:= inΓ newΓ) up
◀,-∋:= (S^ inΓ up) (◀S^ newΓ) = S^ (◀,-∋:= inΓ newΓ) up
◀,-∋:= (S= inΓ up) (◀S= newΓ) = S= (◀,-∋:= inΓ newΓ) up
