module Implicit.Language.EnvOps.Strengthen.Lookup where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.All
open import Implicit.Language.EnvOps.Strengthen.Base

∋∙-strengthen : Γ ∋∙ punchIn k X
      → Γ ◀ k ⇘ Γ'
      → Γ' ∋∙ X
∋∙-strengthen {k = #0} {#0} (S, inΓ) (◀S, new up) = S, (∋∙-strengthen inΓ new)
∋∙-strengthen {k = #0} {#0} (S∙ inΓ) ◀Z∙ = inΓ
∋∙-strengthen {k = #0} {#0} (S= inΓ) ◀Z= = inΓ
∋∙-strengthen {k = #0} {#0} (S^ inΓ) ◀Z^ = inΓ
∋∙-strengthen {k = #0} {#0} (S⋈ inΓ) (◀S⋈ new) = S⋈ (∋∙-strengthen inΓ new)
∋∙-strengthen {k = #0} {#S X} (S, inΓ) (◀S, new up) = S, (∋∙-strengthen inΓ new)
∋∙-strengthen {k = #0} {#S X} (S∙ inΓ) ◀Z∙ = inΓ
∋∙-strengthen {k = #0} {#S X} (S= inΓ) ◀Z= = inΓ
∋∙-strengthen {k = #0} {#S X} (S^ inΓ) ◀Z^ = inΓ
∋∙-strengthen {k = #0} {#S X} (S⋈ inΓ) (◀S⋈ new) = S⋈ (∋∙-strengthen inΓ new)
∋∙-strengthen {k = #S k} {#0} Z (◀S∙ new) = Z
∋∙-strengthen {k = #S k} {#0} (S, inΓ) (◀S, new up) = S, (∋∙-strengthen inΓ new)
∋∙-strengthen {k = #S k} {#0} (S⋈ inΓ) (◀S⋈ new) = S⋈ (∋∙-strengthen inΓ new)
∋∙-strengthen {k = #S k} {#S X} (S, inΓ) (◀S, new up) = S, (∋∙-strengthen inΓ new)
∋∙-strengthen {k = #S k} {#S X} (S∙ inΓ) (◀S∙ new) = S∙ (∋∙-strengthen inΓ new)
∋∙-strengthen {k = #S k} {#S X} (S= inΓ) (◀S= new x) = S= (∋∙-strengthen inΓ new)
∋∙-strengthen {k = #S k} {#S X} (S^ inΓ) (◀S^ new) = S^ (∋∙-strengthen inΓ new)
∋∙-strengthen {k = #S k} {#S X} (S⋈ inΓ) (◀S⋈ new) = S⋈ (∋∙-strengthen inΓ new)


∋=-strengthen : Γ ∋= punchIn k X
      → Γ ◀ k ⇘ Γ'
      → Γ' ∋= X
∋=-strengthen {k = #0} {#0} (S∙ inΓ) ◀Z∙ = inΓ
∋=-strengthen {k = #0} {#0} (S^ inΓ) ◀Z^ = inΓ
∋=-strengthen {k = #0} {#0} (S= inΓ) ◀Z= = inΓ
∋=-strengthen {k = #0} {#0} (S, inΓ) (◀S, new up) = S, (∋=-strengthen inΓ new)
∋=-strengthen {k = #0} {#0} (S⋈ inΓ) (◀S⋈ new) = S⋈ (∋=-strengthen inΓ new)
∋=-strengthen {k = #0} {#S X} (S^ inΓ) ◀Z^ = inΓ
∋=-strengthen {k = #0} {#S X} (S= inΓ) ◀Z= = inΓ
∋=-strengthen {k = #0} {#S X} (S∙ inΓ) ◀Z∙ = inΓ
∋=-strengthen {k = #0} {#S X} (S, inΓ) (◀S, new up) = S, (∋=-strengthen inΓ new)
∋=-strengthen {k = #0} {#S X} (S⋈ inΓ) (◀S⋈ new) = S⋈ (∋=-strengthen inΓ new)
∋=-strengthen {k = #S k} {#0} Z (◀S= new x) = Z
∋=-strengthen {k = #S k} {#0} (S, inΓ) (◀S, new up) = S, (∋=-strengthen inΓ new)
∋=-strengthen {k = #S k} {#0} (S⋈ inΓ) (◀S⋈ new) = S⋈ (∋=-strengthen inΓ new)
∋=-strengthen {k = #S k} {#S X} (S∙ inΓ) (◀S∙ new) = S∙ (∋=-strengthen inΓ new)
∋=-strengthen {k = #S k} {#S X} (S^ inΓ) (◀S^ new) = S^ (∋=-strengthen inΓ new)
∋=-strengthen {k = #S k} {#S X} (S= inΓ) (◀S= new x) = S= (∋=-strengthen inΓ new)
∋=-strengthen {k = #S k} {#S X} (S, inΓ) (◀S, new up) = S, (∋=-strengthen inΓ new)
∋=-strengthen {k = #S k} {#S X} (S⋈ inΓ) (◀S⋈ new) = S⋈ (∋=-strengthen inΓ new)

∋^-strengthen : Γ ∋^ punchIn k X
      → Γ ◀ k ⇘ Γ'
      → Γ' ∋^ X
∋^-strengthen {k = #0} {X = #0} (S∙ inΓ) ◀Z∙ = inΓ
∋^-strengthen {k = #0} {X = #0} (S= inΓ) ◀Z= = inΓ
∋^-strengthen {k = #0} {X = #0} (S^ inΓ) ◀Z^ = inΓ
∋^-strengthen {k = #0} {X = #0} (S, inΓ) (◀S, new up) = S, (∋^-strengthen inΓ new)
∋^-strengthen {k = #0} {X = #0} (S⋈ inΓ) (◀S⋈ new) = S⋈ (∋^-strengthen inΓ new)
∋^-strengthen {k = #0} {X = #S X} (S∙ inΓ) ◀Z∙ = inΓ
∋^-strengthen {k = #0} {X = #S X} (S= inΓ) ◀Z= = inΓ
∋^-strengthen {k = #0} {X = #S X} (S^ inΓ) ◀Z^ = inΓ
∋^-strengthen {k = #0} {X = #S X} (S, inΓ) (◀S, new up) = S, (∋^-strengthen inΓ new)
∋^-strengthen {k = #0} {X = #S X} (S⋈ inΓ) (◀S⋈ new) = S⋈ (∋^-strengthen inΓ new)
∋^-strengthen {k = #S k} {X = #0} Z (◀S^ new) = Z
∋^-strengthen {k = #S k} {X = #0} (S, inΓ) (◀S, new up) = S, (∋^-strengthen inΓ new)
∋^-strengthen {k = #S k} {X = #0} (S⋈ inΓ) (◀S⋈ new) = S⋈ (∋^-strengthen inΓ new)
∋^-strengthen {k = #S k} {X = #S X} (S, inΓ) (◀S, new up) = S, (∋^-strengthen inΓ new)
∋^-strengthen {k = #S k} {X = #S X} (S^ inΓ) (◀S^ new) = S^ (∋^-strengthen inΓ new)
∋^-strengthen {k = #S k} {X = #S X} (S∙ inΓ) (◀S∙ new) = S∙ (∋^-strengthen inΓ new)
∋^-strengthen {k = #S k} {X = #S X} (S= inΓ) (◀S= new x) = S= (∋^-strengthen inΓ new)
∋^-strengthen {k = #S k} {X = #S X} (S⋈ inΓ) (◀S⋈ new) = S⋈ (∋^-strengthen inΓ new)



∋⦂-strengthen= : Γ ∋ x ⦂ A'
               → Regular Γ
               → Γ ◀ k ⇘ Γ'
               → A ↑ty k ⇘ A'
               → Γ' ∋ x ⦂ A
∋⦂-strengthen= Z (reg-S, regΓ regA) (◀S, newΓ up) upA with refl ← ↑ty-unique-inver upA up = Z
∋⦂-strengthen= (S, inΓ) (reg-S, regΓ regA) (◀S, newΓ up) upA = S, (∋⦂-strengthen= inΓ regΓ newΓ upA)
∋⦂-strengthen= (S∙ inΓ up) (reg-S∙ regΓ) (◀S∙ newΓ) upA
  with regA ← ∋⦂-⊢r regΓ inΓ
  with ⟨ pA , uppA ⟩ ← ⊢r-◀=-↑ty-surjective regA newΓ = S∙ (∋⦂-strengthen= inΓ regΓ newΓ uppA) (↑ty-comm1 upA up uppA)
∋⦂-strengthen= (S^ inΓ up) (reg-S^ regΓ) (◀S^ newΓ) upA
  with regA ← ∋⦂-⊢r regΓ inΓ
  with ⟨ pA , uppA ⟩ ← ⊢r-◀=-↑ty-surjective regA newΓ = S^ (∋⦂-strengthen= inΓ regΓ newΓ uppA) (↑ty-comm1 upA up uppA)
∋⦂-strengthen= (S= inΓ up) (reg-S= regΓ regA) ◀Z upA with refl ← ↑ty-unique-inver up upA = inΓ
∋⦂-strengthen= (S= inΓ up) (reg-S= regΓ regA) (◀S= newΓ x) upA
  with regA ← ∋⦂-⊢r regΓ inΓ
  with ⟨ pA , uppA ⟩ ← ⊢r-◀=-↑ty-surjective regA newΓ = S= (∋⦂-strengthen= inΓ regΓ newΓ uppA) (↑ty-comm1 upA up uppA)
∋⦂-strengthen= (S⋈ inΓ) regΓ new upA = {!!}
