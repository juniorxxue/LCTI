module Implicit.Language.EnvOps.Strengthen.Lookup where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.All
open import Implicit.Language.Occur.All
open import Implicit.Language.EnvOps.Regular
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

∋⦂-strengthen : Γ ∋ x ⦂ A'
               → k ¬εᵍ Γ
               → Γ ◀ k ⇘ Γ'
               → A ↑ty k ⇘ A'
               → Γ' ∋ x ⦂ A
∋⦂-strengthen Z (S, x ninΓ) (◀S, newΓ up) upA
  with refl ← ↑ty-unique-inver upA up = Z
∋⦂-strengthen (S, inΓ) (S, x ninΓ) (◀S, newΓ up) upA = S, (∋⦂-strengthen inΓ ninΓ newΓ upA)
∋⦂-strengthen (S∙ inΓ up) Z∙ ◀Z∙ upA
  with refl ← ↑ty-unique-inver upA up = inΓ
∋⦂-strengthen (S∙ inΓ up) (S∙ ninΓ) (◀S∙ newΓ) upA
  with ninA ← εᵍ-⦂-¬ε ninΓ inΓ
  with ⟨ pA , uppA ⟩ ← ↑ty-surjective ninA
  = S∙ (∋⦂-strengthen inΓ ninΓ newΓ uppA) (↑ty-comm1 upA up uppA)
∋⦂-strengthen (S^ inΓ up) Z^ ◀Z^ upA
  with refl ← ↑ty-unique-inver upA up = inΓ
∋⦂-strengthen (S^ inΓ up) (S^ ninΓ) (◀S^ newΓ) upA
  with ninA ← εᵍ-⦂-¬ε ninΓ inΓ
  with ⟨ pA , uppA ⟩ ← ↑ty-surjective ninA
  = S^ (∋⦂-strengthen inΓ ninΓ newΓ uppA) (↑ty-comm1 upA up uppA)
∋⦂-strengthen (S= inΓ up) (Z= upA₁ ¬inA) ◀Z= upA
  with refl ← ↑ty-unique-inver upA up = inΓ
∋⦂-strengthen (S= inΓ up) (S= ninΓ upA₁ ¬inA) (◀S= newΓ x) upA
  with ninA ← εᵍ-⦂-¬ε ninΓ inΓ
  with ⟨ pA , uppA ⟩ ← ↑ty-surjective ninA
  = S= (∋⦂-strengthen inΓ ninΓ newΓ uppA) (↑ty-comm1 upA up uppA)


∋:=-strengthen : Γ ∋ punchIn k X := A'
                 → k ¬εᵍ Γ
                 → Γ ◀ k ⇘ Γ'
                 → A ↑ty k ⇘ A'
                 → Γ' ∋ X := A
∋:=-strengthen {k = #0} {X = #0} (S= inΓ up) (Z= upA₁ ¬inA) ◀Z= upA
  with refl ← ↑ty-unique-inver up upA = inΓ
∋:=-strengthen {k = #0} {X = #S X} (S= inΓ up) (Z= upA₁ ¬inA) ◀Z= upA with refl ← ↑ty-unique-inver up upA = inΓ
∋:=-strengthen {k = #S k} {X = #0} (Z up) (S= ninΓ upA₁ ¬inA) (◀S= upΓ x) upA with refl ← ↑ty-unique upA₁ up = Z (↑ty-comm1 upA up x)
∋:=-strengthen {k = #S k} {X = #S X} (S∙ inΓ up) (S∙ ninΓ) (◀S∙ upΓ) upA
  with k¬inA ← εᵍ-:=-¬ε ninΓ inΓ
  with ⟨ preA , uptoA ⟩ ← ↑ty-surjective k¬inA = S∙ (∋:=-strengthen inΓ ninΓ upΓ uptoA) (↑ty-comm1 upA up uptoA)
∋:=-strengthen {k = #S k} {X = #S X} (S^ inΓ up) (S^ ninΓ) (◀S^ upΓ) upA
  with k¬inA ← εᵍ-:=-¬ε ninΓ inΓ
  with ⟨ preA , uptoA ⟩ ← ↑ty-surjective k¬inA = S^ (∋:=-strengthen inΓ ninΓ upΓ uptoA) (↑ty-comm1 upA up uptoA)
∋:=-strengthen {k = #S k} {X = #S X} (S= inΓ up) (S= ninΓ upA₁ ¬inA) (◀S= upΓ x) upA
  with k¬inA ← εᵍ-:=-¬ε ninΓ inΓ
  with ⟨ preA , uptoA ⟩ ← ↑ty-surjective k¬inA = S= (∋:=-strengthen inΓ ninΓ upΓ uptoA) (↑ty-comm1 upA up uptoA)
∋:=-strengthen {Γ = Γ , A} {k = k} {X = X} (S, inΓ) (S, x ¬inA) (◀S, new up) upA = S, (∋:=-strengthen inΓ ¬inA new upA)
∋:=-strengthen {Γ = Γ ,^} {#0} {#0} (S^ x up) Z^ ◀Z^ upA
  with refl ← ↑ty-unique-inver up upA = x
∋:=-strengthen {Γ = Γ ,∙} {#0} {#0} (S∙ x up) Z∙ ◀Z∙ upA
  with refl ← ↑ty-unique-inver up upA = x
∋:=-strengthen {Γ = Γ ,^} {#0} {#S X} (S^ x up) Z^ ◀Z^ upA
  with refl ← ↑ty-unique-inver up upA = x
∋:=-strengthen {Γ = Γ ,∙} {#0} {#S X} (S∙ x up) Z∙ ◀Z∙ upA
  with refl ← ↑ty-unique-inver up upA = x
