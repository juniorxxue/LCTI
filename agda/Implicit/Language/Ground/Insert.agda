module Implicit.Language.Ground.Insert where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.OpenClose.All
open import Implicit.Language.Norm.All
open import Implicit.Language.EnvOps.All
open import Implicit.Language.Ground.Base
open import Implicit.Language.Ground.Properties

-- different to original insertion, when insert a type, we apply the environment to the operand
infix 3 _▶%_,=_⇘_
data _▶%_,=_⇘_ : Env n m → Fin (1 + m) → Type m → Env n (1 + m) → Set where
  ▶%Z  : Γ ≫ A ⇘ A%
       → Γ ▶% #0 ,= A ⇘ Γ ,= A%
  ▶%S, : Γ ▶% k ,= A ⇘ Γ'
       → (up : B ↑ty k ⇘ B')
       → Γ , B ▶% k ,= A ⇘ Γ' , B'
  ▶%S^ : Γ ▶% k ,= A ⇘ Γ'
       → ↑ty0 A ⇘ A'
       → Γ ,^ ▶% #S k ,= A' ⇘ Γ' ,^
  ▶%S∙ : Γ ▶% k ,= A ⇘ Γ'
       → ↑ty0 A ⇘ A'
       → Γ ,∙ ▶% #S k ,= A' ⇘ Γ' ,∙
  ▶%S= : Γ ▶% k ,= A ⇘ Γ'
       → ↑ty0 A ⇘ A'
       → B ↑ty k ⇘ B'
       → Γ ,= B ▶% #S k ,= A' ⇘ Γ' ,= B'

▶%-punchOut-∋= : ∀ {m} {Γ : Env n m} {k X B Γ'}
       → (¬p : k ≢ X)
       → Γ ∋= punchOut ¬p
       → Γ ▶% k ,= B ⇘ Γ'
       → Γ' ∋= X
▶%-punchOut-∋= {m = m} {k = #0} {X = #0} ¬p inΓ (▶%Z x) = Z
▶%-punchOut-∋= {m = m} {k = k} {X = #S X} ¬p inΓ (▶%Z x) = S= inΓ
▶%-punchOut-∋= {m = m} {k = k} {X = X} ¬p (S, inΓ) (▶%S, newΓ up) = S, (▶%-punchOut-∋= ¬p inΓ newΓ)
▶%-punchOut-∋= {m = suc m} {k = #S k} {X = #S X} ¬p (S^ inΓ) (▶%S^ newΓ x) = S^ (▶%-punchOut-∋= (≢-pred ¬p) inΓ newΓ)
▶%-punchOut-∋= {m = suc m} {k = #S k} {X = #S X} ¬p (S∙ inΓ) (▶%S∙ newΓ x) = S∙ (▶%-punchOut-∋= (≢-pred ¬p) inΓ newΓ)
▶%-punchOut-∋= {m = m} {k = #S k} {X = #0} ¬p Z (▶%S= newΓ x x₁) = Z
▶%-punchOut-∋= {m = m} {k = #S k} {X = #S X} ¬p (S= inΓ) (▶%S= newΓ x x₁) = S= (▶%-punchOut-∋= (≢-pred ¬p) inΓ newΓ)

▶%-punchOut-∋:= : ∀ {m} {Γ : Env n m} {A A' k X B Γ'}
       → (¬p : k ≢ X)
       → Γ ∋ punchOut ¬p := A
       → Γ ▶% k ,= B ⇘ Γ'
       → Γ' ∋ X := A'
       → A ↑ty k ⇘ A'
▶%-punchOut-∋:= {m = m} {k = #0} {#0} ¬p inΓ (▶%Z x) (Z up) = ⊥-elim (¬p refl)
▶%-punchOut-∋:= {m = m} {k = #0} {#S X} ¬p inΓ (▶%Z x) (S= inΓ' up) with ∋:=-unique inΓ inΓ'
... | refl = up
▶%-punchOut-∋:= {m = m} {k = k} {X} ¬p (S, inΓ) (▶%S, newΓ' up) (S, inΓ') = ▶%-punchOut-∋:= ¬p inΓ newΓ' inΓ'
▶%-punchOut-∋:= {m = suc m} {k = #S k} {#S X} ¬p (S^ inΓ up) (▶%S^ newΓ' x) (S^ inΓ' up₁) with ▶%-punchOut-∋:= (≢-pred ¬p) inΓ newΓ' inΓ'
... | r = ↑ty-comm' z≤n r up₁ up
▶%-punchOut-∋:= {m = suc m} {k = #S k} {#S X} ¬p (S∙ inΓ up) (▶%S∙ newΓ' x) (S∙ inΓ' up₁) with ▶%-punchOut-∋:= (≢-pred ¬p) inΓ newΓ' inΓ'
... | r = ↑ty-comm' z≤n r up₁ up
▶%-punchOut-∋:= {m = suc m} {k = #S k} {#0} ¬p (Z up) (▶%S= newΓ' x x₁) (Z up₁) = ↑ty-comm' z≤n x₁ up₁ up
▶%-punchOut-∋:= {m = suc m} {k = #S k} {#S X} ¬p (S= inΓ up) (▶%S= newΓ' x x₁) (S= inΓ' up₁) with ▶%-punchOut-∋:= (≢-pred ¬p) inΓ newΓ' inΓ'
... | r = ↑ty-comm' z≤n r up₁ up

▶%-punchOut-∋∙ : ∀ {m} {Γ : Env n m} {k X B Γ'}
       → (¬p : k ≢ X)
       → Γ ∋∙ punchOut ¬p
       → Γ ▶% k ,= B ⇘ Γ'
       → Γ' ∋∙ X
▶%-punchOut-∋∙ {m = m} {k = #0} {X = #0} ¬p inΓ (▶%Z x) = ⊥-elim (¬p refl)
▶%-punchOut-∋∙ {m = m} {k = k} {X = #S X} ¬p inΓ (▶%Z x) = S= inΓ
▶%-punchOut-∋∙ {m = m} {k = k} {X = X} ¬p (S, inΓ) (▶%S, newΓ up) = S, (▶%-punchOut-∋∙ ¬p inΓ newΓ)
▶%-punchOut-∋∙ {m = suc m} {k = #S k} {X = #S X} ¬p (S^ inΓ) (▶%S^ newΓ x) = S^ (▶%-punchOut-∋∙ (≢-pred ¬p) inΓ newΓ)
▶%-punchOut-∋∙ {m = suc m} {k = #S k} {X = #S X} ¬p (S∙ inΓ) (▶%S∙ newΓ x) = S∙ (▶%-punchOut-∋∙ (≢-pred ¬p) inΓ newΓ)
▶%-punchOut-∋∙ {m = m} {k = #S k} {X = #0} ¬p Z (▶%S∙ newΓ x) = Z
▶%-punchOut-∋∙ {m = m} {k = #S k} {X = #S X} ¬p (S= inΓ) (▶%S= newΓ x x₁) = S= (▶%-punchOut-∋∙ (≢-pred ¬p) inΓ newΓ)

▶%-∋= : Γ ▶% k ,= B ⇘ Γ'
      → Γ' ∋= k
▶%-∋= (▶%Z x) = Z
▶%-∋= (▶%S, newΓ up) = S, (▶%-∋= newΓ)
▶%-∋= (▶%S^ newΓ x) = S^ (▶%-∋= newΓ)
▶%-∋= (▶%S∙ newΓ x) = S∙ (▶%-∋= newΓ)
▶%-∋= (▶%S= newΓ x x₁) = S= (▶%-∋= newΓ)



▶%-∋:-grd-↑ty-rev-^ : Γ ,^ ≫ A' ⇘ A%'
                 → ↑ty0 A ⇘ A'
                 → ∃[ A% ](↑ty0 A% ⇘ A%')
▶%-∋:-grd-↑ty-rev-^ apA' upA with shifted-↑ty {k = #0} (grd-↑ty apA' Z^ (↑ty-shifted upA))
... | ⟨ A% , upA% ⟩ = ⟨ A% , upA% ⟩

▶%-∋:-grd-↑ty-rev-∙ : Γ ,∙ ≫ A' ⇘ A%'
                 → ↑ty0 A ⇘ A'
                 → ∃[ A% ](↑ty0 A% ⇘ A%')
▶%-∋:-grd-↑ty-rev-∙ apA' upA with shifted-↑ty {k = #0} (grd-↑ty apA' Z∙ (↑ty-shifted upA))
... | ⟨ A% , upA% ⟩ = ⟨ A% , upA% ⟩

▶%-∋:-grd-↑ty-rev-= : Γ ,= T ≫ A' ⇘ A%'
                 → ↑ty0 A ⇘ A'
                 → ∃[ A% ](↑ty0 A% ⇘ A%')
▶%-∋:-grd-↑ty-rev-= {T = T} apA' upA = let ⟨ T' , upT ⟩ = ↑ty0-total T in shifted-↑ty (grd-↑ty apA' (Z= upT (ε-shifted-false (↑ty-shifted upT))) (↑ty-shifted upA))

▶%-∋:=-ap : Γ ▶% k ,= A ⇘ Γ'
          → Γ' ∋ k := A%'
          → Γ ≫ A ⇘ A%
          → A% ↑ty k ⇘ A%'
▶%-∋:=-ap (▶%Z x) (Z up) apA with grd-unique x apA
... | refl = up
▶%-∋:=-ap (▶%S, newΓ up) (S, inΓ) apA = ▶%-∋:=-ap newΓ inΓ (grd-strengthen,0 apA)
▶%-∋:=-ap (▶%S^ newΓ x) (S^ inΓ up) apA
  with ⟨ A , upA ⟩ ← ▶%-∋:-grd-↑ty-rev-^ apA x
  with ▶%-∋:=-ap newΓ inΓ (grd-strengthen^0 apA x upA)
... | ih = ↑ty-comm' z≤n ih up upA
▶%-∋:=-ap (▶%S∙ newΓ x) (S∙ inΓ up) apA
  with ⟨ A , upA ⟩ ← ▶%-∋:-grd-↑ty-rev-∙ apA x
  with ▶%-∋:=-ap newΓ inΓ (grd-strengthen∙0 apA x upA)
... | ih = ↑ty-comm' z≤n ih up upA
▶%-∋:=-ap (▶%S= newΓ x x₁) (S= inΓ up) apA
  with ⟨ A , upA ⟩ ← ▶%-∋:-grd-↑ty-rev-= apA x
  with ▶%-∋:=-ap newΓ inΓ (grd-strengthen=0 apA x upA)
... | ih = ↑ty-comm' z≤n ih up upA
