module Implicit.Language.Occur.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Occur.Base

↑ty-ε-≤ : #S X ε A'
        → A ↑ty k ⇘ A'
        → k #≤ X
        → X ε A
↑ty-ε-≤ {X = X} {k = k} ε-var upA lt rewrite sym (punchIn-≤ lt) = helper lt refl upA
  where helper' : ∀ {X k Y}
                → ‶ (punchIn k X) ≡ ‶ (punchIn k Y)
                → X ≡ Y
        helper' {X = X} {k = k} {Y = Y} eq = punchIn-injective k X Y (‶-injective eq)
        helper : ∀ {varY}
               → k #≤ X
               → varY ≡ ‶ punchIn k X
               → A ↑ty k ⇘ varY
               → X ε A
        helper lt eq ↑ty-var rewrite helper' eq = ε-var
↑ty-ε-≤ (ε-arr-l inA') (↑ty-arr upA upA₁) lt = ε-arr-l (↑ty-ε-≤ inA' upA lt)
↑ty-ε-≤ (ε-arr-r inA') (↑ty-arr upA upA₁) lt = ε-arr-r (↑ty-ε-≤ inA' upA₁ lt)
↑ty-ε-≤ (ε-∀ inA') (↑ty-∀ upA) lt = ε-∀ (↑ty-ε-≤ inA' upA (s≤s lt))


↑ty-ε : X ε A
      → A ↑ty k ⇘ A'
      → X #< k
      → inject₁ X ε A'
↑ty-ε ε-var ↑ty-var lt rewrite punchIn-inject lt = ε-var
↑ty-ε (ε-arr-l inA) (↑ty-arr up up₁) lt = ε-arr-l (↑ty-ε inA up lt)
↑ty-ε (ε-arr-r inA) (↑ty-arr up up₁) lt = ε-arr-r (↑ty-ε inA up₁ lt)
↑ty-ε (ε-∀ inA) (↑ty-∀ up) lt = ε-∀ (↑ty-ε inA up (s≤s lt))


↑ty-¬ε : X ¬ε A
      → A ↑ty k ⇘ A'
      → X #< k
      → inject₁ X ¬ε A'
↑ty-¬ε ¬ε-int ↑ty-int lt = ¬ε-int
↑ty-¬ε (¬ε-var x) ↑ty-var lt = ¬ε-var (punchIn-inject-neq lt x)
↑ty-¬ε (¬ε-arr ninA ninA₁) (↑ty-arr up up₁) lt = ¬ε-arr (↑ty-¬ε ninA up lt) (↑ty-¬ε ninA₁ up₁ lt)
↑ty-¬ε (¬ε-∀ ninA) (↑ty-∀ up) lt = ¬ε-∀ (↑ty-¬ε ninA up (s≤s lt))

ε-shifted-false : Shifted A k
                → k ε A
                → ⊥
ε-shifted-false (sfd-var x) ε-var = x refl
ε-shifted-false (sfd-arr sd sd₁) (ε-arr-l inT) = ε-shifted-false sd inT
ε-shifted-false (sfd-arr sd sd₁) (ε-arr-r inT) = ε-shifted-false sd₁ inT
ε-shifted-false (sfd-∀ sd) (ε-∀ inT) = ε-shifted-false sd inT

↑ty-ε-false : A ↑ty k ⇘ A'
            → k ε A'
            → ⊥
↑ty-ε-false upA inA = ε-shifted-false (↑ty-shifted upA) inA

ε-var-neg : ¬ (k ε ‶ X)
          → X ≢ k
ε-var-neg noin refl = noin ε-var

εᵍ-false : Γ ∋ X := A
         → k ε A
         → k ¬εᵍ Γ
         → ⊥
εᵍ-false (Z up) inA (Z= x x₁) with ↑ty-unique up x
... | refl = x₁ inA
εᵍ-false (Z up) inA (S= ninΓ x x₁) with ↑ty-unique up x
... | refl = x₁ inA
εᵍ-false (S, inΓ) inA (S, x ninΓ) = εᵍ-false inΓ inA ninΓ
εᵍ-false (S∙ inΓ up) inA Z∙ = ↑ty-ε-false up inA
εᵍ-false (S∙ inΓ up) inA (S∙ ninΓ) = εᵍ-false inΓ (↑ty-ε-≤ inA up z≤n) ninΓ
εᵍ-false (S^ inΓ up) inA Z^ = ↑ty-ε-false up inA
εᵍ-false (S^ inΓ up) inA (S^ ninΓ) = εᵍ-false inΓ (↑ty-ε-≤ inA up z≤n) ninΓ
εᵍ-false (S= inΓ up) inA (Z= x x₁) = ↑ty-ε-false up inA
εᵍ-false (S= inΓ up) inA (S= ninΓ x x₁) = εᵍ-false inΓ (↑ty-ε-≤ inA up z≤n) ninΓ

¬ε-shifted : ¬ (k ε A)
           → Shifted A k
¬ε-shifted {A = Int} nin = sfd-int
¬ε-shifted {A = ‶ X} nin = sfd-var (helper nin)
  where helper : ¬ (k ε ‶ X)
               →  X ≢ k
        helper nin refl = nin ε-var
¬ε-shifted {A = A `→ A₁} nin = sfd-arr (¬ε-shifted (λ z → nin (ε-arr-l z)))
                                       (¬ε-shifted (λ z → nin (ε-arr-r z)))
¬ε-shifted {A = `∀ A} nin = sfd-∀ (¬ε-shifted (λ z → nin (ε-∀ z)))

εᵍ-shifted : k ¬εᵍ Γ
           → Γ ∋ X := A
           → Shifted A k
εᵍ-shifted ninΓ inΓ = ¬ε-shifted (λ x → εᵍ-false inΓ x ninΓ)
