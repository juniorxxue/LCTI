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

ε-¬ε-false : k ε A
           → k ¬ε A
           → ⊥
ε-¬ε-false ε-var (¬ε-var x) = x refl
ε-¬ε-false (ε-arr-l inA) (¬ε-arr ¬inA ¬inA₁) = ε-¬ε-false inA ¬inA
ε-¬ε-false (ε-arr-r inA) (¬ε-arr ¬inA ¬inA₁) = ε-¬ε-false inA ¬inA₁
ε-¬ε-false (ε-∀ inA) (¬ε-∀ ¬inA) = ε-¬ε-false inA ¬inA

εᵍ-:=-¬ε : k ¬εᵍ Γ
         → Γ ∋ X := A
         → k ¬ε A
εᵍ-:=-¬ε Z^ (S^ inΓ up) = ↑ty-¬ε up
εᵍ-:=-¬ε Z∙ (S∙ inΓ up) = ↑ty-¬ε up
εᵍ-:=-¬ε (Z= x x₁) (Z up) = ↑ty-¬ε up
εᵍ-:=-¬ε (Z= x x₁) (S= inΓ up) = ↑ty-¬ε up
εᵍ-:=-¬ε (S, x ninΓ) (S, inΓ) = εᵍ-:=-¬ε ninΓ inΓ
εᵍ-:=-¬ε (S∙ ninΓ) (S∙ inΓ up) = ¬ε-↑ty0 (εᵍ-:=-¬ε ninΓ inΓ) up
εᵍ-:=-¬ε (S^ ninΓ) (S^ inΓ up) = ¬ε-↑ty0 (εᵍ-:=-¬ε ninΓ inΓ) up
εᵍ-:=-¬ε (S= ninΓ x x₁) (Z up) with ↑ty-unique up x
... | refl = x₁
εᵍ-:=-¬ε (S= ninΓ x x₁) (S= inΓ up) = ¬ε-↑ty0 (εᵍ-:=-¬ε ninΓ inΓ) up


εᵍ-:=-false : Γ ∋ X := A
            → k ε A
            → k ¬εᵍ Γ
            → ⊥
εᵍ-:=-false inΓ inA ¬inΓ = ε-¬ε-false inA (εᵍ-:=-¬ε ¬inΓ inΓ)


ε-dec : (k ε A) ⊎ (k ¬ε A)
ε-dec {k = k} {A = Int} = inj₂ ¬ε-int
ε-dec {k = k} {A = ‶ X} with k #≟ X
... | yes refl = inj₁ ε-var
... | no ¬p = inj₂ (¬ε-var (≢-sym ¬p))
ε-dec {k = k} {A = A `→ B} with ε-dec {k = k} {A = A} | ε-dec {k = k} {A = B}
... | inj₁ p | _ = inj₁ (ε-arr-l p)
... | _ | inj₁ p = inj₁ (ε-arr-r p)
... | inj₂ p | inj₂ p' = inj₂ (¬ε-arr p p')
ε-dec {k = k} {A = `∀ A} with ε-dec {k = #S k} {A = A}
... | inj₁ p = inj₁ (ε-∀ p)
... | inj₂ p = inj₂ (¬ε-∀ p)
