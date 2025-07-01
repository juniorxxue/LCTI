module Implicit.Language.Occur.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Occur.Base
open import Implicit.Language.OpenClose.Base

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
↑ty-ε-≤ (ε-arr-r ninA inA') (↑ty-arr upA upA₁) lt = ε-arr-r (¬ε-↑ty-≤ ninA upA lt) (↑ty-ε-≤ inA' upA₁ lt)
↑ty-ε-≤ (ε-∀ inA') (↑ty-∀ upA) lt = ε-∀ (↑ty-ε-≤ inA' upA (s≤s lt))


↑ty-ε : X ε A
      → A ↑ty k ⇘ A'
      → X #< k
      → inject₁ X ε A'
↑ty-ε ε-var ↑ty-var lt rewrite punchIn-inject lt = ε-var
↑ty-ε (ε-arr-l inA) (↑ty-arr up up₁) lt = ε-arr-l (↑ty-ε inA up lt)
↑ty-ε (ε-arr-r ninA inA) (↑ty-arr up up₁) lt = ε-arr-r (¬ε-↑ty' ninA up lt) (↑ty-ε inA up₁ lt)
↑ty-ε (ε-∀ inA) (↑ty-∀ up) lt = ε-∀ (↑ty-ε inA up (s≤s lt))

↑ty-ε' : inject₁ X ε A'
       → X #< k
       → A ↑ty k ⇘ A'
       → X ε A
↑ty-ε' ε-var lt upA rewrite punchIn-inject lt with ↑ty-var-inv-helper upA refl
... | refl = ε-var
↑ty-ε' (ε-arr-l inA) lt (↑ty-arr upA upA₁) = ε-arr-l (↑ty-ε' inA lt upA)
↑ty-ε' (ε-arr-r ¬inA inA) lt (↑ty-arr upA upA₁) = ε-arr-r (¬ε-↑ty'-inv ¬inA upA lt) (↑ty-ε' inA lt upA₁)
↑ty-ε' (ε-∀ inA) lt (↑ty-∀ upA) = ε-∀ (↑ty-ε' inA (s≤s lt) upA)


ε-¬ε-false : k ε A
           → k ¬ε A
           → ⊥
ε-¬ε-false ε-var (¬ε-var x) = x refl
ε-¬ε-false (ε-arr-l inA) (¬ε-arr ¬inA ¬inA₁) = ε-¬ε-false inA ¬inA
ε-¬ε-false (ε-arr-r ninA inA) (¬ε-arr ¬inA ¬inA₁) = ε-¬ε-false inA ¬inA₁
ε-¬ε-false (ε-∀ inA) (¬ε-∀ ¬inA) = ε-¬ε-false inA ¬inA



ε-dec : (k ε A) ⊎ (k ¬ε A)
ε-dec {k = k} {A = Int} = inj₂ ¬ε-int
ε-dec {k = k} {A = ‶ X} with k #≟ X
... | yes refl = inj₁ ε-var
... | no ¬p = inj₂ (¬ε-var (≢-sym ¬p))
ε-dec {k = k} {A = A `→ B} with ε-dec {k = k} {A = A} | ε-dec {k = k} {A = B}
... | inj₁ p | _ = inj₁ (ε-arr-l p)
... | inj₂ p | inj₁ p' = inj₁ (ε-arr-r p p')
... | inj₂ p | inj₂ p' = inj₂ (¬ε-arr p p')
ε-dec {k = k} {A = `∀ A} with ε-dec {k = #S k} {A = A}
... | inj₁ p = inj₁ (ε-∀ p)
... | inj₂ p = inj₂ (¬ε-∀ p)


ε-↑ty : k₁ ε A
      → A ↑ty k₂ ⇘ A'
      → k₂ #≤ k₁
      → #S k₁ ε A'
ε-↑ty ε-var ↑ty-var sm rewrite punchIn-≤ sm = ε-var
ε-↑ty (ε-arr-l kε) (↑ty-arr ↑ty ↑ty₁) sm = ε-arr-l (ε-↑ty kε ↑ty sm)
ε-↑ty (ε-arr-r ninA kε) (↑ty-arr ↑ty ↑ty₁) sm = ε-arr-r (¬ε-↑ty ninA ↑ty sm) (ε-↑ty kε ↑ty₁ sm)
ε-↑ty (ε-∀ kε) (↑ty-∀ ↑ty) sm = ε-∀ (ε-↑ty kε ↑ty (s≤s sm))

ε-↑ty0 : k ε A
       → ↑ty0 A ⇘ A'
       → #S k ε A'
ε-↑ty0 inA ↑ty = ε-↑ty inA ↑ty z≤n

----------------------------------------------------------------------
--+                        not occur in env                        +--
----------------------------------------------------------------------

εᵍ-:=-¬ε : k ¬εᵍ Γ
         → Γ ∋ X := A
         → k ¬ε A
εᵍ-:=-¬ε Z^ (S^ inΓ up) = ↑ty-¬ε up
εᵍ-:=-¬ε Z∙ (S∙ inΓ up) = ↑ty-¬ε up
εᵍ-:=-¬ε (Z= x x₁) (Z up) = ↑ty-¬ε up
εᵍ-:=-¬ε (Z= x x₁) (S= inΓ up) = ↑ty-¬ε up
εᵍ-:=-¬ε (S∙ ninΓ) (S∙ inΓ up) = ¬ε-↑ty0 (εᵍ-:=-¬ε ninΓ inΓ) up
εᵍ-:=-¬ε (S^ ninΓ) (S^ inΓ up) = ¬ε-↑ty0 (εᵍ-:=-¬ε ninΓ inΓ) up
εᵍ-:=-¬ε (S= ninΓ x x₁) (Z up) with ↑ty-unique up x
... | refl = ¬ε-↑ty0 x₁ x
εᵍ-:=-¬ε (S= ninΓ x x₁) (S= inΓ up) = ¬ε-↑ty0 (εᵍ-:=-¬ε ninΓ inΓ) up
εᵍ-:=-¬ε (S, x ninΓ) (S, inΓ) = εᵍ-:=-¬ε ninΓ inΓ


εᵍ-:=-false : Γ ∋ X := A
            → k ε A
            → k ¬εᵍ Γ
            → ⊥
εᵍ-:=-false inΓ inA ¬inΓ = ε-¬ε-false inA (εᵍ-:=-¬ε ¬inΓ inΓ)


⊢c-^∈-false : k ε A
            → Γ ∋^ k
            → Γ ⊢c A
            → ⊥
⊢c-^∈-false ε-var inΓ (⊢c-var-∙ x) = ∋^-∋∙-false inΓ x
⊢c-^∈-false ε-var inΓ (⊢c-var-= x) = ∋^-∋=-false inΓ x
⊢c-^∈-false (ε-arr-l inA) inΓ (⊢c-arr cloA cloA₁) = ⊢c-^∈-false inA inΓ cloA
⊢c-^∈-false (ε-arr-r ¬inA inA) inΓ (⊢c-arr cloA cloA₁) = ⊢c-^∈-false inA inΓ cloA₁
⊢c-^∈-false (ε-∀ inA) inΓ (⊢c-∀ cloA) = ⊢c-^∈-false inA (S∙ inΓ) cloA
