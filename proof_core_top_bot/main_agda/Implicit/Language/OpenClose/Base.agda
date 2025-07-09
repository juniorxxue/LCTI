module Implicit.Language.OpenClose.Base where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.Base
open import Implicit.Language.Shift.Base

infix 3 _⊢o_
-- open: have free existential variables
data _⊢o_ : Env n m → Type m → Set where
  ⊢o-var-^ :
      Δ ∋^ X
    → Δ ⊢o ‶ X
  ⊢o-arr-l :
      Δ ⊢o A
    → Δ ⊢o (A `→ B)
  ⊢o-arr-r :
      Δ ⊢o B
    → Δ ⊢o (A `→ B)
  ⊢o-∀ :
      Δ ,∙ ⊢o A
    → Δ ⊢o `∀ A

⊢r-⊢o-false : Γ ⊢r A
            → Γ ⊢o A
            → ⊥
⊢r-⊢o-false (⊢r-var-∙ inΓ) (⊢o-var-^ x) = ∋^-∋∙-false x inΓ
⊢r-⊢o-false (⊢r-arr regA regA₁) (⊢o-arr-l opnA) = ⊢r-⊢o-false regA opnA
⊢r-⊢o-false (⊢r-arr regA regA₁) (⊢o-arr-r opnA) = ⊢r-⊢o-false regA₁ opnA
⊢r-⊢o-false (⊢r-∀ regA) (⊢o-∀ opnA) = ⊢r-⊢o-false regA opnA


infix 3 _⊢c_
data _⊢c_ : Env n m → Type m → Set where
  ⊢c-int :
      Δ ⊢c Int
  ⊢c-top :
      Δ ⊢c Top
  ⊢c-bot :
      Δ ⊢c Bot
  ⊢c-var-∙ :
      (inΔ : Δ ∋∙ X)
    → Δ ⊢c ‶ X
  ⊢c-var-= :
      (inΔ : Δ ∋= X)
    → Δ ⊢c ‶ X
  ⊢c-arr :
      Δ ⊢c A
    → Δ ⊢c B
    → Δ ⊢c (A `→ B)
  ⊢c-∀ :
      Δ ,∙ ⊢c A
    → Δ ⊢c `∀ A

⊢c-^∈-¬ε : Γ ⊢c A
         → Γ ∋^ k
         → k ¬ε A
⊢c-^∈-¬ε ⊢c-int inΓ = ¬ε-int
⊢c-^∈-¬ε (⊢c-var-∙ inΓ₁) inΓ = ¬ε-var (∋∙-∋^-≢ inΓ₁ inΓ)
⊢c-^∈-¬ε (⊢c-var-= inΓ₁) inΓ = ¬ε-var (∋=-∋^-≢ inΓ₁ inΓ)
⊢c-^∈-¬ε (⊢c-arr cloA cloA₁) inΓ = ¬ε-arr (⊢c-^∈-¬ε cloA inΓ) (⊢c-^∈-¬ε cloA₁ inΓ)
⊢c-^∈-¬ε (⊢c-∀ cloA) inΓ = ¬ε-∀ (⊢c-^∈-¬ε cloA (S∙ inΓ))
⊢c-^∈-¬ε ⊢c-top x = ¬ε-top
⊢c-^∈-¬ε ⊢c-bot x = ¬ε-bot
