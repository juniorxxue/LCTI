module Implicit.Language.OpenClose.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Subst.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Occur.All
open import Implicit.Language.EnvOps.All

open import Implicit.Language.OpenClose.Base
open import Implicit.Language.OpenClose.Weaken
open import Implicit.Language.OpenClose.Strengthen


∋⦂-closed : Closed Γ
          → Γ ∋ x ⦂ A
          → Γ ⊢c A
∋⦂-closed (clo-S, cloΓ cloA) Z = ⊢c-weaken,0 cloA cloA
∋⦂-closed (clo-S, cloΓ cloA) (S, inΓ) = ⊢c-weaken,0 (∋⦂-closed cloΓ inΓ) cloA
∋⦂-closed (clo-S∙ cloΓ) (S∙ inΓ up) = ⊢c-weaken∙0 (∋⦂-closed cloΓ inΓ) up
∋⦂-closed (clo-S^ cloΓ) (S^ inΓ up) = ⊢c-weaken^0 (∋⦂-closed cloΓ inΓ) up
∋⦂-closed (clo-S= cloΓ cloA) (S= inΓ x) = ⊢c-weaken=0 (∋⦂-closed cloΓ inΓ) x cloA

∋=-closed : Closed Γ
          → Γ ∋ X := A
          → Γ ⊢c A
∋=-closed (clo-S= cloΓ cloA) (Z up) = ⊢c-weaken=0 cloA up cloA
∋=-closed (clo-S, cloΓ cloA) (S, inΓ) = ⊢c-weaken,0 (∋=-closed cloΓ inΓ) cloA
∋=-closed (clo-S∙ cloΓ) (S∙ inΓ up) = ⊢c-weaken∙0 (∋=-closed cloΓ inΓ) up
∋=-closed (clo-S^ cloΓ) (S^ inΓ up) = ⊢c-weaken^0 (∋=-closed cloΓ inΓ) up
∋=-closed (clo-S= cloΓ cloA) (S= inΓ up) = ⊢c-weaken=0 (∋=-closed cloΓ inΓ) up cloA

⊢c-◆ : Γ ⊢c A
     → Γ ◆ k ⇘ Γ'
     → Γ' ⊢c A
⊢c-◆ ⊢c-int ◆Γ = ⊢c-int
⊢c-◆ (⊢c-var-∙ inΓ) ◆Γ = ⊢c-var-∙ (◆-∙∈ inΓ ◆Γ)
⊢c-◆ {k = k} (⊢c-var-= {X = X} inΓ) ◆Γ with k #≟ X
... | yes refl = ⊢c-var-∙ (◆-=∈-≡ inΓ ◆Γ)
... | no ¬p = ⊢c-var-= (◆-=∈-≢ inΓ ◆Γ ¬p)
⊢c-◆ (⊢c-arr clo clo₁) ◆Γ = ⊢c-arr (⊢c-◆ clo ◆Γ) (⊢c-◆ clo₁ ◆Γ)
⊢c-◆ (⊢c-∀ clo) ◆Γ = ⊢c-∀ (⊢c-◆ clo (◆S∙ ◆Γ))

⊢c-◆0 : Γ ,= B ⊢c A
      → Γ ,∙ ⊢c A
⊢c-◆0 clo = ⊢c-◆ clo ◆Z

⊢c-◇ : Γ ⊢c A
     → Γ ◇ k ⇘ Γ'
     → Γ' ⊢c A
⊢c-◇ ⊢c-int newΓ = ⊢c-int
⊢c-◇ (⊢c-var-∙ inΓ) newΓ = ⊢c-var-∙ (◇-∙∈ inΓ newΓ)
⊢c-◇ (⊢c-var-= inΓ) newΓ = ⊢c-var-= (◇-=∈ inΓ newΓ)
⊢c-◇ (⊢c-arr cloA cloA₁) newΓ = ⊢c-arr (⊢c-◇ cloA newΓ) (⊢c-◇ cloA₁ newΓ)
⊢c-◇ (⊢c-∀ cloA) newΓ = ⊢c-∀ (⊢c-◇ cloA (◇S∙ newΓ))


⊢c-^∈-false : k ε A
            → Γ ∋^ k
            → Γ ⊢c A
            → ⊥
⊢c-^∈-false ε-var inΓ (⊢c-var-∙ x) = ∋^-∋∙-false inΓ x
⊢c-^∈-false ε-var inΓ (⊢c-var-= x) = ∋^-∋=-false inΓ x
⊢c-^∈-false (ε-arr-l inA) inΓ (⊢c-arr cloA cloA₁) = ⊢c-^∈-false inA inΓ cloA
⊢c-^∈-false (ε-arr-r inA) inΓ (⊢c-arr cloA cloA₁) = ⊢c-^∈-false inA inΓ cloA₁
⊢c-^∈-false (ε-∀ inA) inΓ (⊢c-∀ cloA) = ⊢c-^∈-false inA (S∙ inΓ) cloA

⊢c-^∈-¬ε : Γ ⊢c A
         → Γ ∋^ k
         → k ¬ε A
⊢c-^∈-¬ε ⊢c-int inΓ = ¬ε-int
⊢c-^∈-¬ε (⊢c-var-∙ inΓ₁) inΓ = ¬ε-var (∋∙-∋^-≢ inΓ₁ inΓ)
⊢c-^∈-¬ε (⊢c-var-= inΓ₁) inΓ = ¬ε-var (∋=-∋^-≢ inΓ₁ inΓ)
⊢c-^∈-¬ε (⊢c-arr cloA cloA₁) inΓ = ¬ε-arr (⊢c-^∈-¬ε cloA inΓ) (⊢c-^∈-¬ε cloA₁ inΓ)
⊢c-^∈-¬ε (⊢c-∀ cloA) inΓ = ¬ε-∀ (⊢c-^∈-¬ε cloA (S∙ inΓ))

⊢c-⊢o-disjoint : Ψ ⊢c A
               → Ψ ⊢o A
               → ⊥
⊢c-⊢o-disjoint (⊢c-var-∙ inΓ) (⊢o-var-^ x) = ∋^-∋∙-false x inΓ
⊢c-⊢o-disjoint (⊢c-var-= inΓ) (⊢o-var-^ x) = ∋^-∋=-false x inΓ
⊢c-⊢o-disjoint (⊢c-arr clo clo₁) (⊢o-arr-l opn) = ⊢c-⊢o-disjoint clo opn
⊢c-⊢o-disjoint (⊢c-arr clo clo₁) (⊢o-arr-r opn) = ⊢c-⊢o-disjoint clo₁ opn
⊢c-⊢o-disjoint (⊢c-∀ clo) (⊢o-∀ opn) = ⊢c-⊢o-disjoint clo opn
