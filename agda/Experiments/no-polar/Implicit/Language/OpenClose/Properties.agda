module Implicit.Language.OpenClose.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Lookup
open import Implicit.Language.Shift
open import Implicit.Language.Subst
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

----------------------------------------------------------------------
--+                          replacement                           +--
----------------------------------------------------------------------


⊢c-^∈-false : k ε A
            → Γ ∋^ k
            → Γ ⊢c A
            → ⊥
⊢c-^∈-false ε-var inΓ (⊢c-var-∙ x) = ^∈-∙∈-false inΓ x
⊢c-^∈-false ε-var inΓ (⊢c-var-= x) = ^∈-=∈-false inΓ x
⊢c-^∈-false (ε-arr-l inA) inΓ (⊢c-arr cloA cloA₁) = ⊢c-^∈-false inA inΓ cloA
⊢c-^∈-false (ε-arr-r inA) inΓ (⊢c-arr cloA cloA₁) = ⊢c-^∈-false inA inΓ cloA₁
⊢c-^∈-false (ε-∀ inA) inΓ (⊢c-∀ cloA) = ⊢c-^∈-false inA (S∙ inΓ) cloA


⊢c-⊢o-disjoint : Ψ ⊢c A
               → Ψ ⊢o A
               → ⊥
⊢c-⊢o-disjoint (⊢c-var-∙ inΓ) (⊢o-var-^ x) = ^∈-∙∈-false x inΓ
⊢c-⊢o-disjoint (⊢c-var-= inΓ) (⊢o-var-^ x) = ^∈-=∈-false x inΓ
⊢c-⊢o-disjoint (⊢c-arr clo clo₁) (⊢o-arr-l opn) = ⊢c-⊢o-disjoint clo opn
⊢c-⊢o-disjoint (⊢c-arr clo clo₁) (⊢o-arr-r opn) = ⊢c-⊢o-disjoint clo₁ opn
⊢c-⊢o-disjoint (⊢c-∀ clo) (⊢o-∀ opn) = ⊢c-⊢o-disjoint clo opn
