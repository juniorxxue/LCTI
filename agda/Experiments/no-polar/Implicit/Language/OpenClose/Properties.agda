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
∋⦂-closed (clo-S, cloΓ cloA) Z = ⊢c-weaken,0 cloA
∋⦂-closed (clo-S, cloΓ cloA) (S, inΓ) = ⊢c-weaken,0 (∋⦂-closed cloΓ inΓ)
∋⦂-closed (clo-S∙ cloΓ) (S∙ inΓ up) = ⊢c-weaken∙0 (∋⦂-closed cloΓ inΓ) up
∋⦂-closed (clo-S^ cloΓ) (S^ inΓ up) = ⊢c-weaken^0 (∋⦂-closed cloΓ inΓ) up
∋⦂-closed (clo-S= cloΓ cloA) (S= inΓ x) = ⊢c-weaken=0 (∋⦂-closed cloΓ inΓ) x

∋=-closed : Closed Γ
          → Γ ∋ X := A
          → Γ ⊢c A
∋=-closed (clo-S= cloΓ cloA) (Z up) = ⊢c-weaken=0 cloA up
∋=-closed (clo-S, cloΓ cloA) (S, inΓ) = ⊢c-weaken,0 (∋=-closed cloΓ inΓ)
∋=-closed (clo-S∙ cloΓ) (S∙ inΓ up) = ⊢c-weaken∙0 (∋=-closed cloΓ inΓ) up
∋=-closed (clo-S^ cloΓ) (S^ inΓ up) = ⊢c-weaken^0 (∋=-closed cloΓ inΓ) up
∋=-closed (clo-S= cloΓ cloA) (S= inΓ up) = ⊢c-weaken=0 (∋=-closed cloΓ inΓ) up

----------------------------------------------------------------------
--+                          replacement                           +--
----------------------------------------------------------------------

-- in k position, we replace a ,= B with ,∙
infix 3 _◆_⇘_
data _◆_⇘_ : Env n m → Fin m → Env n m → Set where
  ◆Z : Γ ,= A ◆ #0 ⇘ Γ ,∙
  ◆S, : Γ ◆ k ⇘ Γ'
      → Γ , A ◆ k ⇘ Γ' , A
  ◆S∙ : Γ ◆ k ⇘ Γ'
      → Γ ,∙ ◆ #S k ⇘ Γ' ,∙
  ◆S= : Γ ◆ k ⇘ Γ'
      → Γ ,= A ◆ #S k ⇘ Γ' ,= A
  ◆S^ : Γ ◆ k ⇘ Γ'
      → Γ ,^ ◆ #S k ⇘ Γ' ,^

◆-∙∈ : Γ ∋∙ X
     → Γ ◆ k ⇘ Γ'
     → Γ' ∋∙ X
◆-∙∈ (S= inΓ) ◆Z = S∙ inΓ
◆-∙∈ (S, inΓ) (◆S, ◆Γ) = S, (◆-∙∈ inΓ ◆Γ)
◆-∙∈ Z (◆S∙ ◆Γ) = Z
◆-∙∈ (S∙ inΓ) (◆S∙ ◆Γ) = S∙ (◆-∙∈ inΓ ◆Γ)
◆-∙∈ (S= inΓ) (◆S= ◆Γ) = S= (◆-∙∈ inΓ ◆Γ)
◆-∙∈ (S^ inΓ) (◆S^ ◆Γ) = S^ (◆-∙∈ inΓ ◆Γ)

-- should this A exposed to the outside?
◆-=∈-≢ : Γ ∋= X
     → Γ ◆ k ⇘ Γ'
     → k ≢ X
     → Γ' ∋= X
◆-=∈-≢ Z ◆Z neq = ⊥-elim (neq refl)
◆-=∈-≢ Z (◆S= ◆Γ) neq = Z
◆-=∈-≢ (S, inΓ) (◆S, ◆Γ) neq = S, (◆-=∈-≢ inΓ ◆Γ neq)
◆-=∈-≢ (S^ inΓ) (◆S^ ◆Γ) neq = S^ (◆-=∈-≢ inΓ ◆Γ (≢-pred neq))
◆-=∈-≢ (S∙ inΓ) (◆S∙ ◆Γ) neq = S∙ (◆-=∈-≢ inΓ ◆Γ (≢-pred neq))
◆-=∈-≢ (S= inΓ) ◆Z neq = S∙ inΓ
◆-=∈-≢ (S= inΓ) (◆S= ◆Γ) neq = S= (◆-=∈-≢ inΓ ◆Γ (≢-pred neq))

◆-=∈-≡ : Γ ∋= k
     → Γ ◆ k ⇘ Γ'
     → Γ' ∋∙ k
◆-=∈-≡ Z ◆Z = Z
◆-=∈-≡ (S, inΓ) (◆S, ◆Γ) = S, (◆-=∈-≡ inΓ ◆Γ)
◆-=∈-≡ (S^ inΓ) (◆S^ ◆Γ) = S^ (◆-=∈-≡ inΓ ◆Γ)
◆-=∈-≡ (S∙ inΓ) (◆S∙ ◆Γ) = S∙ (◆-=∈-≡ inΓ ◆Γ)
◆-=∈-≡ (S= inΓ) (◆S= ◆Γ) = S= (◆-=∈-≡ inΓ ◆Γ)

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
