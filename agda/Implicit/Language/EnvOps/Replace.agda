module Implicit.Language.EnvOps.Replace where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.EnvOps.Base

◆-unique : Γ ◆ k ⇘ Γ₁
         → Γ ◆ k ⇘ Γ₂
         → Γ₁ ≡ Γ₂
◆-unique ◆Z ◆Z = refl
◆-unique (◆S, new1) (◆S, new2) rewrite ◆-unique new1 new2 = refl
◆-unique (◆S∙ new1) (◆S∙ new2) rewrite ◆-unique new1 new2 = refl
◆-unique (◆S= new1) (◆S= new2) rewrite ◆-unique new1 new2 = refl
◆-unique (◆S^ new1) (◆S^ new2) rewrite ◆-unique new1 new2 = refl

◆-total : Γ ∋= k
        → ∃[ Γ' ](Γ ◆ k ⇘ Γ')
◆-total {Γ = Γ ,= _} Z = ⟨ Γ ,∙ , ◆Z ⟩
◆-total (S, {B = B} inΓ) with ◆-total inΓ
... | ⟨ Γ' , newΓ ⟩ = ⟨ (Γ' , B) , ◆S, newΓ ⟩
◆-total (S∙ inΓ) = ⟨ (◆-total inΓ .proj₁ ,∙) , ◆S∙ (◆-total inΓ .proj₂) ⟩
◆-total (S^ inΓ) = ⟨ ◆-total inΓ .proj₁ ,^ , ◆S^ (◆-total inΓ .proj₂) ⟩
◆-total (S= {B = B} inΓ) = ⟨ (◆-total inΓ .proj₁ ,= B) , ◆S= (◆-total inΓ .proj₂) ⟩

◇-total : Γ ∋^ k
        → ∃[ Γ' ](Γ ◇ k ⇘ Γ')
◇-total {Γ = Γ ,^ } Z = ⟨ Γ ,∙ , ◇Z ⟩
◇-total (S, {A = A} inΓ) = ⟨ (◇-total inΓ .proj₁ , A) , ◇S, (◇-total inΓ .proj₂) ⟩
◇-total (S∙ inΓ) = ⟨ ◇-total inΓ .proj₁ ,∙ , ◇S∙ (◇-total inΓ .proj₂) ⟩
◇-total (S= {B = B} inΓ) = ⟨ ◇-total inΓ .proj₁ ,= B , ◇S= (◇-total inΓ .proj₂) ⟩
◇-total (S^ inΓ) = ⟨ ◇-total inΓ .proj₁ ,^ , ◇S^ (◇-total inΓ .proj₂) ⟩

◇-unique : Γ ◇ k ⇘ Γ₁
         → Γ ◇ k ⇘ Γ₂
         → Γ₁ ≡ Γ₂
◇-unique ◇Z ◇Z = refl
◇-unique (◇S, in1) (◇S, in2) rewrite ◇-unique in1 in2 = refl
◇-unique (◇S∙ in1) (◇S∙ in2) rewrite ◇-unique in1 in2 = refl
◇-unique (◇S= in1) (◇S= in2) rewrite ◇-unique in1 in2 = refl
◇-unique (◇S^ in1) (◇S^ in2) rewrite ◇-unique in1 in2 = refl


◆-∙∈ : Γ ∋∙ X
     → Γ ◆ k ⇘ Γ'
     → Γ' ∋∙ X
◆-∙∈ (S= inΓ) ◆Z = S∙ inΓ
◆-∙∈ (S, inΓ) (◆S, ◆Γ) = S, (◆-∙∈ inΓ ◆Γ)
◆-∙∈ Z (◆S∙ ◆Γ) = Z
◆-∙∈ (S∙ inΓ) (◆S∙ ◆Γ) = S∙ (◆-∙∈ inΓ ◆Γ)
◆-∙∈ (S= inΓ) (◆S= ◆Γ) = S= (◆-∙∈ inΓ ◆Γ)
◆-∙∈ (S^ inΓ) (◆S^ ◆Γ) = S^ (◆-∙∈ inΓ ◆Γ)

◇-∙∈ : Γ ∋∙ X
     → Γ ◇ k ⇘ Γ'
     → Γ' ∋∙ X
◇-∙∈ Z (◇S∙ newΓ) = Z
◇-∙∈ (S, inΓ) (◇S, newΓ) = S, (◇-∙∈ inΓ newΓ)
◇-∙∈ (S∙ inΓ) (◇S∙ newΓ) = S∙ (◇-∙∈ inΓ newΓ)
◇-∙∈ (S= inΓ) (◇S= newΓ) = S= (◇-∙∈ inΓ newΓ)
◇-∙∈ (S^ inΓ) ◇Z = S∙ inΓ
◇-∙∈ (S^ inΓ) (◇S^ newΓ) = S^ (◇-∙∈ inΓ newΓ)

◇-=∈ : Γ ∋= X
     → Γ ◇ k ⇘ Γ'
     → Γ' ∋= X
◇-=∈ Z (◇S= newΓ) = Z
◇-=∈ (S, inΓ) (◇S, newΓ) = S, (◇-=∈ inΓ newΓ)
◇-=∈ (S∙ inΓ) (◇S∙ newΓ) = S∙ (◇-=∈ inΓ newΓ)
◇-=∈ (S= inΓ) (◇S= newΓ) = S= (◇-=∈ inΓ newΓ)
◇-=∈ (S^ inΓ) ◇Z = S∙ inΓ
◇-=∈ (S^ inΓ) (◇S^ newΓ) = S^ (◇-=∈ inΓ newΓ)

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


env-◆◇-false : Γ ◇ k ⇘ Γ₁
             → Γ ◆ k ⇘ Γ₂
             → ⊥
env-◆◇-false (◇S, newΓ1) (◆S, newΓ2) = env-◆◇-false newΓ1 newΓ2
env-◆◇-false (◇S∙ newΓ1) (◆S∙ newΓ2) = env-◆◇-false newΓ1 newΓ2
env-◆◇-false (◇S= newΓ1) (◆S= newΓ2) = env-◆◇-false newΓ1 newΓ2
env-◆◇-false (◇S^ newΓ1) (◆S^ newΓ2) = env-◆◇-false newΓ1 newΓ2

◇-∋^ : Γ ◇ k ⇘ Γ'
     → Γ ∋^ k
◇-∋^ ◇Z = Z
◇-∋^ (◇S, newΓ) = S, (◇-∋^ newΓ)
◇-∋^ (◇S∙ newΓ) = S∙ (◇-∋^ newΓ)
◇-∋^ (◇S= newΓ) = S= (◇-∋^ newΓ)
◇-∋^ (◇S^ newΓ) = S^ (◇-∋^ newΓ)

◆-∋= : Γ ◆ k ⇘ Γ'
     → Γ ∋= k
◆-∋= ◆Z = Z
◆-∋= (◆S, newΓ) = S, (◆-∋= newΓ)
◆-∋= (◆S∙ newΓ) = S∙ (◆-∋= newΓ)
◆-∋= (◆S= newΓ) = S= (◆-∋= newΓ)
◆-∋= (◆S^ newΓ) = S^ (◆-∋= newΓ)
