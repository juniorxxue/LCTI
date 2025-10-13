module Implicit.Language.EnvOps.Replace where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.EnvOps.Base
open import Implicit.Language.Regular.Base
open import Implicit.Language.OpenClose.Base

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
◆-total (S∙ inΓ) = ⟨ (◆-total inΓ .proj₁ ,∙) , ◆S∙ (◆-total inΓ .proj₂) ⟩
◆-total (S^ inΓ) = ⟨ ◆-total inΓ .proj₁ ,^ , ◆S^ (◆-total inΓ .proj₂) ⟩
◆-total (S= {B = B} inΓ) = ⟨ (◆-total inΓ .proj₁ ,= B) , ◆S= (◆-total inΓ .proj₂) ⟩
◆-total {Γ = Γ , A} (S, inΓ) = ⟨ ((◆-total inΓ .proj₁) , A) , ◆S, (◆-total inΓ .proj₂) ⟩

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


⊢r-◆ : Γ ⊢r A
     → Γ ◆ k ⇘ Γ'
     → Γ' ⊢r A
⊢r-◆ ⊢r-int new = ⊢r-int
⊢r-◆ (⊢r-var-∙ inΓ) new = ⊢r-var-∙ (◆-∙∈ inΓ new)
⊢r-◆ (⊢r-arr regA regA₁) new = ⊢r-arr (⊢r-◆ regA new) (⊢r-◆ regA₁ new)
⊢r-◆ (⊢r-∀ regA) new = ⊢r-∀ (⊢r-◆ regA (◆S∙ new))

⊢r-◆0 : Γ ,= T ⊢r A
     → Γ ,∙ ⊢r A
⊢r-◆0 regA = ⊢r-◆ regA ◆Z


⊢c-◆ : Γ ⊢c A
     → Γ ◆ k ⇘ Γ'
     → Γ' ⊢c A
⊢c-◆ ⊢c-int new = ⊢c-int
⊢c-◆ (⊢c-var-∙ inΔ) new = ⊢c-var-∙ (◆-∙∈ inΔ new)
⊢c-◆ {k = k} (⊢c-var-= {X = X} inΔ) new with k #≟ X
... | yes refl = ⊢c-var-∙ (◆-=∈-≡ inΔ new)
... | no ¬p = ⊢c-var-= (◆-=∈-≢ inΔ new ¬p)
⊢c-◆ (⊢c-arr cloA cloA₁) new = ⊢c-arr (⊢c-◆ cloA new) (⊢c-◆ cloA₁ new)
⊢c-◆ (⊢c-∀ cloA) new = ⊢c-∀ (⊢c-◆ cloA (◆S∙ new))

⊢c-◆0 : Γ ,= T ⊢c A
      → Γ ,∙ ⊢c A
⊢c-◆0 cloA = ⊢c-◆ cloA ◆Z


⊢c-◇ : Γ ⊢c A
     → Γ ◇ k ⇘ Γ'
     → Γ' ⊢c A
⊢c-◇ ⊢c-int new = ⊢c-int
⊢c-◇ (⊢c-var-∙ inΔ) new = ⊢c-var-∙ (◇-∙∈ inΔ new)
⊢c-◇ (⊢c-var-= inΔ) new = ⊢c-var-= (◇-=∈ inΔ new)
⊢c-◇ (⊢c-arr cloA cloA₁) new = ⊢c-arr (⊢c-◇ cloA new) (⊢c-◇ cloA₁ new)
⊢c-◇ (⊢c-∀ cloA) new = ⊢c-∀ (⊢c-◇ cloA (◇S∙ new))

⊢r-◇ : Γ ⊢r A
     → Γ ◇ k ⇘ Γ'
     → Γ' ⊢r A
⊢r-◇ ⊢r-int new = ⊢r-int
⊢r-◇ (⊢r-var-∙ inΓ) new = ⊢r-var-∙ (◇-∙∈ inΓ new)
⊢r-◇ (⊢r-arr regA regA₁) new = ⊢r-arr (⊢r-◇ regA new) (⊢r-◇ regA₁ new)
⊢r-◇ (⊢r-∀ regA) new = ⊢r-∀ (⊢r-◇ regA (◇S∙ new))

⊢c-◇0 : Γ ,^ ⊢c A
        → Γ ,∙ ⊢c A
⊢c-◇0 cloA = ⊢c-◇ cloA ◇Z

◆-sregular : SRegular Γ
           → Γ ◆ k ⇘ Γ'
           → SRegular Γ'
◆-sregular (reg-S∙ regΓ) (◆S∙ new) = reg-S∙ (◆-sregular regΓ new)
◆-sregular (reg-S^ regΓ) (◆S^ new) = reg-S^ (◆-sregular regΓ new)
◆-sregular (reg-S= regΓ regA) ◆Z = reg-S∙ regΓ
◆-sregular (reg-S= regΓ regA) (◆S= new) = reg-S= (◆-sregular regΓ new) (⊢r-◆ regA new)

◇-sregular : SRegular Γ
           → Γ ◇ k ⇘ Γ'
           → SRegular Γ'
◇-sregular (reg-S∙ regΓ) (◇S∙ new) = reg-S∙ (◇-sregular regΓ new)
◇-sregular (reg-S^ regΓ) ◇Z = reg-S∙ regΓ
◇-sregular (reg-S^ regΓ) (◇S^ new) = reg-S^ (◇-sregular regΓ new)
◇-sregular (reg-S= regΓ regA) (◇S= new) = reg-S= (◇-sregular regΓ new) (⊢r-◇ regA new)

◈-∋:=-neq-unique : Γ ◈ k ⇘ Γ'
                 → X ≢ k
                 → Γ ∋ X := A₁
                 → Γ' ∋ X := A₂
                 → A₁ ≡ A₂
◈-∋:=-neq-unique ◈Z neq (S∙ in1 up) (S^ in2 up₁)
  with refl ← ∋:=-unique in1 in2 = ↑ty-unique up up₁
◈-∋:=-neq-unique (◈S, new) neq (S, in1) (S, in2) = ◈-∋:=-neq-unique new neq in1 in2
◈-∋:=-neq-unique (◈S∙ new) neq (S∙ in1 up) (S∙ in2 up₁)
  with refl ← ◈-∋:=-neq-unique new (≢-pred neq) in1 in2 = ↑ty-unique up up₁
◈-∋:=-neq-unique (◈S= new) neq (Z up) (Z up₁) = ↑ty-unique up up₁
◈-∋:=-neq-unique (◈S= new) neq (S= in1 up) (S= in2 up₁)
  with refl ← ◈-∋:=-neq-unique new (≢-pred neq) in1 in2 = ↑ty-unique up up₁
◈-∋:=-neq-unique (◈S^ new) neq (S^ in1 up) (S^ in2 up₁)
  with refl ← ◈-∋:=-neq-unique new (≢-pred neq) in1 in2 = ↑ty-unique up up₁

◈-neq-∋:= : Γ ∋ X := A
          → Γ ◈ k ⇘ Γ'
          → X ≢ k
          → Γ' ∋ X := A
◈-neq-∋:= (Z up) (◈S= new) neq = Z up
◈-neq-∋:= (S∙ inΓ up) ◈Z neq = S^ inΓ up
◈-neq-∋:= (S∙ inΓ up) (◈S∙ new) neq = S∙ (◈-neq-∋:= inΓ new (≢-pred neq)) up
◈-neq-∋:= (S^ inΓ up) (◈S^ new) neq = S^ (◈-neq-∋:= inΓ new (≢-pred neq)) up
◈-neq-∋:= (S= inΓ up) (◈S= new) neq = S= (◈-neq-∋:= inΓ new (≢-pred neq)) up
◈-neq-∋:= (S, inΓ) (◈S, new) neq = S, (◈-neq-∋:= inΓ new neq)

◈-neq-∋∙ : Γ ∋∙ X
         → Γ ◈ k ⇘ Γ'
         → X ≢ k
         → Γ' ∋∙ X
◈-neq-∋∙ Z ◈Z neq = ⊥-elim (neq refl)
◈-neq-∋∙ Z (◈S∙ new) neq = Z
◈-neq-∋∙ (S, in1) (◈S, new) neq = S, (◈-neq-∋∙ in1 new neq)
◈-neq-∋∙ (S∙ in1) ◈Z neq = S^ in1
◈-neq-∋∙ (S∙ in1) (◈S∙ new) neq = S∙ (◈-neq-∋∙ in1 new (≢-pred neq))
◈-neq-∋∙ (S= in1) (◈S= new) neq = S= (◈-neq-∋∙ in1 new (≢-pred neq))
◈-neq-∋∙ (S^ in1) (◈S^ new) neq = S^ (◈-neq-∋∙ in1 new (≢-pred neq))
