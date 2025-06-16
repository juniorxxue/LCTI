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

⊢c-◇0 : Γ ,^ ⊢c A
        → Γ ,∙ ⊢c A
⊢c-◇0 cloA = ⊢c-◇ cloA ◇Z

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



infix 3 [_/_]_∙⟹_
data [_/_]_∙⟹_ : Type m → Fin m → Env n m → Env n m → Set where
  ∙⟹^0 : (up : ↑ty0 A ⇘ A')
         → (regA : Γ ⊢r A)
         → [ A' / #0 ] (Γ ,∙) ∙⟹ (Γ ,= A)

  ∙⟹^S : [ A / k ] Γ ∙⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,^) ∙⟹ Γ' ,^

  ∙⟹∙S : [ A / k ] Γ ∙⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,∙) ∙⟹ (Γ' ,∙)

  ∙⟹,S : [ A / k ] Γ ∙⟹ Γ'
       → [ A / k ] (Γ , B) ∙⟹ (Γ' , B)

  ∙⟹=S : [ A / k ] Γ ∙⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,= B) ∙⟹ (Γ' ,= B)


∙⟹-∋∙ : Γ ∋∙ X
        → X ≢ k
        → [ T / k ] Γ ∙⟹ Γ'
        → Γ' ∋∙ X
∙⟹-∋∙ Z neq (∙⟹^0 up regA) = ⊥-elim (neq refl)
∙⟹-∋∙ Z neq (∙⟹∙S new up1) = Z
∙⟹-∋∙ (S, inΓ) neq (∙⟹,S new) = S, (∙⟹-∋∙ inΓ neq new)
∙⟹-∋∙ (S∙ inΓ) neq (∙⟹^0 up regA) = S= inΓ
∙⟹-∋∙ (S∙ inΓ) neq (∙⟹∙S new up1) = S∙ (∙⟹-∋∙ inΓ (≢-pred neq) new)
∙⟹-∋∙ (S= inΓ) neq (∙⟹=S new up1) = S= (∙⟹-∋∙ inΓ (≢-pred neq) new)
∙⟹-∋∙ (S^ inΓ) neq (∙⟹^S new up1) = S^ (∙⟹-∋∙ inΓ (≢-pred neq) new)


∙⟹-⊢r : Γ ⊢r A
      → [ T / k ] Γ ∙⟹ Γ'
      → k ¬ε A
      → Γ' ⊢r A
∙⟹-⊢r ⊢r-int new ¬ε-int = ⊢r-int
∙⟹-⊢r (⊢r-var-∙ inΓ) new (¬ε-var x) = ⊢r-var-∙ (∙⟹-∋∙ inΓ x new)
∙⟹-⊢r (⊢r-arr regA regA₁) new (¬ε-arr ninA ninA₁) = ⊢r-arr (∙⟹-⊢r regA new ninA) (∙⟹-⊢r regA₁ new ninA₁)
∙⟹-⊢r {T = T} (⊢r-∀ regA) new (¬ε-∀ ninA)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢r-∀ (∙⟹-⊢r regA (∙⟹∙S new upT) ninA)


∙⟹-∋:=-prv : Γ ∋ X := A
       → [ T / k ] Γ ∙⟹ Γ'
       → Γ' ∋ X := A
∙⟹-∋:=-prv (Z up) (∙⟹=S new up1) = Z up
∙⟹-∋:=-prv (S∙ inΓ up) (∙⟹^0 up₁ regA) = S= inΓ up
∙⟹-∋:=-prv (S∙ inΓ up) (∙⟹∙S new up1) = S∙ (∙⟹-∋:=-prv inΓ new) up
∙⟹-∋:=-prv (S^ inΓ up) (∙⟹^S new up1) = S^ (∙⟹-∋:=-prv inΓ new) up
∙⟹-∋:=-prv (S= inΓ up) (∙⟹=S new up1) = S= (∙⟹-∋:=-prv inΓ new) up
∙⟹-∋:=-prv (S, inΓ) (∙⟹,S new) = S, (∙⟹-∋:=-prv inΓ new)

∙⟹-∋:= : [ T / k ] Γ ∙⟹ Γ'
         → Γ' ∋ k := T
∙⟹-∋:= (∙⟹^0 up regA) = Z up
∙⟹-∋:= (∙⟹^S new up1) = S^ (∙⟹-∋:= new) up1
∙⟹-∋:= (∙⟹∙S new up1) = S∙ (∙⟹-∋:= new) up1
∙⟹-∋:= (∙⟹,S new) = S, (∙⟹-∋:= new)
∙⟹-∋:= (∙⟹=S new up1) = S= (∙⟹-∋:= new) up1


∙⟹-∋∙-neq : Γ ∋∙ X
          → [ T' / k ] Γ ∙⟹ Γ'
          → Γ' ∋∙ X
          → k ≢ X
∙⟹-∋∙-neq Z (∙⟹∙S new up1) Z = λ ()
∙⟹-∋∙-neq (S, inΓ) (∙⟹,S new) (S, inΓ') = ∙⟹-∋∙-neq inΓ new inΓ'
∙⟹-∋∙-neq (S∙ inΓ) (∙⟹^0 up regA) (S= inΓ') = λ ()
∙⟹-∋∙-neq (S∙ inΓ) (∙⟹∙S new up1) (S∙ inΓ') = ≢-suc (∙⟹-∋∙-neq inΓ new inΓ')
∙⟹-∋∙-neq (S= inΓ) (∙⟹=S new up1) (S= inΓ') = ≢-suc (∙⟹-∋∙-neq inΓ new inΓ')
∙⟹-∋∙-neq (S^ inΓ) (∙⟹^S new up1) (S^ inΓ') = ≢-suc (∙⟹-∋∙-neq inΓ new inΓ')


∙⟹-:=-eq : Γ ∋ X := A₁
          → [ B / k ] Γ ∙⟹ Γ'
          → Γ' ∋ X := A₂
          → A₁ ≡ A₂
∙⟹-:=-eq (Z up) (∙⟹=S newΓ up1) (Z up₁) = ↑ty-unique up up₁
∙⟹-:=-eq (S, in1) (∙⟹,S newΓ) (S, in2) = ∙⟹-:=-eq in1 newΓ in2
∙⟹-:=-eq (S∙ in1 up) (∙⟹^0 reg up₁) (S= in2 up₂) with ∋:=-unique in1 in2
... | refl = ↑ty-unique up up₂
∙⟹-:=-eq (S∙ in1 up) (∙⟹∙S newΓ up1) (S∙ in2 up₁) with ∙⟹-:=-eq in1 newΓ in2
... | refl = ↑ty-unique up up₁
∙⟹-:=-eq (S^ in1 up) (∙⟹^S newΓ up1) (S^ in2 up₁) with ∙⟹-:=-eq in1 newΓ in2
... | refl = ↑ty-unique up up₁
∙⟹-:=-eq (S= in1 up) (∙⟹=S newΓ up1) (S= in2 up₁) with ∙⟹-:=-eq in1 newΓ in2
... | refl = ↑ty-unique up up₁

∙⟹-:=-∙-false : Γ ∋ X := A
               → [ B / k ] Γ ∙⟹ Γ'
               → Γ' ∋∙ X
               → ⊥
∙⟹-:=-∙-false (Z up) (∙⟹=S newΓ' up1) ()
∙⟹-:=-∙-false (S, inΓ) (∙⟹,S newΓ') (S, inΓ') = ∙⟹-:=-∙-false inΓ newΓ' inΓ'
∙⟹-:=-∙-false (S∙ inΓ up) (∙⟹^0 reg up₁) (S= inΓ') = ∋∙-∋:=-false inΓ' inΓ
∙⟹-:=-∙-false (S∙ inΓ up) (∙⟹∙S newΓ' up1) (S∙ inΓ') = ∙⟹-:=-∙-false inΓ newΓ' inΓ'
∙⟹-:=-∙-false (S^ inΓ up) (∙⟹^S newΓ' up1) (S^ inΓ') = ∙⟹-:=-∙-false inΓ newΓ' inΓ'
∙⟹-:=-∙-false (S= inΓ up) (∙⟹=S newΓ' up1) (S= inΓ') = ∙⟹-:=-∙-false inΓ newΓ' inΓ'

∙⟹-∙-:=-eq : Γ ∋∙ k
            → [ B / k ] Γ ∙⟹ Γ'
            → Γ' ∋ k := A
            → A ≡ B
∙⟹-∙-:=-eq Z (∙⟹^0 reg up) (Z up₁) = ↑ty-unique up₁ reg
∙⟹-∙-:=-eq (S, inΓ) (∙⟹,S newΓ) (S, inΓ') = ∙⟹-∙-:=-eq inΓ newΓ inΓ'
∙⟹-∙-:=-eq (S∙ inΓ) (∙⟹∙S newΓ up1) (S∙ inΓ' up) with ∙⟹-∙-:=-eq inΓ newΓ inΓ'
... | refl = ↑ty-unique up up1
∙⟹-∙-:=-eq (S= inΓ) (∙⟹=S newΓ up1) (S= inΓ' up) with ∙⟹-∙-:=-eq inΓ newΓ inΓ'
... | refl = ↑ty-unique up up1
∙⟹-∙-:=-eq (S^ inΓ) (∙⟹^S newΓ up1) (S^ inΓ' up) with ∙⟹-∙-:=-eq inΓ newΓ inΓ'
... | refl = ↑ty-unique up up1

∙⟹-∙-:=-neq-false : Γ ∋∙ X
                   → [ B / k ] Γ ∙⟹ Γ'
                   → Γ' ∋ X := A
                   → k ≢ X
                   → ⊥
∙⟹-∙-:=-neq-false Z (∙⟹^0 up reg) inΓ' neq = neq refl
∙⟹-∙-:=-neq-false (S, inΓ) (∙⟹,S newΓ) (S, inΓ') neq = ∙⟹-∙-:=-neq-false inΓ newΓ inΓ' neq
∙⟹-∙-:=-neq-false (S∙ inΓ) (∙⟹^0 up reg) (S= inΓ' up₁) neq = ∋∙-∋:=-false inΓ inΓ'
∙⟹-∙-:=-neq-false (S∙ inΓ) (∙⟹∙S newΓ up1) (S∙ inΓ' up) neq = ∙⟹-∙-:=-neq-false inΓ newΓ inΓ' (≢-pred neq)
∙⟹-∙-:=-neq-false (S= inΓ) (∙⟹=S newΓ up1) (S= inΓ' up) neq = ∙⟹-∙-:=-neq-false inΓ newΓ inΓ' (≢-pred neq)
∙⟹-∙-:=-neq-false (S^ inΓ) (∙⟹^S newΓ up1) (S^ inΓ' up) neq = ∙⟹-∙-:=-neq-false inΓ newΓ inΓ' (≢-pred neq)

∙⟹-∙-eq-false : Γ ∋∙ k
               → [ A / k ] Γ ∙⟹ Γ'
               → Γ' ∋∙ k
               → ⊥
∙⟹-∙-eq-false Z (∙⟹^0 up reg) ()
∙⟹-∙-eq-false (S, inΓ) (∙⟹,S newΓ) (S, inΓ') = ∙⟹-∙-eq-false inΓ newΓ inΓ'
∙⟹-∙-eq-false (S∙ inΓ) (∙⟹∙S newΓ up1) (S∙ inΓ') = ∙⟹-∙-eq-false inΓ newΓ inΓ'
∙⟹-∙-eq-false (S= inΓ) (∙⟹=S newΓ up1) (S= inΓ') = ∙⟹-∙-eq-false inΓ newΓ inΓ'
∙⟹-∙-eq-false (S^ inΓ) (∙⟹^S newΓ up1) (S^ inΓ') = ∙⟹-∙-eq-false inΓ newΓ inΓ'
