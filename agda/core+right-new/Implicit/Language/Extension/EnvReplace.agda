module Implicit.Language.Extension.EnvReplace where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Occur.All
open import Implicit.Language.EnvOps.All
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Regular.All

open import Implicit.Language.Extension.Base
open import Implicit.Language.Extension.InputOutput
open import Implicit.Language.Extension.ExSol
open import Implicit.Language.Extension.Occur
open import Implicit.Language.Extension.Properties

data ReExt◇◆ (Γ : Env n m) (Δ : Env n m) (k : Fin m) (A : Type m) : Set where
  justexts : ∀ {Γ' Δ'}
           → (newΓ : Γ ◇ k ⇘ Γ')
           → (newΔ : Δ ◆ k ⇘ Δ')
           → (ext : Γ' ⊆ Δ' w/t A)
           → ReExt◇◆ Γ Δ k A

data ReExt◆◆ (Γ : Env n m) (Δ : Env n m) (k : Fin m) (A : Type m) : Set where
  justexts : ∀ {Γ' Δ'}
           → (newΓ : Γ ◆ k ⇘ Γ')
           → (newΔ : Δ ◆ k ⇘ Δ')
           → (ext : Γ' ⊆ Δ' w/t A)
           → ReExt◆◆ Γ Δ k A

data ReExt◇◇ (Γ : Env n m) (Δ : Env n m) (k : Fin m) (A : Type m) : Set where
  justexts : ∀ {Γ' Δ'}
           → (newΓ : Γ ◇ k ⇘ Γ')
           → (newΔ : Δ ◇ k ⇘ Δ')
           → (ext : Γ' ⊆ Δ' w/t A)
           → ReExt◇◇ Γ Δ k A

⊆/x-◇◆ : Γ ⊆ Δ w/v k
        → Γ ∋^ k
        → ReExt◇◆ Γ Δ k (‶ k)
⊆/x-◇◆ (ext-Z^ regΓ cloA) Z = justexts ◇Z ◆Z (ext-var (ext-Z∙ regΓ))
⊆/x-◇◆ (ext-S^ extx) (S^ inΓ) with ⊆/x-◇◆ extx inΓ
... | justexts x x₁ (ext-var x₂) = justexts (◇S^ x) (◆S^ x₁) (ext-var (ext-S^ x₂))
⊆/x-◇◆ (ext-S∙ extx) (S∙ inΓ) with ⊆/x-◇◆ extx inΓ
... | justexts x x₁ (ext-var x₂) = justexts (◇S∙ x) (◆S∙ x₁) (ext-var (ext-S∙ x₂))
⊆/x-◇◆ (ext-S= extx regA) (S= inΓ) with ⊆/x-◇◆ extx inΓ
... | justexts x x₁ (ext-var x₂) = justexts (◇S= x) (◆S= x₁) (ext-var (ext-S= x₂ (⊢r-◇ regA x)))

⊆/x-◆◆ : Γ ⊆ Δ w/v X
        → Γ ∋= k
        → ReExt◆◆ Γ Δ k (‶ X)
⊆/x-◆◆ (ext-Z^ regΓ cloA) (S^ inΓ) with ◆-total inΓ
... | ⟨ Γ' , newΓ ⟩ = justexts (◆S^ newΓ) (◆S= newΓ) (ext-var (ext-Z^ (◆-sregular regΓ newΓ) (⊢r-◆ cloA newΓ)))
⊆/x-◆◆ (ext-Z∙ regΓ) (S∙ inΓ) with ◆-total inΓ
... | ⟨ Γ' , newΓ ⟩ = justexts (◆S∙ newΓ) (◆S∙ newΓ) (ext-var (ext-Z∙ (◆-sregular regΓ newΓ)))
⊆/x-◆◆ (ext-Z= regΓ regA) Z = justexts ◆Z ◆Z (ext-var (ext-Z∙ regΓ))
⊆/x-◆◆ (ext-Z= regΓ regA) (S= inΓ) with ◆-total inΓ
... | ⟨ _ , newΓ ⟩ = justexts (◆S= newΓ) (◆S= newΓ) (ext-var (ext-Z= (◆-sregular regΓ newΓ) (⊢r-◆ regA newΓ)))
⊆/x-◆◆ (ext-S^ ext) (S^ inΓ) with ⊆/x-◆◆ ext inΓ
... | justexts newΓ newΔ (ext-var x) = justexts (◆S^ newΓ) (◆S^ newΔ) (ext-var (ext-S^ x))
⊆/x-◆◆ (ext-S∙ ext) (S∙ inΓ) with ⊆/x-◆◆ ext inΓ
... | justexts newΓ newΔ (ext-var x) = justexts (◆S∙ newΓ) (◆S∙ newΔ) (ext-var (ext-S∙ x))
⊆/x-◆◆ (ext-S= ext regA) Z = justexts ◆Z ◆Z (ext-var (ext-S∙ ext))
⊆/x-◆◆ (ext-S= ext regA) (S= inΓ) with ⊆/x-◆◆ ext inΓ
... | justexts newΓ newΔ (ext-var x) = justexts (◆S= newΓ) (◆S= newΔ) (ext-var (ext-S= x (⊢r-◆ regA newΓ)))

⊆/x-◇◇ : Γ ⊆ Δ w/v X
        → X ≢ k
        → Γ ∋^ k
        → ReExt◇◇ Γ Δ k (‶ X)
⊆/x-◇◇ (ext-Z^ regΓ cloA) neq Z = ⊥-elim (neq refl)
⊆/x-◇◇ (ext-Z^ regΓ cloA) neq (S^ inΓ) with ◇-total inΓ
... | ⟨ Γ' , newΓ ⟩ = justexts (◇S^ newΓ) (◇S= newΓ) (ext-var (ext-Z^ (◇-sregular regΓ newΓ) (⊢r-◇ cloA newΓ)))
⊆/x-◇◇ (ext-Z∙ regΓ) neq (S∙ inΓ) with ◇-total inΓ
... | ⟨ Γ' , newΓ ⟩ = justexts (◇S∙ newΓ) (◇S∙ newΓ) (ext-var (ext-Z∙ (◇-sregular regΓ newΓ)))
⊆/x-◇◇ (ext-Z= regΓ regA) neq (S= inΓ) with ◇-total inΓ
... | ⟨ Γ' , newΓ ⟩ = justexts (◇S= newΓ) (◇S= newΓ) (ext-var (ext-Z= (◇-sregular regΓ newΓ) (⊢r-◇ regA newΓ)))
⊆/x-◇◇ (ext-S^ ext) neq Z = justexts ◇Z ◇Z (ext-var (ext-S∙ ext))
⊆/x-◇◇ (ext-S^ ext) neq (S^ inΓ) with ⊆/x-◇◇ ext (≢-pred neq) inΓ
... | justexts newΓ newΔ (ext-var x) = justexts (◇S^ newΓ) (◇S^ newΔ) (ext-var (ext-S^ x))
⊆/x-◇◇ (ext-S∙ ext) neq (S∙ inΓ) with ⊆/x-◇◇ ext (≢-pred neq) inΓ
... | justexts newΓ newΔ (ext-var x) = justexts (◇S∙ newΓ) (◇S∙ newΔ) (ext-var (ext-S∙ x))
⊆/x-◇◇ (ext-S= ext regA) neq (S= inΓ) with ⊆/x-◇◇ ext (≢-pred neq) inΓ
... | justexts newΓ newΔ (ext-var x) = justexts (◇S= newΓ) (◇S= newΔ) (ext-var (ext-S= x (⊢r-◇ regA newΓ)))

⊆/-◆◇ : Γ ⊆ Δ w/t A
       → k ε A
       → Γ ∋^ k
       → ReExt◇◆ Γ Δ k A

⊆/-◆◇-derived : Γ ⊆ Δ w/t A
               → Γ ◇ k ⇘ Γ'
               → Δ ◆ k ⇘ Δ'
               → Γ' ⊆ Δ' w/t A
⊆/-◆◇-derived {k = k} ext newΓ newΔ with ⊆/-◆◇ ext (^in-=out-ε ext (◇-∋^ newΓ) (◆-∋= newΔ)) (◇-∋^ newΓ)
... | justexts newΓ₁ newΔ₁ ext₁ rewrite ◆-unique newΔ newΔ₁ | ◇-unique newΓ newΓ₁ = ext₁

⊆/-◆◆ : Γ ⊆ Δ w/t A
       → Γ ∋= k
       → ReExt◆◆ Γ Δ k A

⊆/-◇◇ : Γ ⊆ Δ w/t A
       → k ¬ε A
       → Γ ∋^ k
       → ReExt◇◇ Γ Δ k A

⊆/-◆◇ (ext-var x) ε-var inΓ = ⊆/x-◇◆ x inΓ
⊆/-◆◇ (ext-arr ext ext₁) (ε-arr-l ¬inB inA) inΓ with ⊆/-◇◇ ext₁ ¬inB inΓ | ⊆/-◆◇ ext inA (⊆/-^in-^out ext₁ ¬inB inΓ)
... | justexts newΓ newΔ ext₂ | justexts newΓ₁ newΔ₁ ext₃
  with refl ← ◇-unique newΔ newΓ₁ = justexts newΓ newΔ₁ (ext-arr ext₃ ext₂)
⊆/-◆◇ {k = k} (ext-arr {A = A} ext ext₁) (ε-arr-r inA) inΓ with ⊆/-◆◇ ext₁ inA inΓ | ⊆/-◆◆ ext (⊆/-^in-=out ext₁ inA inΓ)
... | justexts newΓ newΔ ext₂ | justexts newΓ₁ newΔ₁ ext₃
  with refl ← ◆-unique newΔ newΓ₁ = justexts newΓ newΔ₁ (ext-arr ext₃ ext₂)
⊆/-◆◇ (ext-∀ ext) (ε-∀ inA) inΓ with ⊆/-◆◇ ext inA (S∙ inΓ)
... | justexts (◇S∙ newΓ) (◆S∙ newΔ) ext' = justexts newΓ newΔ (ext-∀ ext')

⊆/-◆◆ (ext-int regΓ) inΓ with ◆-total inΓ
... | ⟨ Γ' , newΓ ⟩ = justexts newΓ newΓ (ext-int (◆-sregular regΓ newΓ))
⊆/-◆◆ (ext-var x) inΓ = ⊆/x-◆◆ x inΓ
⊆/-◆◆ (ext-arr ext ext₁) inΓ
  with justexts x x₁ x₂ ← ⊆/-◆◆ ext₁ inΓ
  with justexts x' x₁' x₂' ← ⊆/-◆◆ ext (⊆/-=in-=out ext₁ inΓ)
  with refl ← ◆-unique x' x₁ = justexts x x₁' (ext-arr x₂' x₂)
⊆/-◆◆ (ext-∀ ext) inΓ with ⊆/-◆◆ ext (S∙ inΓ)
... | justexts (◆S∙ x) (◆S∙ x₁) ext' = justexts x x₁ (ext-∀ ext')

⊆/-◇◇ (ext-int regΓ) ¬ε-int inΓ with ◇-total inΓ
... | ⟨ Γ' , newΓ ⟩ = justexts newΓ newΓ (ext-int (◇-sregular regΓ newΓ))
⊆/-◇◇ (ext-var x) (¬ε-var x₁) inΓ = ⊆/x-◇◇ x x₁ inΓ
⊆/-◇◇ (ext-arr ext ext₁) (¬ε-arr ¬inA ¬inA₁) inΓ with ⊆/-◇◇ ext₁ ¬inA₁ inΓ | ⊆/-◇◇ ext ¬inA (⊆/-^in-^out ext₁ ¬inA₁ inΓ)
... | justexts newΓ newΔ ext₂ | justexts newΓ₁ newΔ₁ ext₃
  with refl ← ◇-unique newΔ newΓ₁ = justexts newΓ newΔ₁ (ext-arr ext₃ ext₂)
⊆/-◇◇ (ext-∀ ext) (¬ε-∀ ¬inA) inΓ with ⊆/-◇◇ ext ¬inA (S∙ inΓ)
... | justexts (◇S∙ newΓ) (◇S∙ newΔ) ext₁ = justexts newΓ newΔ (ext-∀ ext₁)


⊆/-◆◆0 : Γ ,= B ⊆ Δ ,= B w/t A
       → Γ ,∙ ⊆ Δ ,∙ w/t A
⊆/-◆◆0 ext with ⊆/-◆◆ ext Z
... | justexts ◆Z ◆Z ext₁ = ext₁


⊆/-◇◇0 : Γ ,^ ⊆ Δ ,^ w/t A
       → Γ ,∙ ⊆ Δ ,∙ w/t A
⊆/-◇◇0 ext with ⊆/-◇◇ ext (⊢c-^∈-¬ε (⊆/-⊢c ext) Z) Z
... | justexts ◇Z ◇Z ext₁ = ext₁


⊆/-◇◆0 : Γ ,^ ⊆ Δ ,= B w/t A
       → Γ ,∙ ⊆ Δ ,∙ w/t A
⊆/-◇◆0 ext with ⊆/-◆◇ ext (^in-=out-ε ext Z Z) Z
... | justexts ◇Z ◆Z ext₁ = ext₁
