module Implicit.Language.Extension.EnvReplace where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Occur.All
open import Implicit.Language.EnvOps.All
open import Implicit.Language.OpenClose.All

open import Implicit.Language.Extension.Base
open import Implicit.Language.Extension.InputOutput
open import Implicit.Language.Extension.ExSol
open import Implicit.Language.Extension.Occur

data ReExt◆◇ (Γ : Env n m) (Δ : Env n m) (k : Fin m) (A : Type m) : Set where
  justexts : ∀ {Γ' Δ'}
           → (newΓ : Γ ◇ k ⇘ Γ')
           → (newΔ : Δ ◆ k ⇘ Δ')
           → (ext : Γ' ⊆ Δ' w/t A)
           → ReExt◆◇ Γ Δ k A

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

extx-◆◇ : Γ ⊆ Δ w/v k
        → Γ ∋^ k
        → ReExt◆◇ Γ Δ k (‶ k)
extx-◆◇ (ext-Z^ cloA) Z = justexts ◇Z ◆Z (ext-var ext-Z∙)
extx-◆◇ (ext-S, extx) (S, inΓ) with extx-◆◇ extx inΓ
... | justexts x x₁ (ext-var x₂) = justexts (◇S, x) (◆S, x₁) (ext-var (ext-S, x₂))
extx-◆◇ (ext-S^ extx) (S^ inΓ) with extx-◆◇ extx inΓ
... | justexts x x₁ (ext-var x₂) = justexts (◇S^ x) (◆S^ x₁) (ext-var (ext-S^ x₂))
extx-◆◇ (ext-S∙ extx) (S∙ inΓ) with extx-◆◇ extx inΓ
... | justexts x x₁ (ext-var x₂) = justexts (◇S∙ x) (◆S∙ x₁) (ext-var (ext-S∙ x₂))
extx-◆◇ (ext-S= extx) (S= inΓ) with extx-◆◇ extx inΓ
... | justexts x x₁ (ext-var x₂) = justexts (◇S= x) (◆S= x₁) (ext-var (ext-S= x₂))

extx-◆◆ : Γ ⊆ Δ w/v X
        → Γ ∋= k
        → ReExt◆◆ Γ Δ k (‶ X)
extx-◆◆ (ext-Z^ cloA) (S^ inΓ) with ◆-total inΓ
... | ⟨ Γ' , newΓ ⟩ = justexts (◆S^ newΓ) (◆S= newΓ) (ext-var (ext-Z^ (⊢c-◆ cloA newΓ)))
extx-◆◆ ext-Z∙ (S∙ inΓ) with ◆-total inΓ
... | ⟨ _ , newΓ ⟩ = justexts (◆S∙ newΓ) (◆S∙ newΓ) (ext-var ext-Z∙)
extx-◆◆ ext-Z= Z = justexts ◆Z ◆Z (ext-var ext-Z∙)
extx-◆◆ ext-Z= (S= inΓ) with ◆-total inΓ
... | ⟨ _ , newΓ ⟩ = justexts (◆S= newΓ) (◆S= newΓ) (ext-var ext-Z=)
extx-◆◆ (ext-S, ext) (S, inΓ) with extx-◆◆ ext inΓ
... | justexts newΓ newΔ (ext-var x) = justexts (◆S, newΓ) (◆S, newΔ) (ext-var (ext-S, x))
extx-◆◆ (ext-S^ ext) (S^ inΓ) with extx-◆◆ ext inΓ
... | justexts newΓ newΔ (ext-var x) = justexts (◆S^ newΓ) (◆S^ newΔ) (ext-var (ext-S^ x))
extx-◆◆ (ext-S∙ ext) (S∙ inΓ) with extx-◆◆ ext inΓ
... | justexts newΓ newΔ (ext-var x) = justexts (◆S∙ newΓ) (◆S∙ newΔ) (ext-var (ext-S∙ x))
extx-◆◆ (ext-S= ext) Z = justexts ◆Z ◆Z (ext-var (ext-S∙ ext))
extx-◆◆ (ext-S= ext) (S= inΓ) with extx-◆◆ ext inΓ
... | justexts newΓ newΔ (ext-var x) = justexts (◆S= newΓ) (◆S= newΔ) (ext-var (ext-S= x))

extx-◇◇ : Γ ⊆ Δ w/v X
        → X ≢ k
        → Γ ∋^ k
        → ReExt◇◇ Γ Δ k (‶ X)
extx-◇◇ (ext-Z^ cloA) neq Z = ⊥-elim (neq refl)
extx-◇◇ (ext-Z^ cloA) neq (S^ inΓ) with ◇-total inΓ
... | ⟨ Γ' , newΓ ⟩ = justexts (◇S^ newΓ) (◇S= newΓ) (ext-var (ext-Z^ (⊢c-◇ cloA newΓ)))
extx-◇◇ ext-Z∙ neq (S∙ inΓ) with ◇-total inΓ
... | ⟨ Γ' , newΓ ⟩ = justexts (◇S∙ newΓ) (◇S∙ newΓ) (ext-var ext-Z∙)
extx-◇◇ ext-Z= neq (S= inΓ) with ◇-total inΓ
... | ⟨ Γ' , newΓ ⟩ = justexts (◇S= newΓ) (◇S= newΓ) (ext-var ext-Z=)
extx-◇◇ (ext-S, ext) neq (S, inΓ) with extx-◇◇ ext neq inΓ
... | justexts newΓ newΔ (ext-var x) = justexts (◇S, newΓ) (◇S, newΔ) (ext-var (ext-S, x))
extx-◇◇ (ext-S^ ext) neq Z = justexts ◇Z ◇Z (ext-var (ext-S∙ ext))
extx-◇◇ (ext-S^ ext) neq (S^ inΓ) with extx-◇◇ ext (≢-pred neq) inΓ
... | justexts newΓ newΔ (ext-var x) = justexts (◇S^ newΓ) (◇S^ newΔ) (ext-var (ext-S^ x))
extx-◇◇ (ext-S∙ ext) neq (S∙ inΓ) with extx-◇◇ ext (≢-pred neq) inΓ
... | justexts newΓ newΔ (ext-var x) = justexts (◇S∙ newΓ) (◇S∙ newΔ) (ext-var (ext-S∙ x))
extx-◇◇ (ext-S= ext) neq (S= inΓ) with extx-◇◇ ext (≢-pred neq) inΓ
... | justexts newΓ newΔ (ext-var x) = justexts (◇S= newΓ) (◇S= newΔ) (ext-var (ext-S= x))

ext-◆◇ : Γ ⊆ Δ w/t A
       → k ε A
       → Γ ∋^ k
       → ReExt◆◇ Γ Δ k A

ext-◆◇-derived : Γ ⊆ Δ w/t A
               → Γ ◇ k ⇘ Γ'
               → Δ ◆ k ⇘ Δ'
               → Γ' ⊆ Δ' w/t A
ext-◆◇-derived {k = k} ext newΓ newΔ with ext-◆◇ ext (^in-=out-ε ext (◇-∋^ newΓ) (◆-∋= newΔ)) (◇-∋^ newΓ)
... | justexts newΓ₁ newΔ₁ ext₁ rewrite ◆-unique newΔ newΔ₁ | ◇-unique newΓ newΓ₁ = ext₁

ext-◆◆ : Γ ⊆ Δ w/t A
       → Γ ∋= k
       → ReExt◆◆ Γ Δ k A

ext-◇◇ : Γ ⊆ Δ w/t A
       → k ¬ε A
       → Γ ∋^ k
       → ReExt◇◇ Γ Δ k A

ext-◆◇ (ext-var x) ε-var inΓ = extx-◆◇ x inΓ
ext-◆◇ (ext-arr ext ext₁) (ε-arr-l inA) inΓ with ext-◆◇ ext inA inΓ | ext-◆◆ ext₁ (ext-^in-=out ext inA inΓ)
... | justexts newΓ newΔ newext | justexts newΓ' newΔ' newext' rewrite ◆-unique newΔ newΓ' = justexts newΓ newΔ' (ext-arr newext newext')
ext-◆◇ {k = k} (ext-arr {A = A} ext ext₁) (ε-arr-r inA) inΓ with ε-dec {k = k} {A = A}
... | inj₁ inA'
  with justexts newΓ' newΔ' newext ← ext-◆◇ ext inA' inΓ
  with justexts newΓ'' newΔ'' newext' ← ext-◆◆ ext₁ (ext-^in-=out ext inA' inΓ)
  with refl ← ◆-unique newΓ'' newΔ' = justexts newΓ' newΔ'' (ext-arr newext newext')
... | inj₂ ¬inA'
  with justexts newΓ' newΔ' newext ← ext-◇◇ ext ¬inA' inΓ
  with justexts newΓ'' newΔ'' newext' ← ext-◆◇ ext₁ inA (ext-^in-^out ext ¬inA' inΓ)
  with refl ← ◇-unique newΔ' newΓ'' = justexts newΓ' newΔ'' (ext-arr newext newext')
ext-◆◇ (ext-∀ ext) (ε-∀ inA) inΓ with ext-◆◇ ext inA (S∙ inΓ)
... | justexts (◇S∙ newΓ) (◆S∙ newΔ) ext' = justexts newΓ newΔ (ext-∀ ext')

ext-◆◆ ext-int inΓ with ◆-total inΓ
... | ⟨ Γ' , newΓ ⟩ = justexts newΓ newΓ ext-int
ext-◆◆ (ext-var x) inΓ = extx-◆◆ x inΓ
ext-◆◆ (ext-arr ext ext₁) inΓ
  with justexts x x₁ x₂ ← ext-◆◆ ext inΓ
  with justexts x' x₁' x₂' ← ext-◆◆ ext₁ (ext-=in-=out ext inΓ)
  with refl ← ◆-unique x' x₁ = justexts x x₁' (ext-arr x₂ x₂')
ext-◆◆ (ext-∀ ext) inΓ with ext-◆◆ ext (S∙ inΓ)
... | justexts (◆S∙ x) (◆S∙ x₁) ext' = justexts x x₁ (ext-∀ ext')

ext-◇◇ ext-int ¬ε-int inΓ with ◇-total inΓ
... | ⟨ Γ' , newΓ ⟩ = justexts newΓ newΓ ext-int
ext-◇◇ (ext-var x) (¬ε-var x₁) inΓ = extx-◇◇ x x₁ inΓ
ext-◇◇ (ext-arr ext ext₁) (¬ε-arr ¬inA ¬inA₁) inΓ with ext-◇◇ ext ¬inA inΓ | ext-◇◇ ext₁ ¬inA₁ (ext-^in-^out ext ¬inA inΓ)
... | justexts newΓ newΔ ext₂ | justexts newΓ₁ newΔ₁ ext₃
  with refl ← ◇-unique newΔ newΓ₁ = justexts newΓ newΔ₁ (ext-arr ext₂ ext₃)
ext-◇◇ (ext-∀ ext) (¬ε-∀ ¬inA) inΓ with ext-◇◇ ext ¬inA (S∙ inΓ)
... | justexts (◇S∙ newΓ) (◇S∙ newΔ) ext₁ = justexts newΓ newΔ (ext-∀ ext₁)
