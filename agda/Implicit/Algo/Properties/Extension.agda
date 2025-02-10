module Implicit.Algo.Properties.Extension where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Subst
open import Implicit.Algo.Properties.OpenClose
open import Implicit.Algo.Properties.Polarity

inst-affect-one : [ A / X ] Γ ⟹ Δ
                → Γ ∋^ k
                → Δ ∋= k
                → k ≡ X
inst-affect-one (⟹^0 up) Z inΔ = refl
inst-affect-one (⟹^0 up) (S^ inΓ) (S= inΔ) = ⊥-elim (∋^-∋=-false inΓ inΔ)
inst-affect-one (⟹^S inst up1) (S^ inΓ) (S^ inΔ) = cong #S (inst-affect-one inst inΓ inΔ)
inst-affect-one (⟹∙S inst up1) (S∙ inΓ) (S∙ inΔ) = cong #S (inst-affect-one inst inΓ inΔ)
inst-affect-one (⟹,S inst) (S, inΓ) (S, inΔ) = inst-affect-one inst inΓ inΔ
inst-affect-one (⟹=S inst up1) (S= inΓ) (S= inΔ) = cong #S (inst-affect-one inst inΓ inΔ)

data ExSol (Γ : Env n m) (k : Fin m) : Set where
  is-ex  : (inΓ : Γ ∋^ k) → ExSol Γ k
  is-sol : (inΓ : Γ ∋= k) → ExSol Γ k

s-⊆-exsol : Γ ⊆ Δ
          → Γ ∋^ k
          → ExSol Δ k
s-⊆-exsol (uvar ext) (S∙ inΓ) with s-⊆-exsol ext inΓ
... | is-ex x = is-ex (S∙ x)
... | is-sol x = is-sol (S∙ x)
s-⊆-exsol (var ext) (S, inΓ) with s-⊆-exsol ext inΓ
... | is-ex x = is-ex (S, x)
... | is-sol x = is-sol (S, x)
s-⊆-exsol (evar ext) Z = is-ex Z
s-⊆-exsol (evar ext) (S^ inΓ) with s-⊆-exsol ext inΓ
... | is-ex x = is-ex (S^ x)
... | is-sol x = is-sol (S^ x)
s-⊆-exsol (evar-sol ext cloA) Z = is-sol Z
s-⊆-exsol (evar-sol ext cloA) (S^ inΓ) with s-⊆-exsol ext inΓ
... | is-ex x = is-ex (S= x)
... | is-sol x = is-sol (S= x)
s-⊆-exsol (svar ext) (S= inΓ) with s-⊆-exsol ext inΓ
... | is-ex x = is-ex (S= x)
... | is-sol x = is-sol (S= x)

-- a more restricted extending

infix 3 _⊆_w/v_
data _⊆_w/v_ : Env n m → Env n m → Fin m → Set where
  ext-Z^ : (cloA : Γ ⊢c A)
         → Γ ,^ ⊆ Γ ,= A w/v #0
  ext-Z∙ : Γ ,∙ ⊆ Γ ,∙ w/v #0
  ext-Z= : Γ ,= A ⊆ Γ ,= A w/v #0
  ext-S, : Γ ⊆ Δ w/v k
         → Γ , A ⊆ Δ , A w/v k
  ext-S^ : Γ ⊆ Δ w/v k
         → Γ ,^ ⊆ Δ ,^ w/v #S k
  ext-S∙ : Γ ⊆ Δ w/v k
         → Γ ,∙ ⊆ Δ ,∙ w/v #S k
  ext-S= : Γ ⊆ Δ w/v k
         → Γ ,= A ⊆ Δ ,= A w/v #S k

infix 3 _⊆_w/t_
data _⊆_w/t_ : Env n m → Env n m → Type m → Set where
  ext-int : Γ ⊆ Γ w/t Int
  ext-var : Γ ⊆ Δ w/v X
          → Γ ⊆ Δ w/t ‶ X
  ext-arr : Γ ⊆ Ω w/t A
          → Ω ⊆ Δ w/t B
          → Γ ⊆ Δ w/t A `→ B
  ext-∀   : Γ ,∙ ⊆ Δ ,∙ w/t A
          → Γ ⊆ Δ w/t `∀ A




env-◆◇-false : Γ ◇ k ⇘ Γ₁
             → Γ ◆ k ⇘ Γ₂
             → ⊥
env-◆◇-false (◇S, newΓ1) (◆S, newΓ2) = env-◆◇-false newΓ1 newΓ2
env-◆◇-false (◇S∙ newΓ1) (◆S∙ newΓ2) = env-◆◇-false newΓ1 newΓ2
env-◆◇-false (◇S= newΓ1) (◆S= newΓ2) = env-◆◇-false newΓ1 newΓ2
env-◆◇-false (◇S^ newΓ1) (◆S^ newΓ2) = env-◆◇-false newΓ1 newΓ2

ε-dec : (k ε A) ⊎ (k ¬ε A)
ε-dec {k = k} {A = Int} = inj₂ ¬ε-int
ε-dec {k = k} {A = ‶ X} with k #≟ X
... | yes refl = inj₁ ε-var
... | no ¬p = inj₂ (¬ε-var (≢-sym ¬p))
ε-dec {k = k} {A = A `→ B} with ε-dec {k = k} {A = A} | ε-dec {k = k} {A = B}
... | inj₁ p | _ = inj₁ (ε-arr-l p)
... | _ | inj₁ p = inj₁ (ε-arr-r p)
... | inj₂ p | inj₂ p' = inj₂ (¬ε-arr p p')
ε-dec {k = k} {A = `∀ A} with ε-dec {k = #S k} {A = A}
... | inj₁ p = inj₁ (ε-∀ p)
... | inj₂ p = inj₂ (¬ε-∀ p)


extx-^in-=out : Γ ⊆ Δ w/v k
              → Γ ∋^ k
              → Δ ∋= k
extx-^in-=out (ext-Z^ cloA) Z = Z
extx-^in-=out (ext-S, ext) (S, inΓ) = S, (extx-^in-=out ext inΓ)
extx-^in-=out (ext-S^ ext) (S^ inΓ) = S^ (extx-^in-=out ext inΓ)
extx-^in-=out (ext-S∙ ext) (S∙ inΓ) = S∙ (extx-^in-=out ext inΓ)
extx-^in-=out (ext-S= ext) (S= inΓ) = S= (extx-^in-=out ext inΓ)

extx-^in-^out : Γ ⊆ Δ w/v X
              → X ≢ k
              → Γ ∋^ k
              → Δ ∋^ k
extx-^in-^out (ext-Z^ cloA) neq Z = ⊥-elim (neq refl)
extx-^in-^out (ext-Z^ cloA) neq (S^ inΓ) = S= inΓ
extx-^in-^out ext-Z∙ neq inΓ = inΓ
extx-^in-^out ext-Z= neq inΓ = inΓ
extx-^in-^out (ext-S, ext) neq (S, inΓ) = S, (extx-^in-^out ext neq inΓ)
extx-^in-^out (ext-S^ ext) neq Z = Z
extx-^in-^out (ext-S^ ext) neq (S^ inΓ) = S^ (extx-^in-^out ext (≢-pred neq) inΓ)
extx-^in-^out (ext-S∙ ext) neq (S∙ inΓ) = S∙ (extx-^in-^out ext (≢-pred neq) inΓ)
extx-^in-^out (ext-S= ext) neq (S= inΓ) = S= (extx-^in-^out ext (≢-pred neq) inΓ)

extx-=in-=out : Γ ⊆ Δ w/v X
              → Γ ∋= k
              → Δ ∋= k
extx-=in-=out (ext-Z^ cloA) (S^ inΓ) = S= inΓ
extx-=in-=out ext-Z∙ inΓ = inΓ
extx-=in-=out ext-Z= inΓ = inΓ
extx-=in-=out (ext-S, extx) (S, inΓ) = S, (extx-=in-=out extx inΓ)
extx-=in-=out (ext-S^ extx) (S^ inΓ) = S^ (extx-=in-=out extx inΓ)
extx-=in-=out (ext-S∙ extx) (S∙ inΓ) = S∙ (extx-=in-=out extx inΓ)
extx-=in-=out (ext-S= extx) Z = Z
extx-=in-=out (ext-S= extx) (S= inΓ) = S= (extx-=in-=out extx inΓ)

ext-^in-=out : Γ ⊆ Δ w/t A
             → k ε A
             → Γ ∋^ k
             → Δ ∋= k

ext-^in-^out : Γ ⊆ Δ w/t A
             → k ¬ε A
             → Γ ∋^ k
             → Δ ∋^ k

ext-=in-=out : Γ ⊆ Δ w/t A
             → Γ ∋= k
             → Δ ∋= k

ext-^in-=out (ext-var x) ε-var inΓ = extx-^in-=out x inΓ
ext-^in-=out (ext-arr ext ext₁) (ε-arr-l inA) inΓ = ext-=in-=out ext₁ (ext-^in-=out ext inA inΓ)
ext-^in-=out {A = A `→ B} {k = k} (ext-arr ext ext₁) (ε-arr-r inA) inΓ with ε-dec {k = k} {A = A}
... | inj₁ init = ext-=in-=out ext₁ (ext-^in-=out ext init inΓ)
... | inj₂ nint = ext-^in-=out ext₁ inA (ext-^in-^out ext nint inΓ)
ext-^in-=out (ext-∀ ext) (ε-∀ inA) inΓ with ext-^in-=out ext inA (S∙ inΓ)
... | S∙ r = r

ext-^in-^out ext-int ninA inΓ = inΓ
ext-^in-^out (ext-var x) (¬ε-var x₁) inΓ = extx-^in-^out x x₁ inΓ
ext-^in-^out (ext-arr ext ext₁) (¬ε-arr ninA ninA₁) inΓ = ext-^in-^out ext₁ ninA₁ (ext-^in-^out ext ninA inΓ)
ext-^in-^out (ext-∀ ext) (¬ε-∀ ninA) inΓ with ext-^in-^out ext ninA (S∙ inΓ)
... | S∙ r = r

ext-=in-=out ext-int inΓ = inΓ
ext-=in-=out (ext-var x) inΓ = extx-=in-=out x inΓ
ext-=in-=out (ext-arr ext ext₁) inΓ = ext-=in-=out ext₁ (ext-=in-=out ext inΓ)
ext-=in-=out (ext-∀ ext) inΓ with ext-=in-=out ext (S∙ inΓ)
... | S∙ r = r


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

extx-^in-=out-eq : Γ ⊆ Δ w/v X
                 → Γ ∋^ k
                 → Δ ∋= k
                 → k ≡ X
extx-^in-=out-eq (ext-Z^ cloA) Z inΔ = refl
extx-^in-=out-eq (ext-Z^ cloA) (S^ inΓ) (S= inΔ) = ⊥-elim (∋^-∋=-false inΓ inΔ)
extx-^in-=out-eq ext-Z∙ inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
extx-^in-=out-eq ext-Z= inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
extx-^in-=out-eq (ext-S, ext) (S, inΓ) (S, inΔ) = extx-^in-=out-eq ext inΓ inΔ
extx-^in-=out-eq (ext-S^ ext) (S^ inΓ) (S^ inΔ) = cong #S (extx-^in-=out-eq ext inΓ inΔ)
extx-^in-=out-eq (ext-S∙ ext) (S∙ inΓ) (S∙ inΔ) = cong #S (extx-^in-=out-eq ext inΓ inΔ)
extx-^in-=out-eq (ext-S= ext) (S= inΓ) (S= inΔ) = cong #S (extx-^in-=out-eq ext inΓ inΔ)

⊆/x-exsol : Γ ⊆ Δ w/v X
          → Γ ∋^ k
          → ExSol Δ k
⊆/x-exsol (ext-Z^ cloA) Z = is-sol Z
⊆/x-exsol (ext-Z^ cloA) (S^ inΓ) = is-ex (S= inΓ)
⊆/x-exsol ext-Z∙ (S∙ inΓ) = is-ex (S∙ inΓ)
⊆/x-exsol ext-Z= (S= inΓ) = is-ex (S= inΓ)
⊆/x-exsol (ext-S, ext) (S, inΓ) with ⊆/x-exsol ext inΓ
... | is-ex inΓ₁ = is-ex (S, inΓ₁)
... | is-sol inΓ₁ = is-sol (S, inΓ₁)
⊆/x-exsol (ext-S^ ext) Z = is-ex Z
⊆/x-exsol (ext-S^ ext) (S^ inΓ) with ⊆/x-exsol ext inΓ
... | is-ex inΓ₁ = is-ex (S^ inΓ₁)
... | is-sol inΓ₁ = is-sol (S^ inΓ₁)
⊆/x-exsol (ext-S∙ ext) (S∙ inΓ) with ⊆/x-exsol ext inΓ
... | is-ex inΓ₁ = is-ex (S∙ inΓ₁)
... | is-sol inΓ₁ = is-sol (S∙ inΓ₁)
⊆/x-exsol (ext-S= ext) (S= inΓ) with ⊆/x-exsol ext inΓ
... | is-ex inΓ₁ = is-ex (S= inΓ₁)
... | is-sol inΓ₁ = is-sol (S= inΓ₁)

⊆/-exsol : Γ ⊆ Δ w/t A
         → Γ ∋^ k
         → ExSol Δ k
⊆/-exsol ext-int inΓ = is-ex inΓ
⊆/-exsol (ext-var x) inΓ = ⊆/x-exsol x inΓ
⊆/-exsol (ext-arr ext ext₁) inΓ with ⊆/-exsol ext inΓ
... | is-ex inΓ₁ with ⊆/-exsol ext₁ inΓ₁
... | is-ex inΓ₂ = is-ex inΓ₂
... | is-sol inΓ₂ = is-sol inΓ₂
⊆/-exsol (ext-arr ext ext₁) inΓ | is-sol inΓ₁ = is-sol (ext-=in-=out ext₁ inΓ₁)
⊆/-exsol (ext-∀ ext) inΓ with ⊆/-exsol ext (S∙ inΓ)
... | is-ex (S∙ inΓ₁) = is-ex inΓ₁
... | is-sol (S∙ inΓ₁) = is-sol inΓ₁

^in-=out-ε : Γ ⊆ Δ w/t A
           → Γ ∋^ k
           → Δ ∋= k
           → k ε A
^in-=out-ε ext-int inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
^in-=out-ε (ext-var x) inΓ inΔ with extx-^in-=out-eq x inΓ inΔ
... | refl = ε-var
^in-=out-ε (ext-arr ext ext₁) inΓ inΔ with ⊆/-exsol ext inΓ
... | is-ex inΓ₁ = ε-arr-r (^in-=out-ε ext₁ inΓ₁ inΔ)
... | is-sol inΓ₁ = ε-arr-l (^in-=out-ε ext inΓ inΓ₁)
^in-=out-ε (ext-∀ ext) inΓ inΔ = ε-∀ (^in-=out-ε ext (S∙ inΓ) (S∙ inΔ))

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

extv-∙-eq : Γ ∋∙ X
          → Γ ⊆ Δ w/v X
          → Γ ≡ Δ
extv-∙-eq Z ext-Z∙ = refl
extv-∙-eq (S, inΓ) (ext-S, ext) rewrite extv-∙-eq inΓ ext = refl
extv-∙-eq (S∙ inΓ) (ext-S∙ ext) rewrite extv-∙-eq inΓ ext = refl
extv-∙-eq (S= inΓ) (ext-S= ext) rewrite extv-∙-eq inΓ ext = refl
extv-∙-eq (S^ inΓ) (ext-S^ ext) rewrite extv-∙-eq inΓ ext = refl

extv-∙ : Γ ∋∙ X
       → Γ ⊆ Γ w/v X
extv-∙ Z = ext-Z∙
extv-∙ (S, inΓ) = ext-S, (extv-∙ inΓ)
extv-∙ (S∙ inΓ) = ext-S∙ (extv-∙ inΓ)
extv-∙ (S= inΓ) = ext-S= (extv-∙ inΓ)
extv-∙ (S^ inΓ) = ext-S^ (extv-∙ inΓ)

extv-=-eq : Γ ∋= X
          → Γ ⊆ Δ w/v X
          → Γ ≡ Δ
extv-=-eq Z ext-Z= = refl
extv-=-eq (S, inΓ) (ext-S, ext) rewrite extv-=-eq inΓ ext = refl
extv-=-eq (S∙ inΓ) (ext-S∙ ext) rewrite extv-=-eq inΓ ext = refl
extv-=-eq (S= inΓ) (ext-S= ext) rewrite extv-=-eq inΓ ext = refl
extv-=-eq (S^ inΓ) (ext-S^ ext) rewrite extv-=-eq inΓ ext = refl

extv-= : Γ ∋= X
       → Γ ⊆ Γ w/v X
extv-= Z = ext-Z=
extv-= (S, inΓ) = ext-S, (extv-= inΓ)
extv-= (S∙ inΓ) = ext-S∙ (extv-= inΓ)
extv-= (S^ inΓ) = ext-S^ (extv-= inΓ)
extv-= (S= inΓ) = ext-S= (extv-= inΓ)

ext-close-eq : Γ ⊢c A
             → Γ ⊆ Δ w/t A
             → Γ ≡ Δ
ext-close-eq ⊢c-int ext-int = refl
ext-close-eq (⊢c-var-∙ inΓ) (ext-var x) = extv-∙-eq inΓ x
ext-close-eq (⊢c-var-= inΓ) (ext-var x) = extv-=-eq inΓ x
ext-close-eq (⊢c-arr cloA cloA₁) (ext-arr ext ext₁) with ext-close-eq cloA ext
... | refl = ext-close-eq cloA₁ ext₁
ext-close-eq (⊢c-∀ cloA) (ext-∀ ext) with ext-close-eq cloA ext
... | refl = refl

ext-close : Γ ⊢c A
           → Γ ⊆ Γ w/t A
ext-close ⊢c-int = ext-int
ext-close (⊢c-var-∙ inΓ) = ext-var (extv-∙ inΓ)
ext-close (⊢c-var-= inΓ) = ext-var (extv-= inΓ)
ext-close (⊢c-arr cloA cloA₁) = ext-arr (ext-close cloA) (ext-close cloA₁)
ext-close (⊢c-∀ cloA) = ext-∀ (ext-close cloA)

inst-extv : [ A / X ] Γ ⟹ Δ
         → Γ ⊢c A
         → Γ ⊆ Δ w/v X
inst-extv (⟹^0 up) cloA = ext-Z^ (⊢c-strengthen^0 cloA up)
inst-extv (⟹^S inst up1) cloA = ext-S^ (inst-extv inst (⊢c-strengthen^0 cloA up1))
inst-extv (⟹∙S inst up1) cloA = ext-S∙ (inst-extv inst (⊢c-strengthen∙0 cloA up1))
inst-extv (⟹,S inst) cloA = ext-S, (inst-extv inst (⊢c-strengthen,0 cloA))
inst-extv (⟹=S inst up1) cloA = ext-S= (inst-extv inst (⊢c-strengthen=0 cloA up1))

s-extend-l : Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Δ ↪ B
           → Closed Γ
           → Γ ⊢cᶜ Σ
           → Γ ⊆ Δ w/t A

s-extend-r : Γ ⊢ A ⌞ ≤⁻ ⌝ (τ B) ⊣ Δ ↪ C
           → Closed Γ
           → Γ ⊢c A
           → Γ ⊆ Δ w/t B

s-all-closed : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
             → Closed Γ
             → Γ ⊢c A
             → Γ ⊢cᶜ Σ
             → Γ ≡ Δ
s-all-closed {≤ = ≤⁺} s cloΓ cloA cloΣ with s-extend-l s cloΓ cloΣ
... | ext = ext-close-eq cloA ext
s-all-closed {≤ = ≤⁻} {τ A} s cloΓ cloA (⊢c-τ cloA₁) with s-extend-r s cloΓ cloA
... | ext = ext-close-eq cloA₁ ext

s-extend-l s-int cloΓ cloΣ = ext-int
s-extend-l (s-empty clo) cloΓ cloΣ = ext-close clo
s-extend-l s-var cloΓ (⊢c-τ cloA) = ext-close cloA
s-extend-l (s-ex-l^ x-in inst) cloΓ (⊢c-τ cloA) = ext-var (inst-extv inst cloA)
s-extend-l (s-ex-l= x-in s) cloΓ cloΣ with s-all-closed s cloΓ (∋=-closed cloΓ x-in) cloΣ
... | refl = ext-var (extv-= (∋:=to∋= x-in))
s-extend-l (s-ex-r= x-in s) cloΓ (⊢c-τ cloA) = s-extend-l s cloΓ (⊢c-τ (∋=-closed cloΓ x-in))
s-extend-l (s-arr s s₁) cloΓ (⊢c-τ (⊢c-arr cloA cloA₁)) with s-extend-r s cloΓ cloA
                        | s-extend-l s₁ (s-closed-env s (polar-l cloΓ cloA)) (⊢c-τ (⊆-cloA cloA₁ (s-⊆ s (polar-l cloΓ cloA))))
... | r1 | r2 = ext-arr r1 r2
s-extend-l (s-term-c ⊢e s) cloΓ (⊢c-term cloe cloΣ) = ext-arr (ext-close (⊢close-τ ⊢e)) (s-extend-l s cloΓ cloΣ)
s-extend-l (s-term-o opnA ⊢e s s₁) cloΓ (⊢c-term cloe cloΣ) = let cloC = ⊢closeA ⊢e
                                                                  ext = s-⊆ s (polar-l cloΓ cloC)
  in ext-arr (s-extend-r s cloΓ cloC) (s-extend-l s₁ (s-closed-env s (polar-l cloΓ cloC)) (⊆-cloAᶜ cloΣ ext))
s-extend-l (s-∀ s) cloΓ (⊢c-τ (⊢c-∀ cloA)) = ext-∀ (s-extend-l s (clo-S∙ cloΓ) (⊢c-τ cloA))
s-extend-l (s-∀l s upᶜ upᵉ st₁ st₂) cloΓ cloΣ with s-extend-l s (clo-S^ cloΓ) (⊢cᶜ-weaken^0 cloΣ (↑tyᶜ-e upᵉ upᶜ))
... | r = ext-∀ (helper r)
  where helper : Γ ,^ ⊆ Δ ,= B w/t A → Γ ,∙ ⊆ Δ ,∙ w/t A
        helper ext = ext-◆◇-derived ext ◇Z ◆Z

s-extend-r s-int cloΓ cloA = ext-int
s-extend-r s-var cloΓ cloA = ext-close cloA
s-extend-r (s-ex-l= x-in s) cloΓ cloA = s-extend-r s cloΓ (∋=-closed cloΓ x-in)
s-extend-r (s-ex-r^ x-in inst) cloΓ cloA = ext-var (inst-extv inst cloA)
s-extend-r (s-ex-r= x-in s) cloΓ cloA with s-all-closed s cloΓ cloA (⊢c-τ (∋=-closed cloΓ x-in))
... | refl = ext-var (extv-= (∋:=to∋= x-in))
s-extend-r (s-arr s s₁) cloΓ (⊢c-arr cloA cloA₁) = ext-arr (s-extend-l s cloΓ (⊢c-τ cloA))
  (s-extend-r s₁ (s-closed-env s (polar-r cloΓ (⊢c-τ cloA))) (⊆-cloA cloA₁ (s-⊆ s (polar-r cloΓ (⊢c-τ cloA)))))
s-extend-r (s-∀ s) cloΓ (⊢c-∀ cloA) = ext-∀ (s-extend-r s (clo-S∙ cloΓ) cloA)
