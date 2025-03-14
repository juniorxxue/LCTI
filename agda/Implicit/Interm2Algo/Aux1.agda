module Implicit.Interm2Algo.Aux1 where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm.Base

----------------------------------------------------------------------
--+                         env extension                          +--
----------------------------------------------------------------------



----------------------------------------------------------------------
--+                       counter to context                       +--
----------------------------------------------------------------------

infix 3 _⊢_~s_
data _⊢_~s_ : Env n m → Counter × Type m → Context n m → Set where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~s □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~s τ A

  ~I : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : 𝕣 Γ ⊢ □ ⇒ e ⇒ A)
--    → Γ ⊆ Ω w/t A
    → Γ ⊢ ⟨ j , B ⟩ ~s Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ~s ([ e ]↝ Σ)

  ~C : ∀ {Γ : Env n m} {j B Σ e}
    → (⊢e : 𝕣 Γ ⊢ τ A% ⇒ e ⇒ A%)
    → Γ ⊢ ⟨ j , B ⟩ ~s Σ
    → Γ ⊢ ⟨ 𝕔 j , A% `→ B ⟩ ~s ([ e ]↝ Σ)

infix 3 _⊢_~t_
data _⊢_~t_ : Env n m → Counter × Type m → Context n m → Set where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~t □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~t τ A

  ~I : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ □ ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~t Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ~t ([ e ]↝ Σ)

  ~C : ∀ {Γ : Env n m} {j B Σ e}
    → (⊢e : Γ ⊢ τ A% ⇒ e ⇒ A%)
    → Γ ⊢ ⟨ j , B ⟩ ~t Σ
    → Γ ⊢ ⟨ 𝕔 j , A% `→ B ⟩ ~t ([ e ]↝ Σ)


~weaken,0 : Γ ⊢ ⟨ j , B ⟩ ~t Σ
          → ↑tmᶜ0 Σ ⇘ Σ'
          → Γ , A ⊢ ⟨ j , B ⟩ ~t Σ'
~weaken,0 ~Z ↑tmᶜ-□ = ~Z
~weaken,0 ~∞ ↑tmᶜ-τ = ~∞
~weaken,0 (~I ⊢e j~Σ) (↑tmᶜ-e up-e upΣ) = ~I (t-weaken,0 ⊢e ↑tmᶜ-□ up-e) (~weaken,0 j~Σ upΣ)
~weaken,0 (~C ⊢e j~Σ) (↑tmᶜ-e up-e upΣ) = ~C (t-weaken,0 ⊢e ↑tmᶜ-τ up-e) (~weaken,0 j~Σ upΣ)

~weaken^0 : Γ ⊢ ⟨ j , A ⟩ ~s Σ
          → ↑ty0 A ⇘ A'
          → ↑tyᶜ0 Σ ⇘ Σ'
          → Γ ,^ ⊢ ⟨ j , A' ⟩ ~s Σ'
~weaken^0 ~Z upA ↑tyᶜ-□ = ~Z
~weaken^0 ~∞ upA (↑tyᶜ-τ up-t) with refl ← ↑ty-unique upA up-t = ~∞
~weaken^0 (~I ⊢e ~j) (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) = ~I (t-weaken^0 ⊢e ↑tyᶜ-□ up-e upA) (~weaken^0 ~j upA₁ upΣ)
~weaken^0 (~C ⊢e ~j) (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) = ~C (t-weaken^0 ⊢e (↑tyᶜ-τ upA) up-e upA) (~weaken^0 ~j upA₁ upΣ)

~t-~s : Γ ⊢ ⟨ j , B ⟩ ~t Σ
      → Γ ⋈ ⊢ ⟨ j , B ⟩ ~s Σ
~t-~s ~Z = ~Z
~t-~s ~∞ = ~∞
~t-~s (~I ⊢e j~Σ) = ~I ⊢e (~t-~s j~Σ)
~t-~s (~C ⊢e j~Σ) = ~C ⊢e (~t-~s j~Σ)

----------------------------------------------------------------------
--+                       env extension diff                       +--
----------------------------------------------------------------------

-- use for proving the arrow case

-- we know that Ω ⊆ Δ
-- and Γ ⊆ Ω, this relation should imply this property

-- Δ ⅆ Ω ≋ Ψ ⅆ Γ
infix 3 _ⅆ_≋_ⅆ_

data _ⅆ_≋_ⅆ_ : Env n m → Env n m → Env n m → Env n m → Set where
  ⅆ⋈ : (regΓ : TRegular Γ)
     → Γ ⋈ ⅆ Γ ⋈ ≋ Γ ⋈ ⅆ Γ ⋈
  ⅆS∙ : Δ ⅆ Ω ≋ Ψ ⅆ Γ
      → Δ ,∙ ⅆ Ω ,∙  ≋ Ψ ,∙ ⅆ Γ ,∙
  ⅆS^ : Δ ⅆ Ω ≋ Ψ ⅆ Γ
      → Δ ,^ ⅆ Ω ,^  ≋ Ψ ,^ ⅆ Γ ,^
  ⅆS=^ : Δ ⅆ Ω ≋ Ψ ⅆ Γ
       → (regA : Δ ⊢r A)
       → Δ ,= A ⅆ Ω ,^  ≋ Ψ ,= A ⅆ Γ ,^
  ⅆS==1 : Δ ⅆ Ω ≋ Ψ ⅆ Γ
        → (regA : Δ ⊢r A)
      → Δ ,= A ⅆ Ω ,= A  ≋ Ψ ,= A ⅆ Γ ,= A
  ⅆS==2 : Δ ⅆ Ω ≋ Ψ ⅆ Γ
        → (regA : Δ ⊢r A)
      → Δ ,= A ⅆ Ω ,= A  ≋ Ψ ,^ ⅆ Γ ,^

ⅆ-total : Γ ⊆ Ω
        → Ω ⊆ Δ
        → ∃[ Ψ ](Δ ⅆ Ω ≋ Ψ ⅆ Γ)
ⅆ-total (uvar ext1) (uvar ext2) = ⟨ ⅆ-total ext1 ext2 .proj₁ ,∙ , ⅆS∙ (ⅆ-total ext1 ext2 .proj₂) ⟩
ⅆ-total (evar ext1) (evar ext2) = ⟨ ⅆ-total ext1 ext2 .proj₁ ,^ , ⅆS^ (ⅆ-total ext1 ext2 .proj₂) ⟩
ⅆ-total (evar ext1) (evar-sol {A = A} ext2 regA) = ⟨ ⅆ-total ext1 ext2 .proj₁ ,= A , ⅆS=^ (ⅆ-total ext1 ext2 .proj₂) regA ⟩
ⅆ-total (evar-sol ext1 regA) (svar ext2 regA₁) = ⟨ ⅆ-total ext1 ext2 .proj₁ ,^ , ⅆS==2 (ⅆ-total ext1 ext2 .proj₂) (⊆-⊢r regA ext2) ⟩
ⅆ-total (svar ext1 regA) (svar {A = A} ext2 regA₁) = ⟨ ⅆ-total ext1 ext2 .proj₁ ,= A , ⅆS==1 (ⅆ-total ext1 ext2 .proj₂) (⊆-⊢r regA₁ ext2) ⟩
ⅆ-total (mark {Γ = Γ} x) (mark x₁) = ⟨ Γ ⋈ , ⅆ⋈ x ⟩


ⅆ-⊆ : Δ ⅆ Ω ≋ Ψ ⅆ Γ
    → Ψ ⊆ Δ
ⅆ-⊆ (ⅆ⋈ regΓ) = mark regΓ
ⅆ-⊆ (ⅆS∙ ext) = uvar (ⅆ-⊆ ext)
ⅆ-⊆ (ⅆS^ ext) = evar (ⅆ-⊆ ext)
ⅆ-⊆ (ⅆS=^ ext regA) with ⅆ-⊆ ext
... | ih = svar ih (⊆-⊢r' regA ih)
ⅆ-⊆ (ⅆS==1 ext regA) = svar (ⅆ-⊆ ext) (⊆-⊢r' regA (ⅆ-⊆ ext))
ⅆ-⊆ (ⅆS==2 ext regA) = evar-sol (ⅆ-⊆ ext) regA

ⅆ-l-⊆ : Δ ⅆ Ω ≋ Ψ ⅆ Γ
      → Ω ⊆ Δ
ⅆ-l-⊆ (ⅆ⋈ x) = mark x
ⅆ-l-⊆ (ⅆS∙ dd) = uvar (ⅆ-l-⊆ dd)
ⅆ-l-⊆ (ⅆS^ dd) = evar (ⅆ-l-⊆ dd)
ⅆ-l-⊆ (ⅆS=^ dd regA) = evar-sol (ⅆ-l-⊆ dd) regA
ⅆ-l-⊆ (ⅆS==1 dd regA) = svar (ⅆ-l-⊆ dd) (⊆-⊢r' regA (ⅆ-l-⊆ dd))
ⅆ-l-⊆ (ⅆS==2 dd regA) = svar (ⅆ-l-⊆ dd) (⊆-⊢r' regA (ⅆ-l-⊆ dd))

ⅆ-r-⊆ : Δ ⅆ Ω ≋ Ψ ⅆ Γ
      → Γ ⊆ Ψ
ⅆ-r-⊆ (ⅆ⋈ regΓ) = mark regΓ
ⅆ-r-⊆ (ⅆS∙ dd) = uvar (ⅆ-r-⊆ dd)
ⅆ-r-⊆ (ⅆS^ dd) = evar (ⅆ-r-⊆ dd)
ⅆ-r-⊆ (ⅆS=^ dd regA) = evar-sol (ⅆ-r-⊆ dd) (⊆-⊢r' regA (ⅆ-⊆ dd))
ⅆ-r-⊆ (ⅆS==1 dd regA) = svar (ⅆ-r-⊆ dd) (⊆-⊢r' regA (⊆-trans (ⅆ-r-⊆ dd) (ⅆ-⊆ dd)))
ⅆ-r-⊆ (ⅆS==2 dd regA) = evar (ⅆ-r-⊆ dd)
{-
ⅆ-unique : Ψ ⅆ Ω ≋ Ψ ⅆ Γ
         → Ω ≡ Γ
ⅆ-unique (ⅆ⋈ x) = refl
ⅆ-unique (ⅆS∙ dd) = cong _,∙ (ⅆ-unique dd)
ⅆ-unique (ⅆS^ dd) = cong _,^ (ⅆ-unique dd)
ⅆ-unique (ⅆS=^ dd regA) = cong _,^ (ⅆ-unique dd)
ⅆ-unique (ⅆS==1 dd regA) = cong₂ _,=_ (ⅆ-unique dd) refl
-}

ⅆ-out-eq : Δ ⅆ Ω ≋ Ψ ⅆ Ω
         → Δ ≡ Ψ
ⅆ-out-eq (ⅆ⋈ regΓ) = refl
ⅆ-out-eq (ⅆS∙ dd) rewrite ⅆ-out-eq dd = refl
ⅆ-out-eq (ⅆS^ dd) rewrite ⅆ-out-eq dd = refl
ⅆ-out-eq (ⅆS=^ dd regA) rewrite ⅆ-out-eq dd = refl
ⅆ-out-eq (ⅆS==1 dd regA) rewrite ⅆ-out-eq dd = refl

----------------------------------------------------------------------
--+                             Irrev                              +--
----------------------------------------------------------------------

~irrev : Γ ⊢ ⟨ j , D ⟩ ~s Σ
        → Γ ⊆ Ω
        → Ω ⊢ ⟨ j , D ⟩ ~s Σ
~irrev ~Z ext = ~Z
~irrev ~∞ ext = ~∞
~irrev (~I ⊢e ~j) ext = ~I (t-irrev-⊆ ⊢e ext) (~irrev ~j ext)
~irrev (~C ⊢e ~j) ext = ~C (t-irrev-⊆ ⊢e ext) (~irrev ~j ext)

{-
ⅆ-inst : Δ ⅆ Ω ≋ Ψ ⅆ Γ
       → [ B / X ] Ψ ⟹ Δ
       → [ B / X ] Γ ⟹ Ω
ⅆ-inst (ⅆS∙ dd) (⟹∙S inst up1) = ⟹∙S (ⅆ-inst dd inst) up1
ⅆ-inst (ⅆS^ dd) (⟹^S inst up1) = ⟹^S (ⅆ-inst dd inst) up1
ⅆ-inst (ⅆS=^ dd regA) (⟹=S inst up1 regB) = ⟹^S (ⅆ-inst dd inst) up1
ⅆ-inst (ⅆS==1 dd regA) (⟹=S inst up1 regB) = ⟹=S (ⅆ-inst dd inst) up1 (⊆-⊢r' regB (ⅆ-r-⊆ dd))
ⅆ-inst (ⅆS==2 dd regA) (⟹^0 up regA₁ env) with refl ← ⅆ-unique dd = ⟹^0 up (⊆-⊢r' regA (ⅆ-l-⊆ dd)) (⊆-regular' env (ⅆ-r-⊆ dd))
-}


ⅆ-total-mid : Δ ⅆ Δ' ≋ Γ ⅆ Γ'
            → Γ' ⊆ Ω'
            → Ω' ⊆ Δ'
            → ∃[ Ω ](Ω ⅆ Ω' ≋ Γ ⅆ Γ'
                   × Δ ⅆ Δ' ≋ Ω ⅆ Ω')
ⅆ-total-mid (ⅆ⋈ {Γ = Γ} regΓ) (mark regΓ₁) (mark regΓ₂) = ⟨ Γ ⋈ , ⟨ ⅆ⋈ regΓ , ⅆ⋈ regΓ₂ ⟩ ⟩
ⅆ-total-mid (ⅆS∙ dd) (uvar ext1) (uvar ext2) = ⟨ ⅆ-total-mid dd ext1 ext2 .proj₁ ,∙ ,
                                                ⟨ ⅆS∙ (ⅆ-total-mid dd ext1 ext2 .proj₂ .proj₁) ,
                                                ⅆS∙ (ⅆ-total-mid dd ext1 ext2 .proj₂ .proj₂) ⟩
                                                ⟩
ⅆ-total-mid (ⅆS^ dd) (evar ext1) (evar ext2) = ⟨ ⅆ-total-mid dd ext1 ext2 .proj₁ ,^ ,
                                                ⟨ ⅆS^ (ⅆ-total-mid dd ext1 ext2 .proj₂ .proj₁) ,
                                                ⅆS^ (ⅆ-total-mid dd ext1 ext2 .proj₂ .proj₂) ⟩
                                                ⟩
ⅆ-total-mid (ⅆS=^ {A = A} dd regA) (evar ext1) (evar ext2) with ⅆ-total-mid dd ext1 ext2
... | ⟨ Ω , ⟨ dd1 , dd2 ⟩ ⟩ = ⟨ (Ω ,= A) , ⟨ ⅆS=^ dd1 (⊆-⊢r' regA (ⅆ-⊆ dd2)) , ⅆS=^ dd2 regA ⟩ ⟩
ⅆ-total-mid (ⅆS==1 {A = A} dd regA) (svar ext1 regA₁) (svar ext2 regA₂) with ⅆ-total-mid dd ext1 ext2
... | ⟨ Ω , ⟨ dd1 , dd2 ⟩ ⟩ = ⟨ (Ω ,= A) , ⟨ ⅆS==1 dd1 (⊆-⊢r regA₂ (ⅆ-l-⊆ dd1)) , ⅆS==1 dd2 regA ⟩ ⟩
ⅆ-total-mid (ⅆS==2 dd regA) (evar ext1) (evar-sol ext2 regA₁) = ⟨ ⅆ-total-mid dd ext1 ext2 .proj₁ ,^ ,
                                                                 ⟨ ⅆS^ (ⅆ-total-mid dd ext1 ext2 .proj₂ .proj₁) ,
                                                                 ⅆS==2 (ⅆ-total-mid dd ext1 ext2 .proj₂ .proj₂) regA ⟩
                                                                 ⟩
ⅆ-total-mid (ⅆS==2 {A = A} dd regA) (evar-sol ext1 regA₁) (svar ext2 regA₂) with ⅆ-total-mid dd ext1 ext2
... | ⟨ Ω , ⟨ dd1 , dd2 ⟩ ⟩ = ⟨ (Ω ,= A) , ⟨ (ⅆS==2 dd1 (⊆-⊢r regA₁ (ⅆ-l-⊆ dd1))) , (ⅆS==1 dd2 regA) ⟩ ⟩

ⅆ-⊆/x : Δ ⅆ Δ' ≋ Γ ⅆ Γ'
      → Γ' ⊆ Δ' w/v X
      → Γ ⊆ Δ w/v X
ⅆ-⊆/x (ⅆ⋈ regΓ) ext = ext
ⅆ-⊆/x (ⅆS∙ dd) (ext-Z∙ regΓ) with refl ← ⅆ-out-eq dd = ext-Z∙ (⊆-regular regΓ (ⅆ-l-⊆ dd))
ⅆ-⊆/x (ⅆS∙ dd) (ext-S∙ ext) = ext-S∙ (ⅆ-⊆/x dd ext)
ⅆ-⊆/x (ⅆS^ dd) (ext-S^ ext) = ext-S^ (ⅆ-⊆/x dd ext)
ⅆ-⊆/x (ⅆS=^ dd regA) (ext-S^ ext) = ext-S= (ⅆ-⊆/x dd ext) (⊆-⊢r' regA (ⅆ-⊆ dd))
ⅆ-⊆/x (ⅆS==1 dd regA) (ext-Z= regΓ regA₁) with refl ← ⅆ-out-eq dd = ext-Z= (⊆-regular regΓ (ⅆ-l-⊆ dd)) regA
ⅆ-⊆/x (ⅆS==1 dd regA) (ext-S= ext regA₁) = ext-S= (ⅆ-⊆/x dd ext) (⊆-⊢r regA₁ (ⅆ-r-⊆ dd))
ⅆ-⊆/x (ⅆS==2 dd regA) (ext-Z^ regΓ regA₁) with refl ← ⅆ-out-eq dd = ext-Z^ (⊆-regular regΓ (ⅆ-l-⊆ dd)) regA


ⅆ-⊆/ : Δ ⅆ Δ' ≋ Γ ⅆ Γ'
     → Γ' ⊆ Δ' w/t A
     → Γ ⊆ Δ w/t A
ⅆ-⊆/ dd (ext-int x) with refl ← ⅆ-out-eq dd = ⊆/-refl (⊆-regular x (ⅆ-l-⊆ dd)) ⊢c-int
ⅆ-⊆/ dd (ext-var x) = ext-var (ⅆ-⊆/x dd x)
ⅆ-⊆/ dd (ext-arr ext ext₁) with ⅆ-total-mid dd (⊆/-⊆ ext) (⊆/-⊆ ext₁)
... | ⟨ Ω' , ⟨ dd1 , dd2 ⟩ ⟩ = ext-arr (ⅆ-⊆/ dd1 ext) (ⅆ-⊆/ dd2 ext₁)
ⅆ-⊆/ dd (ext-∀ ext) = ext-∀ (ⅆ-⊆/ (ⅆS∙ dd) ext)
