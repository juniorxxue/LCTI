module Implicit.NewCompleteIntermAlgoAux where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm.Base

----------------------------------------------------------------------
--+                         env extension                          +--
----------------------------------------------------------------------

reg-⊆/x∙ : SRegular Δ
        → Δ ∋∙ X
        → Δ ⊆ Δ w/v X
reg-⊆/x∙ (reg-Z regΓ) (S⋈ inΔ) = ext-mark regΓ
reg-⊆/x∙ (reg-S∙ regΔ) Z = ext-Z∙ regΔ
reg-⊆/x∙ (reg-S∙ regΔ) (S∙ inΔ) = ext-S∙ (reg-⊆/x∙ regΔ inΔ)
reg-⊆/x∙ (reg-S^ regΔ) (S^ inΔ) = ext-S^ (reg-⊆/x∙ regΔ inΔ)
reg-⊆/x∙ (reg-S= regΔ regA) (S= inΔ) = ext-S= (reg-⊆/x∙ regΔ inΔ) regA

reg-⊆/ : SRegular Δ
       → Δ ⊢r A
       → Δ ⊆ Δ w/t A
reg-⊆/ senv ⊢r-int = ext-int senv
reg-⊆/ senv (⊢r-var-∙ inΓ) = ext-var (reg-⊆/x∙ senv inΓ)
reg-⊆/ senv (⊢r-arr regA regA₁) = ext-arr (reg-⊆/ senv regA) (reg-⊆/ senv regA₁)
reg-⊆/ senv (⊢r-∀ regA) = ext-∀ (reg-⊆/ (reg-S∙ senv) regA)

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

~t-~s : Γ ⊢ ⟨ j , B ⟩ ~t Σ
      → Γ ⋈ ⊢ ⟨ j , B ⟩ ~s Σ
~t-~s ~Z = ~Z
~t-~s ~∞ = ~∞
~t-~s (~I ⊢e j~Σ) = ~I ⊢e (~t-~s j~Σ)
~t-~s (~C ⊢e j~Σ) = ~C ⊢e (~t-~s j~Σ)

----------------------------------------------------------------------
--+                           extension                            +--
----------------------------------------------------------------------


⊆/x-∋∙-eq : Γ ⊆ Δ w/v X
          → Γ ∋∙ X
          → Γ ≡ Δ
⊆/x-∋∙-eq (ext-Z∙ regΓ) Z = refl
⊆/x-∋∙-eq (ext-S^ ext) (S^ inΓ) = cong _,^ (⊆/x-∋∙-eq ext inΓ)
⊆/x-∋∙-eq (ext-S∙ ext) (S∙ inΓ) = cong _,∙ (⊆/x-∋∙-eq ext inΓ)
⊆/x-∋∙-eq (ext-S= ext regA) (S= inΓ) = cong₂ _,=_ (⊆/x-∋∙-eq ext inΓ) refl
⊆/x-∋∙-eq (ext-mark x) inΓ = refl

⊆/x-∋=-eq : Γ ⊆ Δ w/v X
          → Γ ∋= X
          → Γ ≡ Δ
⊆/x-∋=-eq (ext-Z= regA regΓ) Z = refl
⊆/x-∋=-eq (ext-S^ ext) (S^ inΓ) = cong _,^ (⊆/x-∋=-eq ext inΓ)
⊆/x-∋=-eq (ext-S∙ ext) (S∙ inΓ) = cong _,∙ (⊆/x-∋=-eq ext inΓ)
⊆/x-∋=-eq (ext-S= ext _) (S= inΓ) = cong₂ _,=_ (⊆/x-∋=-eq ext inΓ) refl

⊆/-⊢c-eq : Γ ⊆ Δ w/t A
         → Γ ⊢c A
         → Γ ≡ Δ
⊆/-⊢c-eq (ext-int regΓ) cloA = refl
⊆/-⊢c-eq (ext-var x) (⊢c-var-∙ inΔ) = ⊆/x-∋∙-eq x inΔ
⊆/-⊢c-eq (ext-var x) (⊢c-var-= inΔ) = ⊆/x-∋=-eq x inΔ
⊆/-⊢c-eq (ext-arr ext ext₁) (⊢c-arr cloA cloA₁)
  with refl ← ⊆/-⊢c-eq ext cloA
  with refl ← ⊆/-⊢c-eq ext₁ cloA₁ = refl
⊆/-⊢c-eq (ext-∀ ext) (⊢c-∀ cloA)
  with refl ← ⊆/-⊢c-eq ext cloA = refl

⊆/-∙out-∙in : Δ ∋∙ X
            → Γ ⊆ Δ w/v X
            → Γ ∋∙ X
⊆/-∙out-∙in Z (ext-Z∙ _) = Z
⊆/-∙out-∙in (S∙ inΓ) (ext-S∙ ext) = S∙ (⊆/-∙out-∙in inΓ ext)
⊆/-∙out-∙in (S= inΓ) (ext-S= ext _) = S= (⊆/-∙out-∙in inΓ ext)
⊆/-∙out-∙in (S^ inΓ) (ext-S^ ext) = S^ (⊆/-∙out-∙in inΓ ext)
⊆/-∙out-∙in (S⋈ inΓ) (ext-mark x) = S⋈ inΓ

----------------------------------------------------------------------
--+                       env extension diff                       +--
----------------------------------------------------------------------

-- use for proving the arrow case

-- we know that Ω ⊆ Δ
-- and Γ ⊆ Ω, this relation should imply this property

-- Δ ⅆ Ω ≋ Ψ ⅆ Γ
infix 3 _ⅆ_≋_ⅆ_

data _ⅆ_≋_ⅆ_ : Env n m → Env n m → Env n m → Env n m → Set where
  ⅆ⋈ : (TRegular Γ)
     → Γ ⋈ ⅆ Γ ⋈ ≋ Γ ⋈ ⅆ Γ ⋈
  ⅆS∙ : Δ ⅆ Ω ≋ Ψ ⅆ Γ
      → Δ ,∙ ⅆ Ω ,∙  ≋ Ψ ,∙ ⅆ Γ ,∙
  ⅆS^ : Δ ⅆ Ω ≋ Ψ ⅆ Γ
      → Δ ,^ ⅆ Ω ,^  ≋ Ψ ,^ ⅆ Γ ,^
  ⅆS=^ : Δ ⅆ Ω ≋ Ψ ⅆ Γ
       → (regA : Δ ⊢r A)
       → Δ ,= A ⅆ Ω ,^  ≋ Ψ ,= A ⅆ Γ ,^
  ⅆS==1 : Δ ⅆ Ω ≋ Ψ ⅆ Γ
      → Δ ,= A ⅆ Ω ,= A  ≋ Ψ ,= A ⅆ Γ ,= A
  ⅆS==2 : Δ ⅆ Ω ≋ Ψ ⅆ Γ
      → Δ ,= A ⅆ Ω ,= A  ≋ Ψ ,^ ⅆ Γ ,^

ⅆ-total : Γ ⊆ Ω
        → Ω ⊆ Δ
        → ∃[ Ψ ](Δ ⅆ Ω ≋ Ψ ⅆ Γ)
ⅆ-total (uvar ext1) (uvar ext2) = ⟨ ⅆ-total ext1 ext2 .proj₁ ,∙ , ⅆS∙ (ⅆ-total ext1 ext2 .proj₂) ⟩
ⅆ-total (evar ext1) (evar ext2) = ⟨ ⅆ-total ext1 ext2 .proj₁ ,^ , ⅆS^ (ⅆ-total ext1 ext2 .proj₂) ⟩
ⅆ-total (evar ext1) (evar-sol {A = A} ext2 regA) = ⟨ ⅆ-total ext1 ext2 .proj₁ ,= A , ⅆS=^ (ⅆ-total ext1 ext2 .proj₂) regA ⟩
ⅆ-total (evar-sol ext1 regA) (svar ext2 regA₁) = ⟨ ⅆ-total ext1 ext2 .proj₁ ,^ , ⅆS==2 (ⅆ-total ext1 ext2 .proj₂) ⟩
ⅆ-total (svar ext1 regA) (svar {A = A} ext2 regA₁) = ⟨ ⅆ-total ext1 ext2 .proj₁ ,= A , ⅆS==1 (ⅆ-total ext1 ext2 .proj₂) ⟩
ⅆ-total (mark {Γ = Γ} x) (mark x₁) = ⟨ Γ ⋈ , ⅆ⋈ x ⟩


-- ⅆ-⊆ : Δ ⅆ Ω ≋ Ψ ⅆ Γ
--     → Ψ ⊆ Δ
-- ⅆ-⊆ (ⅆ⋈ regΓ) = mark regΓ
-- ⅆ-⊆ (ⅆS∙ ext) = uvar (ⅆ-⊆ ext)
-- ⅆ-⊆ (ⅆS^ ext) = evar (ⅆ-⊆ ext)
-- ⅆ-⊆ (ⅆS=^ ext regA) with ⅆ-⊆ ext
-- ... | ih = svar ih (⊆-⊢r' regA ih)
-- ⅆ-⊆ (ⅆS==1 ext) = {!!}
-- ⅆ-⊆ (ⅆS==2 ext) = {!!}


----------------------------------------------------------------------
--+             restricted extension implies extension             +--
----------------------------------------------------------------------

⊆/x-⊆ : Γ ⊆ Δ w/v X
      → Γ ⊆ Δ
⊆/x-⊆ (ext-Z^ regΓ regA) = evar-sol (⊆-refl regΓ) regA
⊆/x-⊆ (ext-Z∙ regΓ) = ⊆-refl (reg-S∙ regΓ)
⊆/x-⊆ (ext-Z= regΓ regA) = ⊆-refl (reg-S= regΓ regA)
⊆/x-⊆ (ext-S^ ext) = evar (⊆/x-⊆ ext)
⊆/x-⊆ (ext-S∙ ext) = uvar (⊆/x-⊆ ext)
⊆/x-⊆ (ext-S= ext regA) = svar (⊆/x-⊆ ext) regA
⊆/x-⊆ (ext-mark x) = mark x

⊆/-⊆ : Γ ⊆ Δ w/t A
     → Γ ⊆ Δ
⊆/-⊆ (ext-int regΓ) = ⊆-refl regΓ
⊆/-⊆ (ext-var x) = ⊆/x-⊆ x
⊆/-⊆ (ext-arr ext ext₁) = ⊆-trans (⊆/-⊆ ext) (⊆/-⊆ ext₁)
⊆/-⊆ (ext-∀ ext) with ⊆/-⊆ ext
... | uvar r = r


----------------------------------------------------------------------
--+                             Irrev                              +--
----------------------------------------------------------------------

postulate
  t-irrev-⊆ : 𝕣 Γ ⊢ Σ ⇒ e ⇒ A
            → Γ ⊆ Δ
            → 𝕣 Δ ⊢ Σ ⇒ e ⇒ A


~irrev : Γ ⊢ ⟨ j , D ⟩ ~s Σ
        → Γ ⊆ Ω
        → Ω ⊢ ⟨ j , D ⟩ ~s Σ
~irrev ~Z ext = ~Z
~irrev ~∞ ext = ~∞
~irrev (~I ⊢e ~j) ext = ~I (t-irrev-⊆ ⊢e ext) (~irrev ~j ext)
~irrev (~C ⊢e ~j) ext = ~C (t-irrev-⊆ ⊢e ext) (~irrev ~j ext)
