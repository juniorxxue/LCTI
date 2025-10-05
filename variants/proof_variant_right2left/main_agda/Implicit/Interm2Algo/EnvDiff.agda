module Implicit.Interm2Algo.EnvDiff where


open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.AuxLemmas

open import Implicit.Interm2Algo.FVClose


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

ⅆ-out-eq : Δ ⅆ Ω ≋ Ψ ⅆ Ω
         → Δ ≡ Ψ
ⅆ-out-eq (ⅆ⋈ regΓ) = refl
ⅆ-out-eq (ⅆS∙ dd) rewrite ⅆ-out-eq dd = refl
ⅆ-out-eq (ⅆS^ dd) rewrite ⅆ-out-eq dd = refl
ⅆ-out-eq (ⅆS=^ dd regA) rewrite ⅆ-out-eq dd = refl
ⅆ-out-eq (ⅆS==1 dd regA) rewrite ⅆ-out-eq dd = refl

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
ⅆ-⊆/ dd (ext-arr ext ext₁) with ⅆ-total-mid dd (⊆/-⊆ ext₁) (⊆/-⊆ ext)
... | ⟨ Ω' , ⟨ dd1 , dd2 ⟩ ⟩ = ext-arr (ⅆ-⊆/ dd2 ext) (ⅆ-⊆/ dd1 ext₁)
ⅆ-⊆/ dd (ext-∀ ext) = ext-∀ (ⅆ-⊆/ (ⅆS∙ dd) ext)


ⅆk-total :  Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
         → Γ ⊆ Ω
         → Ω ⊆ Δ
         → ∃[ Ω' ](Γ ⅆ Γ' ⊆ Ω ⅆ Ω' kp H
                 × Ω ⅆ Ω' ⊆ Δ ⅆ Δ' kp H)
ⅆk-total (ⅆ⋈ {Γ = Γ} regΓ) (mark regΓ₁) (mark regΓ₂) = ⟨ Γ ⋈ , ⟨ ⅆ⋈ regΓ , ⅆ⋈ regΓ₂ ⟩ ⟩
ⅆk-total (ⅆS∙∙-hit dd) (uvar ext1) (uvar ext2) = ⟨ ⅆk-total dd ext1 ext2 .proj₁ ,∙ ,
                                                 ⟨ ⅆS∙∙-hit (ⅆk-total dd ext1 ext2 .proj₂ .proj₁) ,
                                                 ⅆS∙∙-hit (ⅆk-total dd ext1 ext2 .proj₂ .proj₂) ⟩
                                                 ⟩
ⅆk-total (ⅆS∙∙-mis dd) (uvar ext1) (uvar ext2) = ⟨ ⅆk-total dd ext1 ext2 .proj₁ ,∙ ,
                                                 ⟨ ⅆS∙∙-mis (ⅆk-total dd ext1 ext2 .proj₂ .proj₁) ,
                                                 ⅆS∙∙-mis (ⅆk-total dd ext1 ext2 .proj₂ .proj₂) ⟩
                                                 ⟩
ⅆk-total (ⅆS^=-hit dd regA') (evar ext1) (evar-sol ext2 regA) = ⟨ ⅆk-total dd ext1 ext2 .proj₁ ,^ ,
                                                          ⟨ ⅆS^^-hit (ⅆk-total dd ext1 ext2 .proj₂ .proj₁) ,
                                                          ⅆS^=-hit (ⅆk-total dd ext1 ext2 .proj₂ .proj₂) regA' ⟩
                                                          ⟩
ⅆk-total (ⅆS^=-hit dd regA') (evar-sol {A = A} ext1 regA) (svar ext2 regA₁) = ⟨ ⅆk-total dd ext1 ext2 .proj₁ ,= A ,
                                                                ⟨ ⅆS^=-hit (ⅆk-total dd ext1 ext2 .proj₂ .proj₁) regA ,
                                                                ⅆS==-hit (ⅆk-total dd ext1 ext2 .proj₂ .proj₂) regA ⟩
                                                                ⟩
ⅆk-total (ⅆS^=-mis dd regA') (evar ext1) (evar-sol ext2 regA) = ⟨ ⅆk-total dd ext1 ext2 .proj₁ ,^ ,
                                                          ⟨ ⅆS^^-mis (ⅆk-total dd ext1 ext2 .proj₂ .proj₁) ,
                                                          ⅆS^=-mis (ⅆk-total dd ext1 ext2 .proj₂ .proj₂) regA' ⟩
                                                          ⟩
ⅆk-total (ⅆS^=-mis {A = A} dd regA') (evar-sol ext1 regA) (svar ext2 regA₁) = ⟨ ⅆk-total dd ext1 ext2 .proj₁ ,= A ,
                                                                ⟨ ⅆS^=-mis (ⅆk-total dd ext1 ext2 .proj₂ .proj₁) regA ,
                                                                ⅆS==-mis-1 (ⅆk-total dd ext1 ext2 .proj₂ .proj₂) regA ⟩
                                                                ⟩
ⅆk-total (ⅆS^^-hit dd) (evar ext1) (evar ext2) = ⟨ ⅆk-total dd ext1 ext2 .proj₁ ,^ ,
                                                 ⟨ ⅆS^^-hit (ⅆk-total dd ext1 ext2 .proj₂ .proj₁) ,
                                                 ⅆS^^-hit (ⅆk-total dd ext1 ext2 .proj₂ .proj₂) ⟩
                                                 ⟩
ⅆk-total (ⅆS^^-mis dd) (evar ext1) (evar ext2) = ⟨ ⅆk-total dd ext1 ext2 .proj₁ ,^ ,
                                                   ⟨ ⅆS^^-mis (ⅆk-total dd ext1 ext2 .proj₂ .proj₁) ,
                                                   ⅆS^^-mis (ⅆk-total dd ext1 ext2 .proj₂ .proj₂) ⟩
                                                   ⟩
ⅆk-total (ⅆS==-hit {A = A} dd regA) (svar ext1 regA') (svar ext2 regA₁) = ⟨ ⅆk-total dd ext1 ext2 .proj₁ ,= A ,
                                                            ⟨ ⅆS==-hit (ⅆk-total dd ext1 ext2 .proj₂ .proj₁) regA ,
                                                            ⅆS==-hit (ⅆk-total dd ext1 ext2 .proj₂ .proj₂) regA₁ ⟩
                                                            ⟩
ⅆk-total (ⅆS==-mis-1 {A = A} dd regA) (svar ext1 regA') (svar ext2 regA₁) = ⟨ ⅆk-total dd ext1 ext2 .proj₁ ,= A ,
                                                              ⟨ ⅆS==-mis-1 (ⅆk-total dd ext1 ext2 .proj₂ .proj₁) regA ,
                                                              ⅆS==-mis-1 (ⅆk-total dd ext1 ext2 .proj₂ .proj₂) regA₁ ⟩
                                                              ⟩
ⅆk-total (ⅆS==-mis-2 dd regA) (svar ext1 regA') (svar ext2 regA₁) = ⟨ ⅆk-total dd ext1 ext2 .proj₁ ,^ ,
                                                              ⟨ ⅆS==-mis-2 (ⅆk-total dd ext1 ext2 .proj₂ .proj₁) regA ,
                                                              ⅆS==-mis-2 (ⅆk-total dd ext1 ext2 .proj₂ .proj₂) regA₁ ⟩
                                                              ⟩


kp-mkMis : Γ' ⊆ Γ
         → Γ ⅆ Γ' ⊆ Γ ⅆ Γ' kp mkMis
kp-mkMis (uvar ext) = ⅆS∙∙-mis (kp-mkMis ext)
kp-mkMis (evar ext) = ⅆS^^-mis (kp-mkMis ext)
kp-mkMis (evar-sol ext regA) = ⅆS==-mis-2 (kp-mkMis ext) regA
kp-mkMis (svar ext regA) = ⅆS==-mis-1 (kp-mkMis ext) (⊆-⊢r regA ext)
kp-mkMis (mark regΓ) = ⅆ⋈ regΓ


dd-or : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H₁
      → Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H₂
      → orHit H₁ H₂ H
      → Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
dd-or (ⅆ⋈ regΓ) (ⅆ⋈ regΓ₁) orh = ⅆ⋈ regΓ
dd-or (ⅆS∙∙-hit dd1) (ⅆS∙∙-hit dd2) (S-hh orh) = ⅆS∙∙-hit (dd-or dd1 dd2 orh)
dd-or (ⅆS∙∙-hit dd1) (ⅆS∙∙-mis dd2) (S-hm orh) = ⅆS∙∙-hit (dd-or dd1 dd2 orh)
dd-or (ⅆS∙∙-mis dd1) (ⅆS∙∙-hit dd2) (S-mh orh) = ⅆS∙∙-hit (dd-or dd1 dd2 orh)
dd-or (ⅆS∙∙-mis dd1) (ⅆS∙∙-mis dd2) (s-mm orh) = ⅆS∙∙-mis (dd-or dd1 dd2 orh)
dd-or (ⅆS^=-hit dd1 regA) (ⅆS^=-hit dd2 regA') (S-hh orh) = ⅆS^=-hit (dd-or dd1 dd2 orh) regA
dd-or (ⅆS^=-hit dd1 regA) (ⅆS^=-mis dd2 regA') (S-hm orh) = ⅆS^=-hit (dd-or dd1 dd2 orh) regA
dd-or (ⅆS^=-mis dd1 regA) (ⅆS^=-hit dd2 regA') (S-mh orh) = ⅆS^=-hit (dd-or dd1 dd2 orh) regA
dd-or (ⅆS^=-mis dd1 regA) (ⅆS^=-mis dd2 regA') (s-mm orh) = ⅆS^=-mis (dd-or dd1 dd2 orh) regA
dd-or (ⅆS^^-hit dd1) (ⅆS^^-hit dd2) (S-hh orh) = ⅆS^^-hit (dd-or dd1 dd2 orh)
dd-or (ⅆS^^-hit dd1) (ⅆS^^-mis dd2) (S-hm orh) = ⅆS^^-hit (dd-or dd1 dd2 orh)
dd-or (ⅆS^^-mis dd1) (ⅆS^^-hit dd2) (S-mh orh) = ⅆS^^-hit (dd-or dd1 dd2 orh)
dd-or (ⅆS^^-mis dd1) (ⅆS^^-mis dd2) (s-mm orh) = ⅆS^^-mis (dd-or dd1 dd2 orh)
dd-or (ⅆS==-hit dd1 regA) (ⅆS==-hit dd2 regA₁) (S-hh orh) = ⅆS==-hit (dd-or dd1 dd2 orh) regA
dd-or (ⅆS==-hit dd1 regA) (ⅆS==-mis-1 dd2 regA₁) (S-hm orh) = ⅆS==-hit (dd-or dd1 dd2 orh) regA
dd-or (ⅆS==-mis-1 dd1 regA) (ⅆS==-hit dd2 regA₁) (S-mh orh) = ⅆS==-hit (dd-or dd1 dd2 orh) regA
dd-or (ⅆS==-mis-1 dd1 regA) (ⅆS==-mis-1 dd2 regA₁) (s-mm orh) = ⅆS==-mis-1 (dd-or dd1 dd2 orh) regA
dd-or (ⅆS==-mis-2 dd1 regA) (ⅆS==-mis-2 dd2 regA₁) (s-mm orh) = ⅆS==-mis-2 (dd-or dd1 dd2 orh) regA

∋∙-⊆-kp : Γ' ⊆ Γ
        → Γ ∋∙ X
        → Γ ⅆ Γ' ⊆ Γ ⅆ Γ' kp mkHit X
∋∙-⊆-kp (uvar ext) Z = ⅆS∙∙-hit (kp-mkMis ext)
∋∙-⊆-kp (uvar ext) (S∙ inΓ) = ⅆS∙∙-mis (∋∙-⊆-kp ext inΓ)
∋∙-⊆-kp (evar ext) (S^ inΓ) = ⅆS^^-mis (∋∙-⊆-kp ext inΓ)
∋∙-⊆-kp (evar-sol ext regA) (S= inΓ) = ⅆS==-mis-2 (∋∙-⊆-kp ext inΓ) regA
∋∙-⊆-kp (svar ext regA) (S= inΓ) = ⅆS==-mis-1 (∋∙-⊆-kp ext inΓ) (⊆-⊢r regA ext)
∋∙-⊆-kp (mark regΓ) (S⋈ inΓ) = ⅆ⋈ regΓ

⊢r-exist-kp : ∀ {A : Type m}
            → Γ' ⊆ Γ
            → Γ ⊢r A
            → ∃[ H ]((A 𝕗𝕧 H) × (Γ ⅆ Γ' ⊆ Γ ⅆ Γ' kp H))
⊢r-exist-kp {m = m} ext ⊢r-int = ⟨ mkMis , ⟨ fv-Int , kp-mkMis ext ⟩ ⟩
⊢r-exist-kp ext (⊢r-var-∙ {X = X} inΓ) = ⟨ mkHit X , ⟨ fv-var , ∋∙-⊆-kp ext inΓ ⟩ ⟩
⊢r-exist-kp ext (⊢r-arr regA regA₁) with ⊢r-exist-kp ext regA | ⊢r-exist-kp ext regA₁
... | ⟨ H1 , ⟨ fv1 , dd1 ⟩ ⟩ | ⟨ H2 , ⟨ fv2 , dd2 ⟩ ⟩
  with ⟨ Hor , fv12 ⟩ ← orHit-total H1 H2 = ⟨ Hor , ⟨ (fv-arr fv1 fv2 fv12) , dd-or dd1 dd2 fv12 ⟩ ⟩
⊢r-exist-kp ext (⊢r-∀ regA) with ⊢r-exist-kp (uvar ext) regA
... | ⟨ hit H' , ⟨ fv , ⅆS∙∙-hit dd ⟩ ⟩ = ⟨ H' , ⟨ fv-∀-h fv , dd ⟩ ⟩
... | ⟨ mis H' , ⟨ fv , ⅆS∙∙-mis dd ⟩ ⟩ = ⟨ H' , ⟨ fv-∀-m fv , dd ⟩ ⟩



ⅆk-inst : [ T / X ] Γ ⟹ Δ
       → Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp mkHit X
       → [ T / X ] Γ' ⟹ Δ'
ⅆk-inst (⟹^0 up regA env) (ⅆS^=-hit dd regA') with refl ← ⅆk-input-eq dd = ⟹^0 up (⊆-⊢r' regA (ⅆk-⊆-l dd)) (⊆-regular' env (ⅆk-⊆-l dd))
ⅆk-inst (⟹^S inst up1) (ⅆS^^-mis dd) = ⟹^S (ⅆk-inst inst dd) up1
ⅆk-inst (⟹∙S inst up1) (ⅆS∙∙-mis dd) = ⟹∙S (ⅆk-inst inst dd) up1
ⅆk-inst (⟹=S inst up1 regB) (ⅆS==-mis-1 dd regA) = ⟹=S (ⅆk-inst inst dd) up1 (⊆-⊢r' regB (ⅆk-⊆-l dd))
ⅆk-inst (⟹=S inst up1 regB) (ⅆS==-mis-2 dd regA) = ⟹^S (ⅆk-inst inst dd) up1

s+-subirrev : Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ
            → A 𝕗𝕧 H
            → Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
            → Γ' ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ'

s--subirrev : Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ
            → B 𝕗𝕧 H
            → Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
            → Γ' ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ'

s+-subirrev (s-int regΓ) fv-Int tf with refl ← ⅆk-input-eq tf = s-int (⊆-regular' regΓ (ⅆk-⊆-l tf))
s+-subirrev (s-var-∙ regΓ x) fv-var tf with refl ← ⅆk-input-eq tf = s-var-∙ (⊆-regular' regΓ (ⅆk-⊆-l tf)) (ⅆk-∋∙ tf refl x)
s+-subirrev (s-ex-l^ inst) fv-var tf = s-ex-l^ (ⅆk-inst inst tf)
s+-subirrev (s-ex-l= regΓ x-in) fv-var tf with refl ← ⅆk-input-eq tf = s-ex-l= (⊆-regular' regΓ (ⅆk-⊆-l tf)) (ⅆk-∋:= tf refl x-in)
s+-subirrev (s-arr s s₁) (fv-arr fv fv₁ cb) tf with ⅆk-total tf (ss-⊆ s₁) (ss-⊆ s)
... | ⟨ Ω' , ⟨ dd1 , dd2 ⟩ ⟩ = s-arr (s--subirrev s fv (ⅆk-or-l dd2 cb)) (s+-subirrev s₁ fv₁ (ⅆk-or-r dd1 cb))
s+-subirrev (s-∀ s) (fv-∀-h fv) tf = s-∀ (s+-subirrev s fv (ⅆS∙∙-hit tf))
s+-subirrev (s-∀ s) (fv-∀-m fv) tf = s-∀ (s+-subirrev s fv (ⅆS∙∙-mis tf))

s--subirrev (s-int regΓ) fv tf with refl ← ⅆk-input-eq tf = s-int (⊆-regular' regΓ (ⅆk-⊆-l tf))
s--subirrev (s-var-∙ regΓ x) fv-var tf with refl ← ⅆk-input-eq tf = s-var-∙ (⊆-regular' regΓ (ⅆk-⊆-l tf)) (ⅆk-∋∙ tf refl x)
s--subirrev (s-ex-r^ inst) fv-var tf = s-ex-r^ (ⅆk-inst inst tf)
s--subirrev (s-ex-r= regΓ x-in) fv-var tf with refl ← ⅆk-input-eq tf = s-ex-r= (⊆-regular' regΓ (ⅆk-⊆-l tf)) (ⅆk-∋:= tf refl x-in)
s--subirrev (s-arr s s₁) (fv-arr fv fv₁ cb) tf with ⅆk-total tf (ss-⊆ s₁) (ss-⊆ s)
... | ⟨ Ω' , ⟨ dd1 , dd2 ⟩ ⟩ = s-arr (s+-subirrev s fv (ⅆk-or-l dd2 cb)) (s--subirrev s₁ fv₁ (ⅆk-or-r dd1 cb))
s--subirrev (s-∀ s) (fv-∀-h fv) tf = s-∀ (s--subirrev s fv (ⅆS∙∙-hit tf))
s--subirrev (s-∀ s) (fv-∀-m fv) tf = s-∀ (s--subirrev s fv (ⅆS∙∙-mis tf))


s-subirrev : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
           → A 𝕗𝕧 H
           → Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
           → Γ' ⊢ A ≤⁺ Σ ⊣ Δ' ↪ B
s-subirrev (s-empty regΓ cloA grd) fv tf with refl ← ⅆk-input-eq tf = s-empty (⊆-regular' regΓ (ⅆk-⊆-l tf)) (ⅆk-⊢c-r cloA fv tf) (ⅆk-≫-r grd fv tf)
s-subirrev (s-type ss) fv tf = s-type (s+-subirrev ss fv tf)
s-subirrev (s-term-c cloA ap ⊢e s) (fv-arr fv fv₁ x) tf
  = s-term-c (ⅆk-⊢c-r cloA fv (ⅆk-or-l tf x)) (ⅆk-≫-r ap fv (ⅆk-or-l tf x)) (t-irrev-⊆' ⊢e (ⅆk-⊆-r tf)) (s-subirrev s fv₁ (ⅆk-or-r tf x))
s-subirrev (s-term-o opnA ⊢e ss s) (fv-arr fv fv₁ x) tf with ⅆk-total tf (s-⊆ s) (ss-⊆ ss)
... | ⟨ Ω' , ⟨ dd1 , dd2 ⟩ ⟩ = s-term-o (ⅆk-⊢o-r opnA fv (ⅆk-or-l dd1 x)) (t-irrev-⊆' ⊢e (ⅆk-⊆-r dd1)) (s--subirrev ss fv (ⅆk-or-l dd2 x)) (s-subirrev s fv₁ (ⅆk-or-r dd1 x))
s-subirrev (s-∀l s upᶜ upᵉ upC upD) (fv-∀-h fv) tf
  with s-env-out s
... | reg-S= r regA = s-∀l (s-subirrev s fv (ⅆS^=-hit tf regA)) upᶜ upᵉ upC upD
s-subirrev (s-∀l s upᶜ upᵉ upC upD) (fv-∀-m fv) tf
  with s-env-out s
... | reg-S= r regA = s-∀l (s-subirrev s fv (ⅆS^=-mis tf regA)) upᶜ upᵉ upC upD
s-subirrev (s-∀l-no s upᶜ upᵉ upC upD) (fv-∀-h fv) tf = s-∀l-no (s-subirrev s fv (ⅆS^^-hit tf)) upᶜ upᵉ upC upD
s-subirrev (s-∀l-no s upᶜ upᵉ upC upD) (fv-∀-m fv) tf = s-∀l-no (s-subirrev s fv (ⅆS^^-mis tf)) upᶜ upᵉ upC upD
s-subirrev (s-tapp s upᶜ) (fv-∀-h fv) tf with s-env-in s
... | reg-S= r regA = s-tapp (s-subirrev s fv (ⅆS==-hit tf regA)) upᶜ
s-subirrev (s-tapp s upᶜ) (fv-∀-m fv) tf with s-env-in s
... | reg-S= r regA = s-tapp (s-subirrev s fv (ⅆS==-mis-1 tf regA)) upᶜ
s-subirrev (s-svar-term x s) fv-var tf with refl ← ⅆk-input-eq tf
  with ⟨ H , ⟨ fv , dd ⟩ ⟩ ← ⊢r-exist-kp (ⅆk-⊆-l tf) (∋:=-⊢r (s-env-in s) x)
  = s-svar-term (ⅆk-∋:= tf refl x) (s-subirrev s fv dd)
s-subirrev (s-svar-tapp x s) fv-var tf with refl ← ⅆk-input-eq tf
  with ⟨ H , ⟨ fv , dd ⟩ ⟩ ← ⊢r-exist-kp (ⅆk-⊆-l tf) (∋:=-⊢r (s-env-in s) x)
  = s-svar-tapp (ⅆk-∋:= tf refl x) (s-subirrev s fv dd)

ⅆk-ⅆk-gen' : Δ ⅆ Ω ≋ Ψ ⅆ Γ
          → A 𝕗𝕧 H
          → HClosed Ω H
          → Ψ ⅆ Γ ⊆ Δ ⅆ Ω kp H
ⅆk-ⅆk-gen' (ⅆ⋈ regΓ) fv hclo = ⅆ⋈ regΓ
ⅆk-ⅆk-gen' (ⅆS∙ dd) fv (hclo-S∙-hit hclo) = ⅆS∙∙-hit (ⅆk-ⅆk-gen' dd (fv-∀-h fv) hclo)
ⅆk-ⅆk-gen' (ⅆS∙ dd) fv (hclo-S∙-mis hclo) = ⅆS∙∙-mis (ⅆk-ⅆk-gen' dd (fv-∀-m fv) hclo)
ⅆk-ⅆk-gen' (ⅆS^ dd) fv (hclo-S^ hclo) = ⅆS^^-mis (ⅆk-ⅆk-gen' dd (fv-∀-m fv) hclo)
ⅆk-ⅆk-gen' (ⅆS=^ dd regA) fv (hclo-S^ hclo) = ⅆS==-mis-2 (ⅆk-ⅆk-gen' dd (fv-∀-m fv) hclo) (⊆-⊢r' regA (ⅆ-⊆ dd))
ⅆk-ⅆk-gen' (ⅆS==1 dd regA) fv (hclo-S=-hit hclo) = ⅆS==-hit (ⅆk-ⅆk-gen' dd (fv-∀-h fv) hclo) (⊆-⊢r' regA (ⅆ-⊆ dd))
ⅆk-ⅆk-gen' (ⅆS==1 dd regA) fv (hclo-S=-mis hclo) = ⅆS==-mis-1 (ⅆk-ⅆk-gen' dd (fv-∀-m fv) hclo) (⊆-⊢r' regA (ⅆ-⊆ dd))
ⅆk-ⅆk-gen' (ⅆS==2 dd regA) fv (hclo-S=-hit hclo) = ⅆS^=-hit (ⅆk-ⅆk-gen' dd (fv-∀-h fv) hclo) regA
ⅆk-ⅆk-gen' (ⅆS==2 dd regA) fv (hclo-S=-mis hclo) = ⅆS^=-mis (ⅆk-ⅆk-gen' dd (fv-∀-m fv) hclo) regA


s--subirrev-final : Ψ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ
           → Δ ⅆ Ω ≋ Ψ ⅆ Γ
           → Ω ⊢c B
           → Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Ω
s--subirrev-final {B = B} s dd cloB
  with (f-close fv hclo) ← ⊢c-fclose cloB = s--subirrev s fv (ⅆk-ⅆk-gen' dd fv hclo)

s+-subirrev-final : Ψ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ
           → Δ ⅆ Ω ≋ Ψ ⅆ Γ
           → Ω ⊢c A
           → Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Ω
s+-subirrev-final {A = A} s dd cloB
 with (f-close fv hclo) ← ⊢c-fclose cloB = s+-subirrev s fv (ⅆk-ⅆk-gen' dd fv hclo)


s-subirrev-final : Ψ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
                 → Δ ⅆ Ω ≋ Ψ ⅆ Γ
                 → Ω ⊢c A
                 → Γ ⊢ A ≤⁺ Σ ⊣ Ω ↪ B
s-subirrev-final {A = A} s dd cloA
  with (f-close fv hclo) ← ⊢c-fclose cloA = s-subirrev s fv (ⅆk-ⅆk-gen' dd fv hclo)
