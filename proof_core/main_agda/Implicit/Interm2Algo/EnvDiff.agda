module Implicit.Interm2Algo.EnvDiff where


open import Implicit.Language.All
open import Implicit.Algo.All

open import Implicit.Interm2Algo.FVClose


infix 3 _ⅆ_⊆_ⅆ_kp_
data _ⅆ_⊆_ⅆ_kp_ : Env n m → Env n m → Env n m → Env n m → HitMis m → Set where
  ⅆ⋈ : (regΓ : TRegular Γ)
     → Γ ⋈ ⅆ Γ ⋈ ⊆ Γ ⋈ ⅆ Γ ⋈ kp H
  ⅆS∙∙-hit : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
          → Γ ,∙ ⅆ Γ' ,∙ ⊆ Δ ,∙ ⅆ Δ' ,∙ kp (hit H)
  ⅆS∙∙-mis : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
          → Γ ,∙ ⅆ Γ' ,∙ ⊆ Δ ,∙ ⅆ Δ' ,∙ kp (mis H)
  ⅆS^=-hit : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
           → Γ ,^ ⅆ Γ' ,^ ⊆ Δ ,= A ⅆ Δ' ,= A kp (hit H)
  ⅆS^=-mis : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
           → Γ ,^ ⅆ Γ' ,^ ⊆ Δ ,= A ⅆ Δ' ,= A kp (mis H)
  ⅆS^^-hit : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
             → Γ ,^ ⅆ Γ' ,^ ⊆ Δ ,^ ⅆ Δ' ,^ kp (hit H)
  ⅆS^^-mis : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
             → Γ ,^ ⅆ Γ' ,^ ⊆ Δ ,^ ⅆ Δ' ,^ kp (mis H)
  ⅆS==-hit : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
           → (regA : Γ ⊢r A)
           → Γ ,= A ⅆ Γ' ,= A ⊆ Δ ,= A ⅆ Δ' ,= A kp (hit H)
  ⅆS==-mis-1 : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
             → (regA : Γ ⊢r A)
             → Γ ,= A ⅆ Γ' ,= A ⊆ Δ ,= A ⅆ Δ' ,= A kp (mis H)
  ⅆS==-mis-2 : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
             → (regA : Γ ⊢r A)
             → Γ ,= A ⅆ Γ' ,^ ⊆ Δ ,= A ⅆ Δ' ,^ kp (mis H)

ⅆk-⊆-l : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
      → Γ' ⊆ Γ
ⅆk-⊆-l (ⅆ⋈ regΓ) = mark regΓ
ⅆk-⊆-l (ⅆS∙∙-hit dd) = uvar (ⅆk-⊆-l dd)
ⅆk-⊆-l (ⅆS∙∙-mis dd) = uvar (ⅆk-⊆-l dd)
ⅆk-⊆-l (ⅆS^=-hit dd) = evar (ⅆk-⊆-l dd)
ⅆk-⊆-l (ⅆS^=-mis dd) = evar (ⅆk-⊆-l dd)
ⅆk-⊆-l (ⅆS^^-hit dd) = evar (ⅆk-⊆-l dd)
ⅆk-⊆-l (ⅆS^^-mis dd) = evar (ⅆk-⊆-l dd)
ⅆk-⊆-l (ⅆS==-hit dd regA) = svar (ⅆk-⊆-l dd) (⊆-⊢r' regA (ⅆk-⊆-l dd))
ⅆk-⊆-l (ⅆS==-mis-1 dd regA) = svar (ⅆk-⊆-l dd) (⊆-⊢r' regA (ⅆk-⊆-l dd))
ⅆk-⊆-l (ⅆS==-mis-2 dd regA) = evar-sol (ⅆk-⊆-l dd) regA


ⅆk-input-eq : Γ ⅆ Γ' ⊆ Γ ⅆ Δ' kp H
           → Γ' ≡ Δ'
ⅆk-input-eq (ⅆ⋈ regΓ) = refl
ⅆk-input-eq (ⅆS∙∙-hit dd) = cong _,∙ (ⅆk-input-eq dd)
ⅆk-input-eq (ⅆS∙∙-mis dd) = cong _,∙ (ⅆk-input-eq dd)
ⅆk-input-eq (ⅆS^^-hit dd) = cong _,^ (ⅆk-input-eq dd)
ⅆk-input-eq (ⅆS^^-mis dd) = cong _,^ (ⅆk-input-eq dd)
ⅆk-input-eq (ⅆS==-hit dd regA) = cong₂ _,=_ (ⅆk-input-eq dd) refl
ⅆk-input-eq (ⅆS==-mis-1 dd regA) = cong₂ _,=_ (ⅆk-input-eq dd) refl
ⅆk-input-eq (ⅆS==-mis-2 dd regA) = cong _,^ (ⅆk-input-eq dd)


ⅆk-or-l : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
         → orHit H₁ H₂ H
         → Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H₁
ⅆk-or-l (ⅆ⋈ regΓ) or = ⅆ⋈ regΓ
ⅆk-or-l (ⅆS∙∙-hit dd) (S-hm or) = ⅆS∙∙-hit (ⅆk-or-l dd or)
ⅆk-or-l (ⅆS∙∙-hit dd) (S-mh or) = ⅆS∙∙-mis (ⅆk-or-l dd or)
ⅆk-or-l (ⅆS∙∙-hit dd) (S-hh or) = ⅆS∙∙-hit (ⅆk-or-l dd or)
ⅆk-or-l (ⅆS∙∙-mis dd) (s-mm or) = ⅆS∙∙-mis (ⅆk-or-l dd or)
ⅆk-or-l (ⅆS^=-hit dd) (S-hm or) = ⅆS^=-hit (ⅆk-or-l dd or)
ⅆk-or-l (ⅆS^=-hit dd) (S-mh or) = ⅆS^=-mis (ⅆk-or-l dd or)
ⅆk-or-l (ⅆS^=-hit dd) (S-hh or) = ⅆS^=-hit (ⅆk-or-l dd or)
ⅆk-or-l (ⅆS^=-mis dd) (s-mm or) = ⅆS^=-mis (ⅆk-or-l dd or)
ⅆk-or-l (ⅆS^^-hit dd) (S-hm or) = ⅆS^^-hit (ⅆk-or-l dd or)
ⅆk-or-l (ⅆS^^-hit dd) (S-mh or) = ⅆS^^-mis (ⅆk-or-l dd or)
ⅆk-or-l (ⅆS^^-hit dd) (S-hh or) = ⅆS^^-hit (ⅆk-or-l dd or)
ⅆk-or-l (ⅆS^^-mis dd) (s-mm or) = ⅆS^^-mis (ⅆk-or-l dd or)
ⅆk-or-l (ⅆS==-hit dd regA) (S-hm or) = ⅆS==-hit (ⅆk-or-l dd or) regA
ⅆk-or-l (ⅆS==-hit dd regA) (S-mh or) = ⅆS==-mis-1 (ⅆk-or-l dd or) regA
ⅆk-or-l (ⅆS==-hit dd regA) (S-hh or) = ⅆS==-hit (ⅆk-or-l dd or) regA
ⅆk-or-l (ⅆS==-mis-1 dd regA) (s-mm or) = ⅆS==-mis-1 (ⅆk-or-l dd or) regA
ⅆk-or-l (ⅆS==-mis-2 dd regA) (s-mm or) = ⅆS==-mis-2 (ⅆk-or-l dd or) regA

ⅆk-or-r : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
         → orHit H₁ H₂ H
         → Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H₂
ⅆk-or-r (ⅆ⋈ regΓ) or = ⅆ⋈ regΓ
ⅆk-or-r (ⅆS∙∙-hit dd) (S-hm or) = ⅆS∙∙-mis (ⅆk-or-r dd or)
ⅆk-or-r (ⅆS∙∙-hit dd) (S-mh or) = ⅆS∙∙-hit (ⅆk-or-r dd or)
ⅆk-or-r (ⅆS∙∙-hit dd) (S-hh or) = ⅆS∙∙-hit (ⅆk-or-r dd or)
ⅆk-or-r (ⅆS∙∙-mis dd) (s-mm or) = ⅆS∙∙-mis (ⅆk-or-r dd or)
ⅆk-or-r (ⅆS^=-hit dd) (S-hm or) = ⅆS^=-mis (ⅆk-or-r dd or)
ⅆk-or-r (ⅆS^=-hit dd) (S-mh or) = ⅆS^=-hit (ⅆk-or-r dd or)
ⅆk-or-r (ⅆS^=-hit dd) (S-hh or) = ⅆS^=-hit (ⅆk-or-r dd or)
ⅆk-or-r (ⅆS^=-mis dd) (s-mm or) = ⅆS^=-mis (ⅆk-or-r dd or)
ⅆk-or-r (ⅆS^^-hit dd) (S-hm or) = ⅆS^^-mis (ⅆk-or-r dd or)
ⅆk-or-r (ⅆS^^-hit dd) (S-mh or) = ⅆS^^-hit (ⅆk-or-r dd or)
ⅆk-or-r (ⅆS^^-hit dd) (S-hh or) = ⅆS^^-hit (ⅆk-or-r dd or)
ⅆk-or-r (ⅆS^^-mis dd) (s-mm or) = ⅆS^^-mis (ⅆk-or-r dd or)
ⅆk-or-r (ⅆS==-hit dd regA) (S-hm or) = ⅆS==-mis-1 (ⅆk-or-r dd or) regA
ⅆk-or-r (ⅆS==-hit dd regA) (S-mh or) = ⅆS==-hit (ⅆk-or-r dd or) regA
ⅆk-or-r (ⅆS==-hit dd regA) (S-hh or) = ⅆS==-hit (ⅆk-or-r dd or) regA
ⅆk-or-r (ⅆS==-mis-1 dd regA) (s-mm or) = ⅆS==-mis-1 (ⅆk-or-r dd or) regA
ⅆk-or-r (ⅆS==-mis-2 dd regA) (s-mm or) = ⅆS==-mis-2 (ⅆk-or-r dd or) regA


ⅆk-∋∙ : Γ ⅆ Γ' ⊆ Γ ⅆ Γ' kp H
      → H ≡ mkHit X
      → Γ ∋∙ X
      → Γ' ∋∙ X
ⅆk-∋∙ (ⅆ⋈ regΓ) eq inΓ = inΓ
ⅆk-∋∙ (ⅆS∙∙-hit dd) eq Z = Z
ⅆk-∋∙ (ⅆS∙∙-mis dd) refl (S∙ inΓ) = S∙ (ⅆk-∋∙ dd refl inΓ)
ⅆk-∋∙ (ⅆS^^-hit dd) () (S^ inΓ)
ⅆk-∋∙ (ⅆS^^-mis dd) refl (S^ inΓ) = S^ (ⅆk-∋∙ dd refl inΓ)
ⅆk-∋∙ (ⅆS==-hit dd regA) () (S= inΓ)
ⅆk-∋∙ (ⅆS==-mis-1 dd regA) refl (S= inΓ) = S= (ⅆk-∋∙ dd refl inΓ)
ⅆk-∋∙ (ⅆS==-mis-2 dd regA) refl (S= inΓ) = S^ (ⅆk-∋∙ dd refl inΓ)

ⅆk-∋:= : Γ ⅆ Γ' ⊆ Γ ⅆ Γ' kp H
      → H ≡ mkHit X
      → Γ ∋ X := A
      → Γ' ∋ X := A
ⅆk-∋:= (ⅆS∙∙-hit dd) () (S∙ inΓ up)
ⅆk-∋:= (ⅆS∙∙-mis dd) refl (S∙ inΓ up) = S∙ (ⅆk-∋:= dd refl inΓ) up
ⅆk-∋:= (ⅆS^^-hit dd) () (S^ inΓ up)
ⅆk-∋:= (ⅆS^^-mis dd) refl (S^ inΓ up) = S^ (ⅆk-∋:= dd refl inΓ) up
ⅆk-∋:= (ⅆS==-hit dd regA) refl (Z up) = Z up
ⅆk-∋:= (ⅆS==-mis-1 dd regA) refl (S= inΓ up) = S= (ⅆk-∋:= dd refl inΓ) up
ⅆk-∋:= (ⅆS==-mis-2 dd regA) refl (S= inΓ up) = S^ (ⅆk-∋:= dd refl inΓ) up


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
ⅆk-total (ⅆS^=-hit dd) (evar ext1) (evar-sol ext2 regA) = ⟨ ⅆk-total dd ext1 ext2 .proj₁ ,^ ,
                                                          ⟨ ⅆS^^-hit (ⅆk-total dd ext1 ext2 .proj₂ .proj₁) ,
                                                          ⅆS^=-hit (ⅆk-total dd ext1 ext2 .proj₂ .proj₂) ⟩
                                                          ⟩
ⅆk-total (ⅆS^=-hit dd) (evar-sol {A = A} ext1 regA) (svar ext2 regA₁) = ⟨ ⅆk-total dd ext1 ext2 .proj₁ ,= A ,
                                                                ⟨ ⅆS^=-hit (ⅆk-total dd ext1 ext2 .proj₂ .proj₁) ,
                                                                ⅆS==-hit (ⅆk-total dd ext1 ext2 .proj₂ .proj₂) regA ⟩
                                                                ⟩
ⅆk-total (ⅆS^=-mis dd) (evar ext1) (evar-sol ext2 regA) = ⟨ ⅆk-total dd ext1 ext2 .proj₁ ,^ ,
                                                          ⟨ ⅆS^^-mis (ⅆk-total dd ext1 ext2 .proj₂ .proj₁) ,
                                                          ⅆS^=-mis (ⅆk-total dd ext1 ext2 .proj₂ .proj₂) ⟩
                                                          ⟩
ⅆk-total (ⅆS^=-mis {A = A} dd) (evar-sol ext1 regA) (svar ext2 regA₁) = ⟨ ⅆk-total dd ext1 ext2 .proj₁ ,= A ,
                                                                ⟨ ⅆS^=-mis (ⅆk-total dd ext1 ext2 .proj₂ .proj₁) ,
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



ⅆk-inst : [ T / X ] Γ ⟹ Δ
       → Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp mkHit X
       → [ T / X ] Γ' ⟹ Δ'
ⅆk-inst (⟹^0 up regA env) (ⅆS^=-hit dd) with refl ← ⅆk-input-eq dd = ⟹^0 up (⊆-⊢r' regA (ⅆk-⊆-l dd)) (⊆-regular' env (ⅆk-⊆-l dd))
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
s+-subirrev (s-arr s s₁) (fv-arr fv fv₁ cb) tf with ⅆk-total tf (ss-⊆ s) (ss-⊆ s₁)
... | ⟨ Ω' , ⟨ dd1 , dd2 ⟩ ⟩ = s-arr (s--subirrev s fv (ⅆk-or-l dd1 cb)) (s+-subirrev s₁ fv₁ (ⅆk-or-r dd2 cb))
s+-subirrev (s-∀ s) (fv-∀-h fv) tf = s-∀ (s+-subirrev s fv (ⅆS∙∙-hit tf))
s+-subirrev (s-∀ s) (fv-∀-m fv) tf = s-∀ (s+-subirrev s fv (ⅆS∙∙-mis tf))

s--subirrev (s-int regΓ) fv tf with refl ← ⅆk-input-eq tf = s-int (⊆-regular' regΓ (ⅆk-⊆-l tf))
s--subirrev (s-var-∙ regΓ x) fv-var tf with refl ← ⅆk-input-eq tf = s-var-∙ (⊆-regular' regΓ (ⅆk-⊆-l tf)) (ⅆk-∋∙ tf refl x)
s--subirrev (s-ex-r^ inst) fv-var tf = s-ex-r^ (ⅆk-inst inst tf)
s--subirrev (s-ex-r= regΓ x-in) fv-var tf with refl ← ⅆk-input-eq tf = s-ex-r= (⊆-regular' regΓ (ⅆk-⊆-l tf)) (ⅆk-∋:= tf refl x-in)
s--subirrev (s-arr s s₁) (fv-arr fv fv₁ cb) tf with ⅆk-total tf (ss-⊆ s) (ss-⊆ s₁)
... | ⟨ Ω' , ⟨ dd1 , dd2 ⟩ ⟩ = s-arr (s+-subirrev s fv (ⅆk-or-l dd1 cb)) (s--subirrev s₁ fv₁ (ⅆk-or-r dd2 cb))
s--subirrev (s-∀ s) (fv-∀-h fv) tf = s-∀ (s--subirrev s fv (ⅆS∙∙-hit tf))
s--subirrev (s-∀ s) (fv-∀-m fv) tf = s-∀ (s--subirrev s fv (ⅆS∙∙-mis tf))

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
ⅆk-ⅆk-gen' (ⅆS==2 dd regA) fv (hclo-S=-hit hclo) = ⅆS^=-hit (ⅆk-ⅆk-gen' dd (fv-∀-h fv) hclo)
ⅆk-ⅆk-gen' (ⅆS==2 dd regA) fv (hclo-S=-mis hclo) = ⅆS^=-mis (ⅆk-ⅆk-gen' dd (fv-∀-m fv) hclo)


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
