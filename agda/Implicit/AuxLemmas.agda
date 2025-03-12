module Implicit.AuxLemmas where

open import Implicit.Language.All


-- could be proved via a inst-total
-- however, the total requires a condition: B is shifted k times, which is a tricky to define in well-scoped settings: finite nubmers
inst-exist : [ B / k ] Δ =⟹ Δ'
           → Ω ⊆ Δ
           → Ω ∋= k
           → ∃[ Ω' ]( [ B / k ] Ω =⟹ Ω')
inst-exist (=⟹=0  {A = A} up) (svar {Γ = Γ} ext regA) Z = ⟨ Γ ,= A , =⟹=0 up ⟩
inst-exist (=⟹^S inst up1) (evar ext) (S^ inΩ) = ⟨ inst-exist inst ext inΩ .proj₁ ,^ ,
                                                  =⟹^S (inst-exist inst ext inΩ .proj₂) up1 ⟩
inst-exist (=⟹∙S inst up1) (uvar ext) (S∙ inΩ) = ⟨ inst-exist inst ext inΩ .proj₁ ,∙ ,
                                                  =⟹∙S (inst-exist inst ext inΩ .proj₂) up1 ⟩
inst-exist (=⟹=S inst up1) (evar-sol ext regA) (S^ inΩ) = ⟨ inst-exist inst ext inΩ .proj₁ ,^ ,
                                                           =⟹^S (inst-exist inst ext inΩ .proj₂) up1 ⟩
inst-exist (=⟹=S inst up1) (svar {A = A} ext regA) (S= inΩ) = ⟨ inst-exist inst ext inΩ .proj₁ ,= A ,
                                                       =⟹=S (inst-exist inst ext inΩ .proj₂) up1 ⟩

{-
data Env : ℕ → ℕ → Set where
  ∅     : Env 0 0
  _,_   : Env n m → (A : Type m) → Env (1 + n) m
  _,^   : Env n m → Env n (1 + m)
  _,∙   : Env n m → Env n (1 + m)
  _,=_  : Env n m → (A : Type m) → Env n (1 + m)
  _⋈    : Env n m → Env n m
-}

data HitEnv : ℕ → Set where
  ∅ : HitEnv 0
  hit : HitEnv m → HitEnv (1 + m)
  mis : HitEnv m → HitEnv (1 + m)

variable
  H H₁ H₂ : HitEnv m

mkMis : ∀ {m} → HitEnv m
mkMis {zero} = ∅
mkMis {suc m} = mis (mkMis {m})

mkHit : ∀ {m} → Fin m → HitEnv m
mkHit {suc m} #0 = hit (mkMis {m})
mkHit {suc m} (#S k) = mis (mkHit {m} k)

data orHit : HitEnv m → HitEnv m → HitEnv m → Set where
  Z : orHit ∅ ∅ ∅
  S-hm : orHit H₁ H₂ H
    → orHit (hit H₁) (mis H₂) (hit H)
  S-mh : orHit H₁ H₂ H
    → orHit (mis H₁) (hit H₂) (hit H)
  S-hh : orHit H₁ H₂ H
    → orHit (hit H₁) (hit H₂) (hit H)
  s-mm : orHit H₁ H₂ H
    → orHit (mis H₁) (mis H₂) (mis H)

infix 3 _𝕗𝕧_
data _𝕗𝕧_ : Type m → HitEnv m → Set where
  fv-Int : Int 𝕗𝕧 ∅
  fv-var : (‶ X) 𝕗𝕧 mkHit X
  fv-arr : A 𝕗𝕧 H₁
         → B 𝕗𝕧 H₂
         → orHit H₁ H₂ H
         → A `→ B 𝕗𝕧 H
  fv-∀-h : A 𝕗𝕧 (hit H)
         → `∀ A 𝕗𝕧 H
  fv-∀-m : A 𝕗𝕧 (mis H)
         → `∀ A 𝕗𝕧 H

{-
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
-}

infix 3 _ⅆ_⊆_ⅆ_kp_
data _ⅆ_⊆_ⅆ_kp_ : Env n m → Env n m → Env n m → Env n m → HitEnv m → Set where
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
{-
  ⅆS^^-mis-2 : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
             → Γ ,^ ⅆ Γ' ,= A ⊆ Δ ,^ ⅆ Δ' ,= A kp (mis H)
-}
  ⅆS==-hit : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
           → (regA : Γ ⊢r A)
           → Γ ,= A ⅆ Γ' ,= A ⊆ Δ ,= A ⅆ Δ' ,= A kp (hit H)
  ⅆS==-mis-1 : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
             → (regA : Γ ⊢r A)
             → Γ ,= A ⅆ Γ' ,= A ⊆ Δ ,= A ⅆ Δ' ,= A kp (mis H)
  ⅆS==-mis-2 : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
             → (regA : Γ ⊢r A)
             → Γ ,= A ⅆ Γ' ,^ ⊆ Δ ,= A ⅆ Δ' ,^ kp (mis H)

ⅆ-⊆-l : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
      → Γ' ⊆ Γ -- not essential
ⅆ-⊆-l (ⅆ⋈ regΓ) = mark regΓ
ⅆ-⊆-l (ⅆS∙∙-hit dd) = uvar (ⅆ-⊆-l dd)
ⅆ-⊆-l (ⅆS∙∙-mis dd) = uvar (ⅆ-⊆-l dd)
ⅆ-⊆-l (ⅆS^=-hit dd) = evar (ⅆ-⊆-l dd)
ⅆ-⊆-l (ⅆS^=-mis dd) = evar (ⅆ-⊆-l dd)
ⅆ-⊆-l (ⅆS^^-hit dd) = evar (ⅆ-⊆-l dd)
ⅆ-⊆-l (ⅆS^^-mis dd) = evar (ⅆ-⊆-l dd)
ⅆ-⊆-l (ⅆS==-hit dd regA) = svar (ⅆ-⊆-l dd) (⊆-⊢r' regA (ⅆ-⊆-l dd))
ⅆ-⊆-l (ⅆS==-mis-1 dd regA) = svar (ⅆ-⊆-l dd) (⊆-⊢r' regA (ⅆ-⊆-l dd))
ⅆ-⊆-l (ⅆS==-mis-2 dd regA) = evar-sol (ⅆ-⊆-l dd) regA


ⅆ-input-eq : Γ ⅆ Γ' ⊆ Γ ⅆ Δ' kp H
           → Γ' ≡ Δ'
ⅆ-input-eq (ⅆ⋈ regΓ) = refl
ⅆ-input-eq (ⅆS∙∙-hit dd) = cong _,∙ (ⅆ-input-eq dd)
ⅆ-input-eq (ⅆS∙∙-mis dd) = cong _,∙ (ⅆ-input-eq dd)
ⅆ-input-eq (ⅆS^^-hit dd) = cong _,^ (ⅆ-input-eq dd)
ⅆ-input-eq (ⅆS^^-mis dd) = cong _,^ (ⅆ-input-eq dd)
ⅆ-input-eq (ⅆS==-hit dd regA) = cong₂ _,=_ (ⅆ-input-eq dd) refl
ⅆ-input-eq (ⅆS==-mis-1 dd regA) = cong₂ _,=_ (ⅆ-input-eq dd) refl
ⅆ-input-eq (ⅆS==-mis-2 dd regA) = cong _,^ (ⅆ-input-eq dd)


ⅆ-or-l : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
         → orHit H₁ H₂ H
         → Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H₁
ⅆ-or-l (ⅆ⋈ regΓ) or = ⅆ⋈ regΓ
ⅆ-or-l (ⅆS∙∙-hit dd) (S-hm or) = ⅆS∙∙-hit (ⅆ-or-l dd or)
ⅆ-or-l (ⅆS∙∙-hit dd) (S-mh or) = ⅆS∙∙-mis (ⅆ-or-l dd or)
ⅆ-or-l (ⅆS∙∙-hit dd) (S-hh or) = ⅆS∙∙-hit (ⅆ-or-l dd or)
ⅆ-or-l (ⅆS∙∙-mis dd) (s-mm or) = ⅆS∙∙-mis (ⅆ-or-l dd or)
ⅆ-or-l (ⅆS^=-hit dd) (S-hm or) = ⅆS^=-hit (ⅆ-or-l dd or)
ⅆ-or-l (ⅆS^=-hit dd) (S-mh or) = ⅆS^=-mis (ⅆ-or-l dd or)
ⅆ-or-l (ⅆS^=-hit dd) (S-hh or) = ⅆS^=-hit (ⅆ-or-l dd or)
ⅆ-or-l (ⅆS^=-mis dd) (s-mm or) = ⅆS^=-mis (ⅆ-or-l dd or)
ⅆ-or-l (ⅆS^^-hit dd) (S-hm or) = ⅆS^^-hit (ⅆ-or-l dd or)
ⅆ-or-l (ⅆS^^-hit dd) (S-mh or) = ⅆS^^-mis (ⅆ-or-l dd or)
ⅆ-or-l (ⅆS^^-hit dd) (S-hh or) = ⅆS^^-hit (ⅆ-or-l dd or)
ⅆ-or-l (ⅆS^^-mis dd) (s-mm or) = ⅆS^^-mis (ⅆ-or-l dd or)
ⅆ-or-l (ⅆS==-hit dd regA) (S-hm or) = ⅆS==-hit (ⅆ-or-l dd or) regA
ⅆ-or-l (ⅆS==-hit dd regA) (S-mh or) = ⅆS==-mis-1 (ⅆ-or-l dd or) regA
ⅆ-or-l (ⅆS==-hit dd regA) (S-hh or) = ⅆS==-hit (ⅆ-or-l dd or) regA
ⅆ-or-l (ⅆS==-mis-1 dd regA) (s-mm or) = ⅆS==-mis-1 (ⅆ-or-l dd or) regA
ⅆ-or-l (ⅆS==-mis-2 dd regA) (s-mm or) = ⅆS==-mis-2 (ⅆ-or-l dd or) regA

ⅆ-or-r : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
         → orHit H₁ H₂ H
         → Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H₂
ⅆ-or-r (ⅆ⋈ regΓ) or = ⅆ⋈ regΓ
ⅆ-or-r (ⅆS∙∙-hit dd) (S-hm or) = ⅆS∙∙-mis (ⅆ-or-r dd or)
ⅆ-or-r (ⅆS∙∙-hit dd) (S-mh or) = ⅆS∙∙-hit (ⅆ-or-r dd or)
ⅆ-or-r (ⅆS∙∙-hit dd) (S-hh or) = ⅆS∙∙-hit (ⅆ-or-r dd or)
ⅆ-or-r (ⅆS∙∙-mis dd) (s-mm or) = ⅆS∙∙-mis (ⅆ-or-r dd or)
ⅆ-or-r (ⅆS^=-hit dd) (S-hm or) = ⅆS^=-mis (ⅆ-or-r dd or)
ⅆ-or-r (ⅆS^=-hit dd) (S-mh or) = ⅆS^=-hit (ⅆ-or-r dd or)
ⅆ-or-r (ⅆS^=-hit dd) (S-hh or) = ⅆS^=-hit (ⅆ-or-r dd or)
ⅆ-or-r (ⅆS^=-mis dd) (s-mm or) = ⅆS^=-mis (ⅆ-or-r dd or)
ⅆ-or-r (ⅆS^^-hit dd) (S-hm or) = ⅆS^^-mis (ⅆ-or-r dd or)
ⅆ-or-r (ⅆS^^-hit dd) (S-mh or) = ⅆS^^-hit (ⅆ-or-r dd or)
ⅆ-or-r (ⅆS^^-hit dd) (S-hh or) = ⅆS^^-hit (ⅆ-or-r dd or)
ⅆ-or-r (ⅆS^^-mis dd) (s-mm or) = ⅆS^^-mis (ⅆ-or-r dd or)
ⅆ-or-r (ⅆS==-hit dd regA) (S-hm or) = ⅆS==-mis-1 (ⅆ-or-r dd or) regA
ⅆ-or-r (ⅆS==-hit dd regA) (S-mh or) = ⅆS==-hit (ⅆ-or-r dd or) regA
ⅆ-or-r (ⅆS==-hit dd regA) (S-hh or) = ⅆS==-hit (ⅆ-or-r dd or) regA
ⅆ-or-r (ⅆS==-mis-1 dd regA) (s-mm or) = ⅆS==-mis-1 (ⅆ-or-r dd or) regA
ⅆ-or-r (ⅆS==-mis-2 dd regA) (s-mm or) = ⅆS==-mis-2 (ⅆ-or-r dd or) regA
