module Implicit.AuxLemmas where

open import Implicit.Language.All


-- could be proved via a inst-total
-- however, the total requires a condition: B is shifted k times, which is a tricky to define in well-scoped settings: finite nubmers
inst-exist : [ B / k ] Δ =⟹ Δ'
           → Ω ⊆ Δ
           → Ω ∋= k
           → ∃[ Ω' ]( [ B / k ] Ω =⟹ Ω')
inst-exist (=⟹=0  {A = A} up regA' regΓ) (svar {Γ = Γ} ext regA) Z = ⟨ Γ ,= A , =⟹=0 up (⊆-⊢r' regA' ext) (⊆-regular' regΓ ext) ⟩
inst-exist (=⟹^S inst up1) (evar ext) (S^ inΩ) = ⟨ inst-exist inst ext inΩ .proj₁ ,^ ,
                                                  =⟹^S (inst-exist inst ext inΩ .proj₂) up1 ⟩
inst-exist (=⟹∙S inst up1) (uvar ext) (S∙ inΩ) = ⟨ inst-exist inst ext inΩ .proj₁ ,∙ ,
                                                  =⟹∙S (inst-exist inst ext inΩ .proj₂) up1 ⟩
inst-exist (=⟹=S inst up1 regB) (evar-sol ext regA) (S^ inΩ) = ⟨ inst-exist inst ext inΩ .proj₁ ,^ ,
                                                           =⟹^S (inst-exist inst ext inΩ .proj₂) up1 ⟩
inst-exist (=⟹=S inst up1 regB) (svar {A = A} ext regA) (S= inΩ) = ⟨ inst-exist inst ext inΩ .proj₁ ,= A ,
                                                       =⟹=S (inst-exist inst ext inΩ .proj₂) up1 regA ⟩

inst-exist' : [ B / k ] Γ =⟹ Γ'
            → Γ ⊆ Ω
            → ∃[ Ω' ]( [ B / k ] Ω =⟹ Ω')
inst-exist' (=⟹=0 {A = A} up regA' reΓ) (svar {Δ = Δ} ext regA) = ⟨ Δ ,= A , =⟹=0 up (⊆-⊢r regA' ext) (⊆-regular reΓ ext) ⟩
inst-exist' (=⟹^S inst up1) (evar ext) = ⟨ inst-exist' inst ext .proj₁ ,^ ,
                                          =⟹^S (inst-exist' inst ext .proj₂) up1 ⟩
inst-exist' (=⟹^S inst up1) (evar-sol {A = A} ext regA) = ⟨ inst-exist' inst ext .proj₁ ,= A ,
                                                   =⟹=S (inst-exist' inst ext .proj₂) up1 regA ⟩
inst-exist' (=⟹∙S inst up1) (uvar ext) = ⟨ inst-exist' inst ext .proj₁ ,∙ ,
                                          =⟹∙S (inst-exist' inst ext .proj₂) up1 ⟩
inst-exist' (=⟹=S inst up1 regB) (svar {A = A} ext regA) = ⟨ inst-exist' inst ext .proj₁ ,= A ,
                                               =⟹=S (inst-exist' inst ext .proj₂) up1 (⊆-⊢r regB ext) ⟩



data HitMis : ℕ → Set where
  ∅ : HitMis 0
  hit : HitMis m → HitMis (1 + m)
  mis : HitMis m → HitMis (1 + m)

variable
  H H₁ H₂ : HitMis m

mkMis : ∀ {m} → HitMis m
mkMis {zero} = ∅
mkMis {suc m} = mis (mkMis {m})

mkHit : ∀ {m} → Fin m → HitMis m
mkHit {suc m} #0 = hit (mkMis {m})
mkHit {suc m} (#S k) = mis (mkHit {m} k)

data orHit : HitMis m → HitMis m → HitMis m → Set where
  Z : orHit ∅ ∅ ∅
  S-hm : orHit H₁ H₂ H
    → orHit (hit H₁) (mis H₂) (hit H)
  S-mh : orHit H₁ H₂ H
    → orHit (mis H₁) (hit H₂) (hit H)
  S-hh : orHit H₁ H₂ H
    → orHit (hit H₁) (hit H₂) (hit H)
  s-mm : orHit H₁ H₂ H
    → orHit (mis H₁) (mis H₂) (mis H)

orHit-total : ∀ (H₁ H₂ : HitMis m)
  → ∃[ H ](orHit H₁ H₂ H)
orHit-total ∅ ∅ = ⟨ ∅ , Z ⟩
orHit-total (hit H₁) (hit H₂) = ⟨ hit (orHit-total H₁ H₂ .proj₁) , S-hh (orHit-total H₁ H₂ .proj₂) ⟩
orHit-total (hit H₁) (mis H₂) = ⟨ hit (orHit-total H₁ H₂ .proj₁) , S-hm (orHit-total H₁ H₂ .proj₂) ⟩
orHit-total (mis H₁) (hit H₂) = ⟨ hit (orHit-total H₁ H₂ .proj₁) , S-mh (orHit-total H₁ H₂ .proj₂) ⟩
orHit-total (mis H₁) (mis H₂) = ⟨ mis (orHit-total H₁ H₂ .proj₁) , s-mm (orHit-total H₁ H₂ .proj₂) ⟩

infix 3 _𝕗𝕧_
data _𝕗𝕧_ : Type m → HitMis m → Set where
  fv-Int : ∀ {m} → (Type m ∋⦂ Int) 𝕗𝕧 mkMis {m}
  fv-var : (‶ X) 𝕗𝕧 mkHit X
  fv-arr : A 𝕗𝕧 H₁
         → B 𝕗𝕧 H₂
         → orHit H₁ H₂ H
         → A `→ B 𝕗𝕧 H
  fv-∀-h : A 𝕗𝕧 (hit H)
         → `∀ A 𝕗𝕧 H
  fv-∀-m : A 𝕗𝕧 (mis H)
         → `∀ A 𝕗𝕧 H

𝕗𝕧-total : ∀ {m} (A : Type m)
         → ∃[ H ](A 𝕗𝕧 H)
𝕗𝕧-total {m} Int = ⟨ mkMis , fv-Int ⟩
𝕗𝕧-total (‶ X) = ⟨ mkHit X , fv-var ⟩
𝕗𝕧-total (A `→ B)
  with ⟨ H1 , fv1 ⟩ ← 𝕗𝕧-total A
  with ⟨ H2 , fv2 ⟩ ← 𝕗𝕧-total B
  with ⟨ H , or-hit ⟩ ← orHit-total H1 H2
  = ⟨ H , fv-arr fv1 fv2 or-hit ⟩
𝕗𝕧-total (`∀ A) with 𝕗𝕧-total A
... | ⟨ hit H , fv ⟩ = ⟨ H , fv-∀-h fv ⟩
... | ⟨ mis H , fv ⟩ = ⟨ H , fv-∀-m fv ⟩

infix 3 _ⅆ_⊆_ⅆ_kp_
data _ⅆ_⊆_ⅆ_kp_ : Env n m → Env n m → Env n m → Env n m → HitMis m → Set where
  ⅆ⋈ : (regΓ : TRegular Γ)
     → Γ ⋈ ⅆ Γ ⋈ ⊆ Γ ⋈ ⅆ Γ ⋈ kp H
  ⅆS∙∙-hit : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
          → Γ ,∙ ⅆ Γ' ,∙ ⊆ Δ ,∙ ⅆ Δ' ,∙ kp (hit H)
  ⅆS∙∙-mis : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
          → Γ ,∙ ⅆ Γ' ,∙ ⊆ Δ ,∙ ⅆ Δ' ,∙ kp (mis H)
  ⅆS^=-hit : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
           → (regA : Δ ⊢r A)
           → Γ ,^ ⅆ Γ' ,^ ⊆ Δ ,= A ⅆ Δ' ,= A kp (hit H)
  ⅆS^=-mis : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
           → (regA : Δ ⊢r A)
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


ⅆk-⊆ : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
    → Γ ⊆ Δ
ⅆk-⊆ (ⅆ⋈ regΓ) = mark regΓ
ⅆk-⊆ (ⅆS∙∙-hit dd) = uvar (ⅆk-⊆ dd)
ⅆk-⊆ (ⅆS∙∙-mis dd) = uvar (ⅆk-⊆ dd)
ⅆk-⊆ (ⅆS^=-hit dd regA) = evar-sol (ⅆk-⊆ dd) regA
ⅆk-⊆ (ⅆS^=-mis dd regA) = evar-sol (ⅆk-⊆ dd) regA
ⅆk-⊆ (ⅆS^^-hit dd) = evar (ⅆk-⊆ dd)
ⅆk-⊆ (ⅆS^^-mis dd) = evar (ⅆk-⊆ dd)
ⅆk-⊆ (ⅆS==-hit dd regA) = svar (ⅆk-⊆ dd) regA
ⅆk-⊆ (ⅆS==-mis-1 dd regA) = svar (ⅆk-⊆ dd) regA
ⅆk-⊆ (ⅆS==-mis-2 dd regA) = svar (ⅆk-⊆ dd) regA

ⅆk-⊆-l : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
      → Γ' ⊆ Γ
ⅆk-⊆-l (ⅆ⋈ regΓ) = mark regΓ
ⅆk-⊆-l (ⅆS∙∙-hit dd) = uvar (ⅆk-⊆-l dd)
ⅆk-⊆-l (ⅆS∙∙-mis dd) = uvar (ⅆk-⊆-l dd)
ⅆk-⊆-l (ⅆS^=-hit dd regA) = evar (ⅆk-⊆-l dd)
ⅆk-⊆-l (ⅆS^=-mis dd regA) = evar (ⅆk-⊆-l dd)
ⅆk-⊆-l (ⅆS^^-hit dd) = evar (ⅆk-⊆-l dd)
ⅆk-⊆-l (ⅆS^^-mis dd) = evar (ⅆk-⊆-l dd)
ⅆk-⊆-l (ⅆS==-hit dd regA) = svar (ⅆk-⊆-l dd) (⊆-⊢r' regA (ⅆk-⊆-l dd))
ⅆk-⊆-l (ⅆS==-mis-1 dd regA) = svar (ⅆk-⊆-l dd) (⊆-⊢r' regA (ⅆk-⊆-l dd))
ⅆk-⊆-l (ⅆS==-mis-2 dd regA) = evar-sol (ⅆk-⊆-l dd) regA


ⅆk-⊆-r : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
      → Δ' ⊆ Δ
ⅆk-⊆-r (ⅆ⋈ regΓ) = mark regΓ
ⅆk-⊆-r (ⅆS∙∙-hit dd) = uvar (ⅆk-⊆-r dd)
ⅆk-⊆-r (ⅆS∙∙-mis dd) = uvar (ⅆk-⊆-r dd)
ⅆk-⊆-r (ⅆS^=-hit dd regA) = svar (ⅆk-⊆-r dd) (⊆-⊢r' regA (ⅆk-⊆-r dd))
ⅆk-⊆-r (ⅆS^=-mis dd regA) = svar (ⅆk-⊆-r dd) (⊆-⊢r' regA (ⅆk-⊆-r dd))
ⅆk-⊆-r (ⅆS^^-hit dd) = evar (ⅆk-⊆-r dd)
ⅆk-⊆-r (ⅆS^^-mis dd) = evar (ⅆk-⊆-r dd)
ⅆk-⊆-r (ⅆS==-hit dd regA) = svar (ⅆk-⊆-r dd) (⊆-⊢r' (⊆-⊢r regA (ⅆk-⊆ dd)) (ⅆk-⊆-r dd))
ⅆk-⊆-r (ⅆS==-mis-1 dd regA) = svar (ⅆk-⊆-r dd) (⊆-⊢r' (⊆-⊢r regA (ⅆk-⊆ dd)) (ⅆk-⊆-r dd))
ⅆk-⊆-r (ⅆS==-mis-2 dd regA) = evar-sol (ⅆk-⊆-r dd) (⊆-⊢r regA (ⅆk-⊆ dd))

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
ⅆk-or-l (ⅆS^=-hit dd regA) (S-hm or) = ⅆS^=-hit (ⅆk-or-l dd or) regA
ⅆk-or-l (ⅆS^=-hit dd regA) (S-mh or) = ⅆS^=-mis (ⅆk-or-l dd or) regA
ⅆk-or-l (ⅆS^=-hit dd regA) (S-hh or) = ⅆS^=-hit (ⅆk-or-l dd or) regA
ⅆk-or-l (ⅆS^=-mis dd regA) (s-mm or) = ⅆS^=-mis (ⅆk-or-l dd or) regA
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
ⅆk-or-r (ⅆS^=-hit dd regA) (S-hm or) = ⅆS^=-mis (ⅆk-or-r dd or) regA
ⅆk-or-r (ⅆS^=-hit dd regA) (S-mh or) = ⅆS^=-hit (ⅆk-or-r dd or) regA
ⅆk-or-r (ⅆS^=-hit dd regA) (S-hh or) = ⅆS^=-hit (ⅆk-or-r dd or) regA
ⅆk-or-r (ⅆS^=-mis dd regA) (s-mm or) = ⅆS^=-mis (ⅆk-or-r dd or) regA
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

ⅆk-∋∙-r : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
      → H ≡ mkHit X
      → Δ ∋∙ X
      → Δ' ∋∙ X
ⅆk-∋∙-r (ⅆ⋈ regΓ) refl inΔ = inΔ
ⅆk-∋∙-r (ⅆS∙∙-hit dd) eq Z = Z
ⅆk-∋∙-r (ⅆS∙∙-mis dd) refl (S∙ inΔ) = S∙ (ⅆk-∋∙-r dd refl inΔ)
ⅆk-∋∙-r (ⅆS^=-hit dd regA) () (S= inΔ)
ⅆk-∋∙-r (ⅆS^=-mis dd regA) refl (S= inΔ) = S= (ⅆk-∋∙-r dd refl inΔ)
ⅆk-∋∙-r (ⅆS^^-hit dd) () (S^ inΔ)
ⅆk-∋∙-r (ⅆS^^-mis dd) refl (S^ inΔ) = S^ (ⅆk-∋∙-r dd refl inΔ)
ⅆk-∋∙-r (ⅆS==-hit dd regA) () (S= inΔ)
ⅆk-∋∙-r (ⅆS==-mis-1 dd regA) refl (S= inΔ) = S= (ⅆk-∋∙-r dd refl inΔ)
ⅆk-∋∙-r (ⅆS==-mis-2 dd regA) refl (S= inΔ) = S^ (ⅆk-∋∙-r dd refl inΔ)

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

ⅆk-∋=-r : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
      → H ≡ mkHit X
      → Δ ∋= X
      → Δ' ∋= X
ⅆk-∋=-r (ⅆS∙∙-hit dd) () (S∙ inΔ)
ⅆk-∋=-r (ⅆS∙∙-mis dd) refl (S∙ inΔ) = S∙ (ⅆk-∋=-r dd refl inΔ)
ⅆk-∋=-r (ⅆS^=-hit dd regA) eq Z = Z
ⅆk-∋=-r (ⅆS^=-mis dd regA) refl (S= inΔ) = S= (ⅆk-∋=-r dd refl inΔ)
ⅆk-∋=-r (ⅆS^^-hit dd) () (S^ inΔ)
ⅆk-∋=-r (ⅆS^^-mis dd) refl (S^ inΔ) = S^ (ⅆk-∋=-r dd refl inΔ)
ⅆk-∋=-r (ⅆS==-hit dd regA) eq Z = Z
ⅆk-∋=-r (ⅆS==-mis-1 dd regA) refl (S= inΔ) = S= (ⅆk-∋=-r dd refl inΔ)
ⅆk-∋=-r (ⅆS==-mis-2 dd regA) refl (S= inΔ) = S^ (ⅆk-∋=-r dd refl inΔ)

ⅆk-∋:=-r : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
      → H ≡ mkHit X
      → Δ ∋ X := A
      → Δ' ∋ X := A
ⅆk-∋:=-r (ⅆS∙∙-hit dd) () (S∙ inΔ up)
ⅆk-∋:=-r (ⅆS∙∙-mis dd) refl (S∙ inΔ up) = S∙ (ⅆk-∋:=-r dd refl inΔ) up
ⅆk-∋:=-r (ⅆS^=-hit dd regA) refl (Z up) = Z up
ⅆk-∋:=-r (ⅆS^=-mis dd regA) refl (S= inΔ up) = S= (ⅆk-∋:=-r dd refl inΔ) up
ⅆk-∋:=-r (ⅆS^^-hit dd) () (S^ inΔ up)
ⅆk-∋:=-r (ⅆS^^-mis dd) refl (S^ inΔ up) = S^ (ⅆk-∋:=-r dd refl inΔ) up
ⅆk-∋:=-r (ⅆS==-hit dd regA) refl (Z up) = Z up
ⅆk-∋:=-r (ⅆS==-mis-1 dd regA) refl (S= inΔ up) = S= (ⅆk-∋:=-r dd refl inΔ) up
ⅆk-∋:=-r (ⅆS==-mis-2 dd regA) refl (S= inΔ up) = S^ (ⅆk-∋:=-r dd refl inΔ) up

ⅆk-∋^-r : Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
      → H ≡ mkHit X
      → Δ ∋^ X
      → Δ' ∋^ X
ⅆk-∋^-r (ⅆS∙∙-hit dd) () (S∙ inΔ)
ⅆk-∋^-r (ⅆS∙∙-mis dd) refl (S∙ inΔ) = S∙ (ⅆk-∋^-r dd refl inΔ)
ⅆk-∋^-r (ⅆS^=-hit dd regA) () (S= inΔ)
ⅆk-∋^-r (ⅆS^=-mis dd regA) refl (S= inΔ) = S= (ⅆk-∋^-r dd refl inΔ)
ⅆk-∋^-r (ⅆS^^-hit dd) refl Z = Z
ⅆk-∋^-r (ⅆS^^-mis dd) refl (S^ inΔ) = S^ (ⅆk-∋^-r dd refl inΔ)
ⅆk-∋^-r (ⅆS==-hit dd regA) () (S= inΔ)
ⅆk-∋^-r (ⅆS==-mis-1 dd regA) refl (S= inΔ) = S= (ⅆk-∋^-r dd refl inΔ)
ⅆk-∋^-r (ⅆS==-mis-2 dd regA) refl (S= inΔ) = S^ (ⅆk-∋^-r dd refl inΔ)


ⅆk-⊢c-r : Δ ⊢c A
       → A 𝕗𝕧 H
       → Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
       → Δ' ⊢c A
ⅆk-⊢c-r ⊢c-int fv dd = ⊢c-int
ⅆk-⊢c-r (⊢c-var-∙ inΔ) fv-var dd = ⊢c-var-∙ (ⅆk-∋∙-r dd refl inΔ)
ⅆk-⊢c-r (⊢c-var-= inΔ) fv-var dd = ⊢c-var-= (ⅆk-∋=-r dd refl inΔ)
ⅆk-⊢c-r (⊢c-arr cloA cloA₁) (fv-arr fv fv₁ x) dd = ⊢c-arr (ⅆk-⊢c-r cloA fv (ⅆk-or-l dd x)) (ⅆk-⊢c-r cloA₁ fv₁ (ⅆk-or-r dd x))
ⅆk-⊢c-r (⊢c-∀ cloA) (fv-∀-h fv) dd = ⊢c-∀ (ⅆk-⊢c-r cloA fv (ⅆS∙∙-hit dd))
ⅆk-⊢c-r (⊢c-∀ cloA) (fv-∀-m fv) dd = ⊢c-∀ (ⅆk-⊢c-r cloA fv (ⅆS∙∙-mis dd))


ⅆk-⊢o-r : Δ ⊢o A
       → A 𝕗𝕧 H
       → Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
       → Δ' ⊢o A
ⅆk-⊢o-r (⊢o-var-^ x) fv-var dd = ⊢o-var-^ (ⅆk-∋^-r dd refl x)
ⅆk-⊢o-r (⊢o-arr-l opnA) (fv-arr fv fv₁ x) dd = ⊢o-arr-l (ⅆk-⊢o-r opnA fv (ⅆk-or-l dd x))
ⅆk-⊢o-r (⊢o-arr-r opnA) (fv-arr fv fv₁ x) dd = ⊢o-arr-r (ⅆk-⊢o-r opnA fv₁ (ⅆk-or-r dd x))
ⅆk-⊢o-r (⊢o-∀ opnA) (fv-∀-h fv) dd = ⊢o-∀ (ⅆk-⊢o-r opnA fv (ⅆS∙∙-hit dd))
ⅆk-⊢o-r (⊢o-∀ opnA) (fv-∀-m fv) dd = ⊢o-∀ (ⅆk-⊢o-r opnA fv (ⅆS∙∙-mis dd))

ⅆk-≫-r : Δ ≫ A ⇘ B
       → A 𝕗𝕧 H
       → Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
       → Δ' ≫ A ⇘ B
ⅆk-≫-r grd-int fv-Int dd = grd-int
ⅆk-≫-r (grd-var= x) fv-var dd = grd-var= (ⅆk-∋:=-r dd refl x)
ⅆk-≫-r (grd-var∙ x) fv-var dd = grd-var∙ (ⅆk-∋∙-r dd refl x)
ⅆk-≫-r (grd-arr grd grd₁) (fv-arr fv fv₁ x) dd = grd-arr (ⅆk-≫-r grd fv (ⅆk-or-l dd x)) (ⅆk-≫-r grd₁ fv₁ (ⅆk-or-r dd x))
ⅆk-≫-r (grd-∀ grd) (fv-∀-h fv) dd = grd-∀ (ⅆk-≫-r grd fv (ⅆS∙∙-hit dd))
ⅆk-≫-r (grd-∀ grd) (fv-∀-m fv) dd = grd-∀ (ⅆk-≫-r grd fv (ⅆS∙∙-mis dd))
