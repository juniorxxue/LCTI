module Implicit.Language.Extension.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.All

open import Implicit.Language.EnvOps.Base
open import Implicit.Language.Regular.Base
open import Implicit.Language.Extension.Base
open import Implicit.Language.OpenClose.Base

open import Implicit.Language.Extension.Preservation

⊆-refl : Regular Γ
       → Γ ⊆ Γ
⊆-refl reg-Z = empty
⊆-refl (reg-S, regΓ regA) = tvar (⊆-refl regΓ) regA
⊆-refl (reg-S∙ regΓ) = uvar (⊆-refl regΓ)
⊆-refl (reg-S^ regΓ) = evar (⊆-refl regΓ)
⊆-refl (reg-S= regΓ regA) = svar (⊆-refl regΓ) regA
⊆-refl (reg-S⋈ regΓ) = mark (⊆-refl regΓ)

⊆-trans : Γ ⊆ Ω
        → Ω ⊆ Δ
        → Γ ⊆ Δ
⊆-trans empty empty = empty
⊆-trans (uvar ext1) (uvar ext2) = uvar (⊆-trans ext1 ext2)
⊆-trans (evar ext1) (evar ext2) = evar (⊆-trans ext1 ext2)
⊆-trans (evar ext1) (evar-sol ext2 regA) = evar-sol (⊆-trans ext1 ext2) regA
⊆-trans (evar-sol ext1 regA) (svar ext2 regA₁) = evar-sol (⊆-trans ext1 ext2) (⊆-⊢r regA ext2)
⊆-trans (svar ext1 regA) (svar ext2 regA₁) = svar (⊆-trans ext1 ext2) regA
⊆-trans (tvar ext1 regA) (tvar ext2 regB) = tvar (⊆-trans ext1 ext2) regA
⊆-trans (mark x) (mark ext2) = mark (⊆-trans x ext2)

⊆-antisymm : Γ ⊆ Δ
           → Δ ⊆ Γ
           → Γ ≡ Δ
⊆-antisymm empty empty = refl
⊆-antisymm (uvar ext1) (uvar ext2) with refl ← ⊆-antisymm ext1 ext2 = refl
⊆-antisymm (evar ext1) (evar ext2) with refl ← ⊆-antisymm ext1 ext2 = refl
⊆-antisymm (svar ext1 regA) (svar ext2 regA₁) with refl ← ⊆-antisymm ext1 ext2 = refl
⊆-antisymm (tvar ext1 regA) (tvar ext2 regB) with refl ← ⊆-antisymm ext1 ext2 = refl
⊆-antisymm (mark x) (mark x₁) with refl ← ⊆-antisymm x x₁ = refl

reg-⊆/x∙ : Δ ∋∙ X
         → Δ ⊆ Δ w/v X
reg-⊆/x∙ Z = ext-Z∙
reg-⊆/x∙ (S, inΔ) = ext-S, (reg-⊆/x∙ inΔ)
reg-⊆/x∙ (S∙ inΔ) = ext-S∙ (reg-⊆/x∙ inΔ)
reg-⊆/x∙ (S= inΔ) = ext-S= (reg-⊆/x∙ inΔ)
reg-⊆/x∙ (S^ inΔ) = ext-S^ (reg-⊆/x∙ inΔ)
reg-⊆/x∙ (S⋈ inΔ) = ext-S⋈ (reg-⊆/x∙ inΔ)


reg-⊆/ : SRegular Δ
       → Δ ⊢r A
       → Δ ⊆ Δ w/t A
reg-⊆/ senv ⊢r-int = ext-int senv
reg-⊆/ senv (⊢r-var-∙ inΓ) = ext-var (reg-⊆/x∙ inΓ) senv senv
reg-⊆/ senv (⊢r-arr regA regA₁) = ext-arr (reg-⊆/ senv regA) (reg-⊆/ senv regA₁)
reg-⊆/ senv (⊢r-∀ regA) = ext-∀ (reg-⊆/ (reg-S∙ senv) regA)


⊆/x-∋∙-eq : Γ ⊆ Δ w/v X
          → Γ ∋∙ X
          → Γ ≡ Δ
⊆/x-∋∙-eq (ext-Z∙) Z = refl
⊆/x-∋∙-eq (ext-S^ ext) (S^ inΓ) = cong _,^ (⊆/x-∋∙-eq ext inΓ)
⊆/x-∋∙-eq (ext-S∙ ext) (S∙ inΓ) = cong _,∙ (⊆/x-∋∙-eq ext inΓ)
⊆/x-∋∙-eq (ext-S= ext) (S= inΓ) = cong₂ _,=_ (⊆/x-∋∙-eq ext inΓ) refl
⊆/x-∋∙-eq (ext-S⋈ ext) (S⋈ inΓ) = cong _⋈ (⊆/x-∋∙-eq ext inΓ)
⊆/x-∋∙-eq (ext-S, ext) (S, inΓ) = cong₂ _,_ (⊆/x-∋∙-eq ext inΓ) refl

⊆/x-∋=-eq : Γ ⊆ Δ w/v X
          → Γ ∋= X
          → Γ ≡ Δ
⊆/x-∋=-eq (ext-Z=) Z = refl
⊆/x-∋=-eq (ext-S^ ext) (S^ inΓ) = cong _,^ (⊆/x-∋=-eq ext inΓ)
⊆/x-∋=-eq (ext-S∙ ext) (S∙ inΓ) = cong _,∙ (⊆/x-∋=-eq ext inΓ)
⊆/x-∋=-eq (ext-S= ext) (S= inΓ) = cong₂ _,=_ (⊆/x-∋=-eq ext inΓ) refl
⊆/x-∋=-eq (ext-S⋈ ext) (S⋈ inΓ') = cong _⋈ (⊆/x-∋=-eq ext inΓ')
⊆/x-∋=-eq (ext-S, ext) (S, inΓ) = cong₂ _,_ (⊆/x-∋=-eq ext inΓ) refl

⊆/-⊢c-eq : Γ ⊆ Δ w/t A
         → Γ ⊢c A
         → Γ ≡ Δ
⊆/-⊢c-eq (ext-int regΓ) cloA = refl
⊆/-⊢c-eq (ext-var x reg1 reg2) (⊢c-var-∙ inΔ) = ⊆/x-∋∙-eq x inΔ
⊆/-⊢c-eq (ext-var x reg1 reg2) (⊢c-var-= inΔ) = ⊆/x-∋=-eq x inΔ
⊆/-⊢c-eq (ext-arr ext ext₁) (⊢c-arr cloA cloA₁)
  with refl ← ⊆/-⊢c-eq ext cloA
  with refl ← ⊆/-⊢c-eq ext₁ cloA₁ = refl
⊆/-⊢c-eq (ext-∀ ext) (⊢c-∀ cloA)
  with refl ← ⊆/-⊢c-eq ext cloA = refl

⊆/-∙out-∙in : Δ ∋∙ X
            → Γ ⊆ Δ w/v X
            → Γ ∋∙ X
⊆/-∙out-∙in Z (ext-Z∙) = Z
⊆/-∙out-∙in (S∙ inΓ) (ext-S∙ ext) = S∙ (⊆/-∙out-∙in inΓ ext)
⊆/-∙out-∙in (S= inΓ) (ext-S= ext) = S= (⊆/-∙out-∙in inΓ ext)
⊆/-∙out-∙in (S^ inΓ) (ext-S^ ext) = S^ (⊆/-∙out-∙in inΓ ext)
⊆/-∙out-∙in (S⋈ inΓ) (ext-S⋈ ext) = S⋈ (⊆/-∙out-∙in inΓ ext)
⊆/-∙out-∙in (S, inΓ) (ext-S, ext) = S, (⊆/-∙out-∙in inΓ ext)

----------------------------------------------------------------------
--+             restricted extension implies extension             +--
----------------------------------------------------------------------

⊆/x-⊆ : Regular Γ
      → Regular Δ
      → Γ ⊆ Δ w/v X
      → Γ ⊆ Δ
⊆/x-⊆ (reg-S, reg1 regA) (reg-S, reg2 regA₁) (ext-S, ext) = tvar (⊆/x-⊆ reg1 reg2 ext) regA
⊆/x-⊆ (reg-S∙ reg1) (reg-S∙ reg2) ext-Z∙ = ⊆-refl (reg-S∙ reg1)
⊆/x-⊆ (reg-S∙ reg1) (reg-S∙ reg2) (ext-S∙ ext) = uvar (⊆/x-⊆ reg1 reg2 ext)
⊆/x-⊆ (reg-S^ reg1) (reg-S= reg2 regA) ext-Z^ = evar-sol (⊆-refl reg1) regA
⊆/x-⊆ (reg-S^ reg1) (reg-S^ reg2) (ext-S^ ext) = evar (⊆/x-⊆ reg1 reg2 ext)
⊆/x-⊆ (reg-S= reg1 regA) (reg-S= reg2 regA₁) ext-Z= = ⊆-refl (reg-S= reg1 regA₁)
⊆/x-⊆ (reg-S= reg1 regA) (reg-S= reg2 regA₁) (ext-S= ext) = svar (⊆/x-⊆ reg1 reg2 ext) regA
⊆/x-⊆ (reg-S⋈ reg1) (reg-S⋈ reg2) (ext-S⋈ ext) = mark (⊆/x-⊆ reg1 reg2 ext)


⊆/-⊆ : Γ ⊆ Δ w/t A
     → Γ ⊆ Δ
⊆/-⊆ (ext-int regΓ) = ⊆-refl (sreg-reg regΓ)
⊆/-⊆ (ext-var ext reg1 reg2) = ⊆/x-⊆ (sreg-reg reg1) (sreg-reg reg2) ext
⊆/-⊆ (ext-arr ext ext₁) = ⊆-trans (⊆/-⊆ ext) (⊆/-⊆ ext₁)
⊆/-⊆ (ext-∀ ext) with ⊆/-⊆ ext
... | uvar r = r


⊆/x-∋∙-refl : Γ ∋∙ X
       → Γ ⊆ Γ w/v X
⊆/x-∋∙-refl Z = ext-Z∙
⊆/x-∋∙-refl (S, in1) = ext-S, (⊆/x-∋∙-refl in1)
⊆/x-∋∙-refl (S∙ in1) = ext-S∙ (⊆/x-∋∙-refl in1)
⊆/x-∋∙-refl (S= in1) = ext-S= (⊆/x-∋∙-refl in1)
⊆/x-∋∙-refl (S^ in1) = ext-S^ (⊆/x-∋∙-refl in1)
⊆/x-∋∙-refl (S⋈ in1) = ext-S⋈ (⊆/x-∋∙-refl in1)


⊆/x-∋=-refl : Γ ∋= X
       → Γ ⊆ Γ w/v X
⊆/x-∋=-refl Z = ext-Z=
⊆/x-∋=-refl (S∙ in1) = ext-S∙ (⊆/x-∋=-refl in1)
⊆/x-∋=-refl (S^ in1) = ext-S^ (⊆/x-∋=-refl in1)
⊆/x-∋=-refl (S= in1) = ext-S= (⊆/x-∋=-refl in1)
⊆/x-∋=-refl (S, in1) = ext-S, (⊆/x-∋=-refl in1)
⊆/x-∋=-refl (S⋈ in1) = ext-S⋈ (⊆/x-∋=-refl in1)


⊆/-refl : SRegular Γ
       → Γ ⊢c A
       → Γ ⊆ Γ w/t A
⊆/-refl regΓ ⊢c-int = ext-int regΓ
⊆/-refl regΓ (⊢c-var-∙ inΔ) = ext-var (⊆/x-∋∙-refl inΔ) regΓ regΓ
⊆/-refl regΓ (⊢c-var-= inΔ) = ext-var (⊆/x-∋=-refl inΔ) regΓ regΓ
⊆/-refl regΓ (⊢c-arr cloA cloA₁) = ext-arr (⊆/-refl regΓ cloA) (⊆/-refl regΓ cloA₁)
⊆/-refl regΓ (⊢c-∀ cloA) = ext-∀ (⊆/-refl (reg-S∙ regΓ) cloA)

⊆/x-⊢c : Γ ⊆ Δ w/v X
       → Δ ⊢c ‶ X
⊆/x-⊢c ext-Z^ = ⊢c-var-= Z
⊆/x-⊢c ext-Z∙ = ⊢c-var-∙ Z
⊆/x-⊢c ext-Z= = ⊢c-var-= Z
⊆/x-⊢c (ext-S^ ext) with ⊆/x-⊢c ext
... | ⊢c-var-∙ inΔ = ⊢c-var-∙ (S^ inΔ)
... | ⊢c-var-= inΔ = ⊢c-var-= (S^ inΔ)
⊆/x-⊢c (ext-S∙ ext) with ⊆/x-⊢c ext
... | ⊢c-var-∙ inΔ = ⊢c-var-∙ (S∙ inΔ)
... | ⊢c-var-= inΔ = ⊢c-var-= (S∙ inΔ)
⊆/x-⊢c (ext-S= ext) with ⊆/x-⊢c ext
... | ⊢c-var-∙ inΔ = ⊢c-var-∙ (S= inΔ)
... | ⊢c-var-= inΔ = ⊢c-var-= (S= inΔ)
⊆/x-⊢c (ext-S⋈ ext) with ⊆/x-⊢c ext
... | ⊢c-var-∙ inΔ = ⊢c-var-∙ (S⋈ inΔ)
... | ⊢c-var-= inΔ = ⊢c-var-= (S⋈ inΔ)
⊆/x-⊢c (ext-S, ext) with ⊆/x-⊢c ext
... | ⊢c-var-∙ inΔ = ⊢c-var-∙ (S, inΔ)
... | ⊢c-var-= inΔ = ⊢c-var-= (S, inΔ)

⊆/-⊢c : Γ ⊆ Δ w/t A
      → Δ ⊢c A
⊆/-⊢c (ext-int x) = ⊢c-int
⊆/-⊢c (ext-var ext reg1 reg2) = ⊆/x-⊢c ext
⊆/-⊢c (ext-arr ext ext₁) = ⊢c-arr (⊆-⊢c (⊆/-⊢c ext) (⊆/-⊆ ext₁)) (⊆/-⊢c ext₁)
⊆/-⊢c (ext-∀ ext) = ⊢c-∀ (⊆/-⊢c ext)


-- could be proved via a inst-total
-- however, the total requires a condition: B is shifted k times, which is a tricky to define in well-scoped settings: finite nubmers
inst-exist : [ B / k ] Δ =⟹ Δ'
           → Ω ⊆ Δ
           → Ω ∋= k
           → ∃[ Ω' ]( [ B / k ] Ω =⟹ Ω')
inst-exist (=⟹=0  {A = A} up regA' regΓ) (svar {Γ = Γ} ext regA) Z = ⟨ Γ ,= A , =⟹=0 up (⊆-⊢r' regA' ext) (⊆-sregular' regΓ ext) ⟩
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
inst-exist' (=⟹=0 {A = A} up regA' reΓ) (svar {Δ = Δ} ext regA) = ⟨ Δ ,= A , =⟹=0 up (⊆-⊢r regA' ext) (⊆-sregular reΓ ext) ⟩
inst-exist' (=⟹^S inst up1) (evar ext) = ⟨ inst-exist' inst ext .proj₁ ,^ ,
                                          =⟹^S (inst-exist' inst ext .proj₂) up1 ⟩
inst-exist' (=⟹^S inst up1) (evar-sol {A = A} ext regA) = ⟨ inst-exist' inst ext .proj₁ ,= A ,
                                                   =⟹=S (inst-exist' inst ext .proj₂) up1 regA ⟩
inst-exist' (=⟹∙S inst up1) (uvar ext) = ⟨ inst-exist' inst ext .proj₁ ,∙ ,
                                          =⟹∙S (inst-exist' inst ext .proj₂) up1 ⟩
inst-exist' (=⟹=S inst up1 regB) (svar {A = A} ext regA) = ⟨ inst-exist' inst ext .proj₁ ,= A ,
                                               =⟹=S (inst-exist' inst ext .proj₂) up1 (⊆-⊢r regB ext) ⟩
