module Implicit.Language.Extension.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.All

open import Implicit.Language.EnvOps.Base
open import Implicit.Language.Regular.Base

open import Implicit.Language.Extension.Base

open import Implicit.Language.OpenClose.Base

⊆-refl-regular : TRegular Γ
               → Γ ⊆ Γ
⊆-refl-regular reg-Z = empty
⊆-refl-regular (reg-S, regΓ regA) = tvar (⊆-refl-regular regΓ) regA
⊆-refl-regular (reg-S∙ regΓ) = uvar (⊆-refl-regular regΓ)
⊆-refl-regular (reg-S^ regΓ) = evar (⊆-refl-regular regΓ)
⊆-refl-regular (reg-S= regΓ regA) = svar (⊆-refl-regular regΓ) regA

⊆-refl : SRegular Γ
       → Γ ⊆ Γ
⊆-refl (reg-Z regΓ) = mark (⊆-refl-regular regΓ)
⊆-refl (reg-S∙ senv) = uvar (⊆-refl senv)
⊆-refl (reg-S^ senv) = evar (⊆-refl senv)
⊆-refl (reg-S= senv regA) = svar (⊆-refl senv) regA

⊆-∋∙ : Γ ∋∙ X
     → Γ ⊆ Δ
     → Δ ∋∙ X
⊆-∋∙ Z (uvar ext) = Z
⊆-∋∙ (S∙ inΓ) (uvar ext) = S∙ (⊆-∋∙ inΓ ext)
⊆-∋∙ (S= inΓ) (svar ext regA) = S= (⊆-∋∙ inΓ ext)
⊆-∋∙ (S^ inΓ) (evar ext) = S^ (⊆-∋∙ inΓ ext)
⊆-∋∙ (S^ inΓ) (evar-sol ext regA) = S= (⊆-∋∙ inΓ ext)
⊆-∋∙ (S⋈ inΓ) (mark x) = S⋈ (⊆-∋∙ inΓ x)
⊆-∋∙ (S, inΓ) (tvar ext regA) = S, (⊆-∋∙ inΓ ext)

⊆-∋:= : Γ ∋ X := A
      → Γ ⊆ Δ
      → Δ ∋ X := A
⊆-∋:= (Z up) (svar ext regA) = Z up
⊆-∋:= (S∙ inΓ up) (uvar ext) = S∙ (⊆-∋:= inΓ ext) up
⊆-∋:= (S^ inΓ up) (evar ext) = S^ (⊆-∋:= inΓ ext) up
⊆-∋:= (S^ inΓ up) (evar-sol ext regA) = S= (⊆-∋:= inΓ ext) up
⊆-∋:= (S= inΓ up) (svar ext regA) = S= (⊆-∋:= inΓ ext) up

⊆-∋= : Γ ∋= X
     → Γ ⊆ Δ
     → Δ ∋= X
⊆-∋= Z (svar ext regA) = Z
⊆-∋= (S∙ inΓ) (uvar ext) = S∙ (⊆-∋= inΓ ext)
⊆-∋= (S^ inΓ) (evar ext) = S^ (⊆-∋= inΓ ext)
⊆-∋= (S^ inΓ) (evar-sol ext regA) = S= (⊆-∋= inΓ ext)
⊆-∋= (S= inΓ) (svar ext regA) = S= (⊆-∋= inΓ ext)

⊆-∋∙' : Δ ∋∙ X
      → Γ ⊆ Δ
      → Γ ∋∙ X
⊆-∋∙' Z (uvar ext) = Z
⊆-∋∙' (S∙ inΔ) (uvar ext) = S∙ (⊆-∋∙' inΔ ext)
⊆-∋∙' (S= inΔ) (evar-sol ext regA) = S^ (⊆-∋∙' inΔ ext)
⊆-∋∙' (S= inΔ) (svar ext regA) = S= (⊆-∋∙' inΔ ext)
⊆-∋∙' (S^ inΔ) (evar ext) = S^ (⊆-∋∙' inΔ ext)
⊆-∋∙' (S⋈ inΔ) (mark x) = S⋈ (⊆-∋∙' inΔ x)

⊆-⊢r : Γ ⊢r A
     → Γ ⊆ Δ
     → Δ ⊢r A
⊆-⊢r ⊢r-int ext = ⊢r-int
⊆-⊢r (⊢r-var-∙ inΓ) ext = ⊢r-var-∙ (⊆-∋∙ inΓ ext)
⊆-⊢r (⊢r-arr regA regA₁) ext = ⊢r-arr (⊆-⊢r regA ext) (⊆-⊢r regA₁ ext)
⊆-⊢r (⊢r-∀ regA) ext = ⊢r-∀ (⊆-⊢r regA (uvar ext))

-- ⊆-⊢c : Γ ⊢c A
--      → Γ ⊆ Δ
--      → Δ ⊢c A
-- ⊆-⊢c ⊢c-int ext = ⊢c-int
-- ⊆-⊢c (⊢c-var-∙ inΔ) ext = ⊢c-var-∙ (⊆-∋∙ inΔ ext)
-- ⊆-⊢c (⊢c-var-= inΔ) ext = ⊢c-var-= (⊆-∋= inΔ ext)
-- ⊆-⊢c (⊢c-arr cloA cloA₁) ext = ⊢c-arr (⊆-⊢c cloA ext) (⊆-⊢c cloA₁ ext)
-- ⊆-⊢c (⊢c-∀ cloA) ext = ⊢c-∀ (⊆-⊢c cloA (uvar ext))

-- ⊆-⊢r' : Δ ⊢r A
--       → Γ ⊆ Δ
--       → Γ ⊢r A
-- ⊆-⊢r' ⊢r-int ext = ⊢r-int
-- ⊆-⊢r' (⊢r-var-∙ inΓ) ext = ⊢r-var-∙ (⊆-∋∙' inΓ ext)
-- ⊆-⊢r' (⊢r-arr regA regA₁) ext = ⊢r-arr (⊆-⊢r' regA ext) (⊆-⊢r' regA₁ ext)
-- ⊆-⊢r' (⊢r-∀ regA) ext = ⊢r-∀ (⊆-⊢r' regA (uvar ext))

-- ⊆-trans : Γ ⊆ Ω
--         → Ω ⊆ Δ
--         → Γ ⊆ Δ
-- ⊆-trans (uvar ext1) (uvar ext2) = uvar (⊆-trans ext1 ext2)
-- ⊆-trans (evar ext1) (evar ext2) = evar (⊆-trans ext1 ext2)
-- ⊆-trans (evar ext1) (evar-sol ext2 regA) = evar-sol (⊆-trans ext1 ext2) regA
-- ⊆-trans (evar-sol ext1 regA) (svar ext2 regA₁) = evar-sol (⊆-trans ext1 ext2) (⊆-⊢r regA ext2)
-- ⊆-trans (svar ext1 regA) (svar ext2 regA₁) = svar (⊆-trans ext1 ext2) regA
-- ⊆-trans (mark x) ext2 = {!!}

-- ⊆-antisymm : Γ ⊆ Δ
--            → Δ ⊆ Γ
--            → Γ ≡ Δ
-- ⊆-antisymm (uvar ext1) (uvar ext2) with refl ← ⊆-antisymm ext1 ext2 = refl
-- ⊆-antisymm (evar ext1) (evar ext2) with refl ← ⊆-antisymm ext1 ext2 = refl
-- ⊆-antisymm (svar ext1 regA) (svar ext2 regA₁) with refl ← ⊆-antisymm ext1 ext2 = refl
-- ⊆-antisymm (mark x) (mark x₁) = {!!}

-- reg-⊆/x∙ : SRegular Δ
--         → Δ ∋∙ X
--         → Δ ⊆ Δ w/v X
-- reg-⊆/x∙ (reg-Z regΓ) (S⋈ inΔ) = ext-mark regΓ inΔ
-- reg-⊆/x∙ (reg-S∙ regΔ) Z = ext-Z∙ regΔ
-- reg-⊆/x∙ (reg-S∙ regΔ) (S∙ inΔ) = ext-S∙ (reg-⊆/x∙ regΔ inΔ)
-- reg-⊆/x∙ (reg-S^ regΔ) (S^ inΔ) = ext-S^ (reg-⊆/x∙ regΔ inΔ)
-- reg-⊆/x∙ (reg-S= regΔ regA) (S= inΔ) = ext-S= (reg-⊆/x∙ regΔ inΔ) regA

-- reg-⊆/ : SRegular Δ
--        → Δ ⊢r A
--        → Δ ⊆ Δ w/t A
-- reg-⊆/ senv ⊢r-int = ext-int senv
-- reg-⊆/ senv (⊢r-var-∙ inΓ) = ext-var (reg-⊆/x∙ senv inΓ)
-- reg-⊆/ senv (⊢r-arr regA regA₁) = ext-arr (reg-⊆/ senv regA) (reg-⊆/ senv regA₁)
-- reg-⊆/ senv (⊢r-∀ regA) = ext-∀ (reg-⊆/ (reg-S∙ senv) regA)


-- ⊆/x-∋∙-eq : Γ ⊆ Δ w/v X
--           → Γ ∋∙ X
--           → Γ ≡ Δ
-- ⊆/x-∋∙-eq (ext-Z∙ regΓ) Z = refl
-- ⊆/x-∋∙-eq (ext-S^ ext) (S^ inΓ) = cong _,^ (⊆/x-∋∙-eq ext inΓ)
-- ⊆/x-∋∙-eq (ext-S∙ ext) (S∙ inΓ) = cong _,∙ (⊆/x-∋∙-eq ext inΓ)
-- ⊆/x-∋∙-eq (ext-S= ext regA) (S= inΓ) = cong₂ _,=_ (⊆/x-∋∙-eq ext inΓ) refl
-- ⊆/x-∋∙-eq (ext-mark x _) inΓ = refl

-- ⊆/x-∋=-eq : Γ ⊆ Δ w/v X
--           → Γ ∋= X
--           → Γ ≡ Δ
-- ⊆/x-∋=-eq (ext-Z= regA regΓ) Z = refl
-- ⊆/x-∋=-eq (ext-S^ ext) (S^ inΓ) = cong _,^ (⊆/x-∋=-eq ext inΓ)
-- ⊆/x-∋=-eq (ext-S∙ ext) (S∙ inΓ) = cong _,∙ (⊆/x-∋=-eq ext inΓ)
-- ⊆/x-∋=-eq (ext-S= ext _) (S= inΓ) = cong₂ _,=_ (⊆/x-∋=-eq ext inΓ) refl

-- ⊆/-⊢c-eq : Γ ⊆ Δ w/t A
--          → Γ ⊢c A
--          → Γ ≡ Δ
-- ⊆/-⊢c-eq (ext-int regΓ) cloA = refl
-- ⊆/-⊢c-eq (ext-var x) (⊢c-var-∙ inΔ) = ⊆/x-∋∙-eq x inΔ
-- ⊆/-⊢c-eq (ext-var x) (⊢c-var-= inΔ) = ⊆/x-∋=-eq x inΔ
-- ⊆/-⊢c-eq (ext-arr ext ext₁) (⊢c-arr cloA cloA₁)
--   with refl ← ⊆/-⊢c-eq ext cloA
--   with refl ← ⊆/-⊢c-eq ext₁ cloA₁ = refl
-- ⊆/-⊢c-eq (ext-∀ ext) (⊢c-∀ cloA)
--   with refl ← ⊆/-⊢c-eq ext cloA = refl

-- ⊆/-∙out-∙in : Δ ∋∙ X
--             → Γ ⊆ Δ w/v X
--             → Γ ∋∙ X
-- ⊆/-∙out-∙in Z (ext-Z∙ _) = Z
-- ⊆/-∙out-∙in (S∙ inΓ) (ext-S∙ ext) = S∙ (⊆/-∙out-∙in inΓ ext)
-- ⊆/-∙out-∙in (S= inΓ) (ext-S= ext _) = S= (⊆/-∙out-∙in inΓ ext)
-- ⊆/-∙out-∙in (S^ inΓ) (ext-S^ ext) = S^ (⊆/-∙out-∙in inΓ ext)
-- ⊆/-∙out-∙in (S⋈ inΓ) (ext-mark x _) = S⋈ inΓ

-- ----------------------------------------------------------------------
-- --+             restricted extension implies extension             +--
-- ----------------------------------------------------------------------

-- ⊆/x-⊆ : Γ ⊆ Δ w/v X
--       → Γ ⊆ Δ
-- ⊆/x-⊆ (ext-Z^ regΓ regA) = evar-sol (⊆-refl regΓ) regA
-- ⊆/x-⊆ (ext-Z∙ regΓ) = ⊆-refl (reg-S∙ regΓ)
-- ⊆/x-⊆ (ext-Z= regΓ regA) = ⊆-refl (reg-S= regΓ regA)
-- ⊆/x-⊆ (ext-S^ ext) = evar (⊆/x-⊆ ext)
-- ⊆/x-⊆ (ext-S∙ ext) = uvar (⊆/x-⊆ ext)
-- ⊆/x-⊆ (ext-S= ext regA) = svar (⊆/x-⊆ ext) regA
-- ⊆/x-⊆ (ext-mark x _) = {!!}

-- ⊆/-⊆ : Γ ⊆ Δ w/t A
--      → Γ ⊆ Δ
-- ⊆/-⊆ (ext-int regΓ) = ⊆-refl regΓ
-- ⊆/-⊆ (ext-var x) = ⊆/x-⊆ x
-- ⊆/-⊆ (ext-arr ext ext₁) = ⊆-trans (⊆/-⊆ ext) (⊆/-⊆ ext₁)
-- ⊆/-⊆ (ext-∀ ext) with ⊆/-⊆ ext
-- ... | uvar r = r

-- ⊆/x-refl : SRegular Γ
--        → Γ ⊢c ‶ X
--        → Γ ⊆ Γ w/v X
-- ⊆/x-refl (reg-Z regΓ) (⊢c-var-∙ (S⋈ inΔ)) = ext-mark regΓ inΔ
-- ⊆/x-refl (reg-S∙ regΓ) (⊢c-var-∙ Z) = ext-Z∙ regΓ
-- ⊆/x-refl (reg-S∙ regΓ) (⊢c-var-∙ (S∙ inΔ)) = ext-S∙ (⊆/x-refl regΓ (⊢c-var-∙ inΔ))
-- ⊆/x-refl (reg-S^ regΓ) (⊢c-var-∙ (S^ inΔ)) = ext-S^ (⊆/x-refl regΓ (⊢c-var-∙ inΔ))
-- ⊆/x-refl (reg-S= regΓ regA) (⊢c-var-∙ (S= inΔ)) = ext-S= (⊆/x-refl regΓ (⊢c-var-∙ inΔ)) regA
-- ⊆/x-refl (reg-S∙ regΓ) (⊢c-var-= (S∙ inΔ)) = ext-S∙ (⊆/x-refl regΓ (⊢c-var-= inΔ))
-- ⊆/x-refl (reg-S^ regΓ) (⊢c-var-= (S^ inΔ)) = ext-S^ (⊆/x-refl regΓ (⊢c-var-= inΔ))
-- ⊆/x-refl (reg-S= regΓ regA) (⊢c-var-= Z) = ext-Z= regΓ regA
-- ⊆/x-refl (reg-S= regΓ regA) (⊢c-var-= (S= inΔ)) = ext-S= (⊆/x-refl regΓ (⊢c-var-= inΔ)) regA

-- ⊆/-refl : SRegular Γ
--        → Γ ⊢c A
--        → Γ ⊆ Γ w/t A
-- ⊆/-refl regΓ ⊢c-int = ext-int regΓ
-- ⊆/-refl regΓ (⊢c-var-∙ inΔ) = ext-var (⊆/x-refl regΓ (⊢c-var-∙ inΔ))
-- ⊆/-refl regΓ (⊢c-var-= inΔ) = ext-var (⊆/x-refl regΓ (⊢c-var-= inΔ))
-- ⊆/-refl regΓ (⊢c-arr cloA cloA₁) = ext-arr (⊆/-refl regΓ cloA) (⊆/-refl regΓ cloA₁)
-- ⊆/-refl regΓ (⊢c-∀ cloA) = ext-∀ (⊆/-refl (reg-S∙ regΓ) cloA)

-- ⊆/x-⊢c : Γ ⊆ Δ w/v X
--        → Δ ⊢c ‶ X
-- ⊆/x-⊢c (ext-Z^ regΓ regA) = ⊢c-var-= Z
-- ⊆/x-⊢c (ext-Z∙ regΓ) = ⊢c-var-∙ Z
-- ⊆/x-⊢c (ext-Z= regΓ regA) = ⊢c-var-= Z
-- ⊆/x-⊢c (ext-S^ ext) with ⊆/x-⊢c ext
-- ... | ⊢c-var-∙ inΔ = ⊢c-var-∙ (S^ inΔ)
-- ... | ⊢c-var-= inΔ = ⊢c-var-= (S^ inΔ)
-- ⊆/x-⊢c (ext-S∙ ext) with ⊆/x-⊢c ext
-- ... | ⊢c-var-∙ inΔ = ⊢c-var-∙ (S∙ inΔ)
-- ... | ⊢c-var-= inΔ = ⊢c-var-= (S∙ inΔ)
-- ⊆/x-⊢c (ext-S= ext regA) with ⊆/x-⊢c ext
-- ... | ⊢c-var-∙ inΔ = ⊢c-var-∙ (S= inΔ)
-- ... | ⊢c-var-= inΔ = ⊢c-var-= (S= inΔ)
-- ⊆/x-⊢c (ext-mark x inΓ) = ⊢c-var-∙ (S⋈ inΓ)

-- ⊆/-⊢c : Γ ⊆ Δ w/t A
--       → Δ ⊢c A
-- ⊆/-⊢c (ext-int x) = ⊢c-int
-- ⊆/-⊢c (ext-var x) = ⊆/x-⊢c x
-- ⊆/-⊢c (ext-arr ext ext₁) = ⊢c-arr (⊆-⊢c (⊆/-⊢c ext) (⊆/-⊆ ext₁)) (⊆/-⊢c ext₁)
-- ⊆/-⊢c (ext-∀ ext) = ⊢c-∀ (⊆/-⊢c ext)


-- ⊆-regular : SRegular Γ
--           → Γ ⊆ Δ
--           → SRegular Δ
-- ⊆-regular (reg-Z regΓ) (mark x) = {!!}
-- ⊆-regular (reg-S∙ regΓ) (uvar ext) = reg-S∙ (⊆-regular regΓ ext)
-- ⊆-regular (reg-S^ regΓ) (evar ext) = reg-S^ (⊆-regular regΓ ext)
-- ⊆-regular (reg-S^ regΓ) (evar-sol ext regA) = reg-S= (⊆-regular regΓ ext) regA
-- ⊆-regular (reg-S= regΓ regA) (svar ext regA₁) = reg-S= (⊆-regular regΓ ext) (⊆-⊢r regA ext)

-- ⊆-regular' : SRegular Δ
--            → Γ ⊆ Δ
--            → SRegular Γ
-- ⊆-regular' (reg-Z regΓ) (mark x) = {!!}
-- ⊆-regular' (reg-S∙ reg) (uvar ext) = reg-S∙ (⊆-regular' reg ext)
-- ⊆-regular' (reg-S^ reg) (evar ext) = reg-S^ (⊆-regular' reg ext)
-- ⊆-regular' (reg-S= reg regA) (evar-sol ext regA₁) = reg-S^ (⊆-regular' reg ext)
-- ⊆-regular' (reg-S= reg regA) (svar ext regA₁) = reg-S= (⊆-regular' reg ext) regA₁


-- ⊆-sregular : Γ ⊆ Δ
--            → SRegular Γ
-- ⊆-sregular (uvar ext) = reg-S∙ (⊆-sregular ext)
-- ⊆-sregular (evar ext) = reg-S^ (⊆-sregular ext)
-- ⊆-sregular (evar-sol ext regA) = reg-S^ (⊆-sregular ext)
-- ⊆-sregular (svar ext regA) = reg-S= (⊆-sregular ext) regA
-- ⊆-sregular (mark regΓ) = {!!}

-- ⊆-sregular' : Γ ⊆ Δ
--             → SRegular Δ
-- ⊆-sregular' (uvar ext) = reg-S∙ (⊆-sregular' ext)
-- ⊆-sregular' (evar ext) = reg-S^ (⊆-sregular' ext)
-- ⊆-sregular' (evar-sol ext regA) = reg-S= (⊆-sregular' ext) regA
-- ⊆-sregular' (svar ext regA) = reg-S= (⊆-sregular' ext) (⊆-⊢r regA ext)
-- ⊆-sregular' (mark regΓ) = {!!}



-- -- could be proved via a inst-total
-- -- however, the total requires a condition: B is shifted k times, which is a tricky to define in well-scoped settings: finite nubmers
-- inst-exist : [ B / k ] Δ =⟹ Δ'
--            → Ω ⊆ Δ
--            → Ω ∋= k
--            → ∃[ Ω' ]( [ B / k ] Ω =⟹ Ω')
-- inst-exist (=⟹=0  {A = A} up regA' regΓ) (svar {Γ = Γ} ext regA) Z = ⟨ Γ ,= A , =⟹=0 up (⊆-⊢r' regA' ext) (⊆-regular' regΓ ext) ⟩
-- inst-exist (=⟹^S inst up1) (evar ext) (S^ inΩ) = ⟨ inst-exist inst ext inΩ .proj₁ ,^ ,
--                                                   =⟹^S (inst-exist inst ext inΩ .proj₂) up1 ⟩
-- inst-exist (=⟹∙S inst up1) (uvar ext) (S∙ inΩ) = ⟨ inst-exist inst ext inΩ .proj₁ ,∙ ,
--                                                   =⟹∙S (inst-exist inst ext inΩ .proj₂) up1 ⟩
-- inst-exist (=⟹=S inst up1 regB) (evar-sol ext regA) (S^ inΩ) = ⟨ inst-exist inst ext inΩ .proj₁ ,^ ,
--                                                            =⟹^S (inst-exist inst ext inΩ .proj₂) up1 ⟩
-- inst-exist (=⟹=S inst up1 regB) (svar {A = A} ext regA) (S= inΩ) = ⟨ inst-exist inst ext inΩ .proj₁ ,= A ,
--                                                        =⟹=S (inst-exist inst ext inΩ .proj₂) up1 regA ⟩

-- inst-exist' : [ B / k ] Γ =⟹ Γ'
--             → Γ ⊆ Ω
--             → ∃[ Ω' ]( [ B / k ] Ω =⟹ Ω')
-- inst-exist' (=⟹=0 {A = A} up regA' reΓ) (svar {Δ = Δ} ext regA) = ⟨ Δ ,= A , =⟹=0 up (⊆-⊢r regA' ext) (⊆-regular reΓ ext) ⟩
-- inst-exist' (=⟹^S inst up1) (evar ext) = ⟨ inst-exist' inst ext .proj₁ ,^ ,
--                                           =⟹^S (inst-exist' inst ext .proj₂) up1 ⟩
-- inst-exist' (=⟹^S inst up1) (evar-sol {A = A} ext regA) = ⟨ inst-exist' inst ext .proj₁ ,= A ,
--                                                    =⟹=S (inst-exist' inst ext .proj₂) up1 regA ⟩
-- inst-exist' (=⟹∙S inst up1) (uvar ext) = ⟨ inst-exist' inst ext .proj₁ ,∙ ,
--                                           =⟹∙S (inst-exist' inst ext .proj₂) up1 ⟩
-- inst-exist' (=⟹=S inst up1 regB) (svar {A = A} ext regA) = ⟨ inst-exist' inst ext .proj₁ ,= A ,
--                                                =⟹=S (inst-exist' inst ext .proj₂) up1 (⊆-⊢r regB ext) ⟩
