module Implicit.Algo.Properties.Swap where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Id


data swap : Env n m → Env n m → Set where
  swap-Z : swap (Γ ⋈ ,∙) (Γ ,∙ ⋈)
  swap-S, : swap Γ Δ
          → swap (Γ , A) (Δ , A)
  swap-S∙ : swap Γ Δ
          → swap (Γ ,∙) (Δ ,∙)
  swap-S= : swap Γ Δ
          → swap (Γ ,= A) (Δ ,= A)
  swap-S^ : swap Γ Δ
          → swap (Γ ,^) (Δ ,^)


swap-Ω : Γ ⊆ Ω
       → Ω ⊆ Δ
       → swap Γ Γ'
       → swap Δ Δ'
       → ∃[ Ω' ](swap Ω Ω')
swap-Ω (uvar (mark {Γ = Γ} regΓ)) (uvar (mark regΓ₁)) swap-Z swap-Z = ⟨ Γ ,∙ ⋈ , swap-Z ⟩
swap-Ω (uvar (mark regΓ)) (uvar (mark regΓ₁)) swap-Z (swap-S∙ ())
swap-Ω (uvar (mark {Γ = Γ} regΓ₁)) (uvar (mark regΓ)) (swap-S∙ sw1) swap-Z = ⟨ Γ ,∙ ⋈ , swap-Z ⟩
swap-Ω (uvar ext1) (uvar ext2) (swap-S∙ sw1) (swap-S∙ sw2) = ⟨ swap-Ω ext1 ext2 sw1 sw2 .proj₁ ,∙ ,
                                                              swap-S∙ (swap-Ω ext1 ext2 sw1 sw2 .proj₂) ⟩
swap-Ω (evar ext1) (evar ext2) (swap-S^ sw1) (swap-S^ sw2) = ⟨ swap-Ω ext1 ext2 sw1 sw2 .proj₁ ,^ ,
                                                              swap-S^ (swap-Ω ext1 ext2 sw1 sw2 .proj₂) ⟩
swap-Ω (evar ext1) (evar-sol ext2 regA) (swap-S^ sw1) (swap-S= sw2) = ⟨ swap-Ω ext1 ext2 sw1 sw2 .proj₁ ,^ ,
                                                                       swap-S^ (swap-Ω ext1 ext2 sw1 sw2 .proj₂) ⟩
swap-Ω (evar-sol ext1 regA) (svar ext2 regA₁) (swap-S^ sw1) (swap-S= {A = A} sw2)
  = ⟨ swap-Ω ext1 ext2 sw1 sw2 .proj₁ ,= A , swap-S= (swap-Ω ext1 ext2 sw1 sw2 .proj₂) ⟩
swap-Ω (svar ext1 regA) (svar ext2 regA₁) (swap-S= {A = A} sw1) (swap-S= sw2) = ⟨ swap-Ω ext1 ext2 sw1 sw2 .proj₁ ,= A ,
                                                                         swap-S= (swap-Ω ext1 ext2 sw1 sw2 .proj₂) ⟩


swap-∋∙ : Γ ∋∙ X
        → swap Γ Δ
        → Δ ∋∙ X
swap-∋∙ Z swap-Z = S⋈ Z
swap-∋∙ Z (swap-S∙ sw) = Z
swap-∋∙ (S, inΓ) (swap-S, sw) = S, (swap-∋∙ inΓ sw)
swap-∋∙ (S∙ (S⋈ inΓ)) swap-Z = S⋈ (S∙ inΓ)
swap-∋∙ (S∙ inΓ) (swap-S∙ sw) = S∙ (swap-∋∙ inΓ sw)
swap-∋∙ (S= inΓ) (swap-S= sw) = S= (swap-∋∙ inΓ sw)
swap-∋∙ (S^ inΓ) (swap-S^ sw) = S^ (swap-∋∙ inΓ sw)

swap-∋:= : Γ ∋ X := A
         → swap Γ Δ
         → Δ ∋ X := A
swap-∋:= (Z up) (swap-S= sw) = Z up
swap-∋:= (S∙ inΓ up) (swap-S∙ sw) = S∙ (swap-∋:= inΓ sw) up
swap-∋:= (S^ inΓ up) (swap-S^ sw) = S^ (swap-∋:= inΓ sw) up
swap-∋:= (S= inΓ up) (swap-S= sw) = S= (swap-∋:= inΓ sw) up
swap-∋:= (S, inΓ) (swap-S, sw) = S, (swap-∋:= inΓ sw)

swap-⊢r : Γ ⊢r A
        → swap Γ Δ
        → Δ ⊢r A
swap-⊢r ⊢r-int sw = ⊢r-int
swap-⊢r (⊢r-var-∙ inΓ) sw = ⊢r-var-∙ (swap-∋∙ inΓ sw)
swap-⊢r (⊢r-arr regA regA₁) sw = ⊢r-arr (swap-⊢r regA sw) (swap-⊢r regA₁ sw)
swap-⊢r (⊢r-∀ regA) sw = ⊢r-∀ (swap-⊢r regA (swap-S∙ sw))

swap-sregular : SRegular Γ
              → swap Γ Δ
              → SRegular Δ
swap-sregular (reg-S∙ (reg-Z regΓ)) swap-Z = reg-Z (reg-S∙ regΓ)
swap-sregular (reg-S∙ regΓ) (swap-S∙ sw) = reg-S∙ (swap-sregular regΓ sw)
swap-sregular (reg-S^ regΓ) (swap-S^ sw) = reg-S^ (swap-sregular regΓ sw)
swap-sregular (reg-S= regΓ regA) (swap-S= sw) = reg-S= (swap-sregular regΓ sw) (swap-⊢r regA sw)


swap-unique : swap Γ Δ₁
            → swap Γ Δ₂
            → Δ₁ ≡ Δ₂
swap-unique swap-Z swap-Z = refl
swap-unique (swap-S, sw1) (swap-S, sw2)
  with refl ← swap-unique sw1 sw2 = refl
swap-unique (swap-S∙ sw1) (swap-S∙ sw2)
  with refl ← swap-unique sw1 sw2 = refl
swap-unique (swap-S= sw1) (swap-S= sw2)
  with refl ← swap-unique sw1 sw2 = refl
swap-unique (swap-S^ sw1) (swap-S^ sw2)
  with refl ← swap-unique sw1 sw2 = refl

inst-swap : [ A / X ] Γ ⟹ Δ
           → swap Γ Γ'
           → swap Δ Δ'
           → [ A / X ] Γ' ⟹ Δ'
inst-swap (⟹^0 up regA env) (swap-S^ sw1) (swap-S= sw2)
  with refl ← swap-unique sw1 sw2 = ⟹^0 up (swap-⊢r regA sw1) (swap-sregular env sw1)
inst-swap (⟹^S inst up1) (swap-S^ sw1) (swap-S^ sw2) = ⟹^S (inst-swap inst sw1 sw2) up1
inst-swap (⟹∙S inst up1) (swap-S∙ sw1) (swap-S∙ sw2) = ⟹∙S (inst-swap inst sw1 sw2) up1
inst-swap (⟹=S inst up1 regB) (swap-S= sw1) (swap-S= sw2) = ⟹=S (inst-swap inst sw1 sw2) up1 (swap-⊢r regB sw1)

ss-swap : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
        → swap Γ Γ'
        → swap Δ Δ'
        → Γ' ⊢ A ⌞ ≤ ⌝ B ⊣ Δ'
ss-swap (s-int regΓ) sw1 sw2
  with refl ← swap-unique sw1 sw2 = s-int (swap-sregular regΓ sw1)
ss-swap (s-var-∙ regΓ inΔ) sw1 sw2
  with refl ← swap-unique sw1 sw2 = s-var-∙ (swap-sregular regΓ sw1) (swap-∋∙ inΔ sw1)
ss-swap (s-ex-l^ inst) sw1 sw2 = s-ex-l^ (inst-swap inst sw1 sw2)
ss-swap (s-ex-r^ inst) sw1 sw2 = s-ex-r^ (inst-swap inst sw1 sw2)
ss-swap (s-ex-l= regΓ x-in) sw1 sw2
  with refl ← swap-unique sw1 sw2 = s-ex-l= (swap-sregular regΓ sw1) (swap-∋:= x-in sw1)
ss-swap (s-ex-r= regΓ x-in) sw1 sw2
  with refl ← swap-unique sw1 sw2 = s-ex-r= (swap-sregular regΓ sw1) (swap-∋:= x-in sw1)
ss-swap (s-arr ss ss₁) sw1 sw2
  with ⟨ Ω' , sΩ ⟩ ← swap-Ω (ss-⊆ ss) (ss-⊆ ss₁) sw1 sw2 = s-arr (ss-swap ss sw1 sΩ) (ss-swap ss₁ sΩ sw2)
ss-swap (s-∀ ss) sw1 sw2 = s-∀ (ss-swap ss (swap-S∙ sw1) (swap-S∙ sw2))
