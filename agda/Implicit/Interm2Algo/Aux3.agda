module Implicit.Interm2Algo.Aux3 where


open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.AuxLemmas

open import Implicit.Interm2Algo.Aux1
open import Implicit.Interm2Algo.FVClose

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
