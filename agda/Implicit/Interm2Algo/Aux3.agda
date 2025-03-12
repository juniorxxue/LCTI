{-# OPTIONS --allow-unsolved-metas #-}
module Implicit.Interm2Algo.Aux3 where


open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.AuxLemmas

open import Implicit.Interm2Algo.Aux1 hiding (ⅆ-total; ⅆ-inst; s+-subirrev; s--subirrev)

ⅆ-total :  Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
         → Γ ⊆ Ω
         → Ω ⊆ Δ
         → ∃[ Ω' ](Γ ⅆ Γ' ⊆ Ω ⅆ Ω' kp H
                 × Ω ⅆ Ω' ⊆ Δ ⅆ Δ' kp H)
ⅆ-total (ⅆ⋈ {Γ = Γ} regΓ) (mark regΓ₁) (mark regΓ₂) = ⟨ Γ ⋈ , ⟨ ⅆ⋈ regΓ , ⅆ⋈ regΓ₂ ⟩ ⟩
ⅆ-total (ⅆS∙∙-hit dd) (uvar ext1) (uvar ext2) = ⟨ ⅆ-total dd ext1 ext2 .proj₁ ,∙ ,
                                                 ⟨ ⅆS∙∙-hit (ⅆ-total dd ext1 ext2 .proj₂ .proj₁) ,
                                                 ⅆS∙∙-hit (ⅆ-total dd ext1 ext2 .proj₂ .proj₂) ⟩
                                                 ⟩
ⅆ-total (ⅆS∙∙-mis dd) (uvar ext1) (uvar ext2) = ⟨ ⅆ-total dd ext1 ext2 .proj₁ ,∙ ,
                                                 ⟨ ⅆS∙∙-mis (ⅆ-total dd ext1 ext2 .proj₂ .proj₁) ,
                                                 ⅆS∙∙-mis (ⅆ-total dd ext1 ext2 .proj₂ .proj₂) ⟩
                                                 ⟩
ⅆ-total (ⅆS^=-hit dd) (evar ext1) (evar-sol ext2 regA) = ⟨ ⅆ-total dd ext1 ext2 .proj₁ ,^ ,
                                                          ⟨ ⅆS^^-hit (ⅆ-total dd ext1 ext2 .proj₂ .proj₁) ,
                                                          ⅆS^=-hit (ⅆ-total dd ext1 ext2 .proj₂ .proj₂) ⟩
                                                          ⟩
ⅆ-total (ⅆS^=-hit dd) (evar-sol {A = A} ext1 regA) (svar ext2 regA₁) = ⟨ ⅆ-total dd ext1 ext2 .proj₁ ,= A ,
                                                                ⟨ ⅆS^=-hit (ⅆ-total dd ext1 ext2 .proj₂ .proj₁) ,
                                                                ⅆS==-hit (ⅆ-total dd ext1 ext2 .proj₂ .proj₂) regA ⟩
                                                                ⟩
ⅆ-total (ⅆS^=-mis dd) (evar ext1) (evar-sol ext2 regA) = ⟨ ⅆ-total dd ext1 ext2 .proj₁ ,^ ,
                                                          ⟨ ⅆS^^-mis (ⅆ-total dd ext1 ext2 .proj₂ .proj₁) ,
                                                          ⅆS^=-mis (ⅆ-total dd ext1 ext2 .proj₂ .proj₂) ⟩
                                                          ⟩
ⅆ-total (ⅆS^=-mis {A = A} dd) (evar-sol ext1 regA) (svar ext2 regA₁) = ⟨ ⅆ-total dd ext1 ext2 .proj₁ ,= A ,
                                                                ⟨ ⅆS^=-mis (ⅆ-total dd ext1 ext2 .proj₂ .proj₁) ,
                                                                ⅆS==-mis-1 (ⅆ-total dd ext1 ext2 .proj₂ .proj₂) regA ⟩
                                                                ⟩
ⅆ-total (ⅆS^^-hit dd) (evar ext1) (evar ext2) = ⟨ ⅆ-total dd ext1 ext2 .proj₁ ,^ ,
                                                 ⟨ ⅆS^^-hit (ⅆ-total dd ext1 ext2 .proj₂ .proj₁) ,
                                                 ⅆS^^-hit (ⅆ-total dd ext1 ext2 .proj₂ .proj₂) ⟩
                                                 ⟩
ⅆ-total (ⅆS^^-mis dd) (evar ext1) (evar ext2) = ⟨ ⅆ-total dd ext1 ext2 .proj₁ ,^ ,
                                                   ⟨ ⅆS^^-mis (ⅆ-total dd ext1 ext2 .proj₂ .proj₁) ,
                                                   ⅆS^^-mis (ⅆ-total dd ext1 ext2 .proj₂ .proj₂) ⟩
                                                   ⟩
ⅆ-total (ⅆS==-hit {A = A} dd regA) (svar ext1 regA') (svar ext2 regA₁) = ⟨ ⅆ-total dd ext1 ext2 .proj₁ ,= A ,
                                                            ⟨ ⅆS==-hit (ⅆ-total dd ext1 ext2 .proj₂ .proj₁) regA ,
                                                            ⅆS==-hit (ⅆ-total dd ext1 ext2 .proj₂ .proj₂) regA₁ ⟩
                                                            ⟩
ⅆ-total (ⅆS==-mis-1 {A = A} dd regA) (svar ext1 regA') (svar ext2 regA₁) = ⟨ ⅆ-total dd ext1 ext2 .proj₁ ,= A ,
                                                              ⟨ ⅆS==-mis-1 (ⅆ-total dd ext1 ext2 .proj₂ .proj₁) regA ,
                                                              ⅆS==-mis-1 (ⅆ-total dd ext1 ext2 .proj₂ .proj₂) regA₁ ⟩
                                                              ⟩
ⅆ-total (ⅆS==-mis-2 dd regA) (svar ext1 regA') (svar ext2 regA₁) = ⟨ ⅆ-total dd ext1 ext2 .proj₁ ,^ ,
                                                              ⟨ ⅆS==-mis-2 (ⅆ-total dd ext1 ext2 .proj₂ .proj₁) regA ,
                                                              ⅆS==-mis-2 (ⅆ-total dd ext1 ext2 .proj₂ .proj₂) regA₁ ⟩
                                                              ⟩



ⅆ-inst : [ T / X ] Γ ⟹ Δ
       → Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp mkHit X
       → [ T / X ] Γ' ⟹ Δ'
ⅆ-inst (⟹^0 up regA env) (ⅆS^=-hit dd) with refl ← ⅆ-input-eq dd = ⟹^0 up (⊆-⊢r' regA (ⅆ-⊆-l dd)) {!!}
ⅆ-inst (⟹^S inst up1) (ⅆS^^-mis dd) = ⟹^S (ⅆ-inst inst dd) up1
ⅆ-inst (⟹∙S inst up1) (ⅆS∙∙-mis dd) = ⟹∙S (ⅆ-inst inst dd) up1
ⅆ-inst (⟹=S inst up1 regB) (ⅆS==-mis-1 dd regA) = ⟹=S (ⅆ-inst inst dd) up1 (⊆-⊢r' regB (ⅆ-⊆-l dd))
ⅆ-inst (⟹=S inst up1 regB) (ⅆS==-mis-2 dd regA) = ⟹^S (ⅆ-inst inst dd) up1

s+-subirrev : Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ
            → A 𝕗𝕧 H
            → Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
            → Γ' ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ'

s--subirrev : Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ
            → B 𝕗𝕧 H
            → Γ ⅆ Γ' ⊆ Δ ⅆ Δ' kp H
            → Γ' ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ'

s+-subirrev (s-int regΓ) fv-Int tf with refl ← ⅆ-input-eq tf = s-int {!!}
s+-subirrev (s-var-∙ regΓ x) fv-var tf with refl ← ⅆ-input-eq tf = s-var-∙ {!!} {!!}
s+-subirrev (s-ex-l^ inst) fv-var tf = s-ex-l^ (ⅆ-inst inst tf)
s+-subirrev (s-ex-l= regΓ x-in) fv-var tf with refl ← ⅆ-input-eq tf = s-ex-l= {!!} {!!}
s+-subirrev (s-arr s s₁) (fv-arr fv fv₁ cb) tf with ⅆ-total tf (ss-⊆ s) (ss-⊆ s₁)
... | ⟨ Ω' , ⟨ dd1 , dd2 ⟩ ⟩ = s-arr (s--subirrev s fv (ⅆ-or-l dd1 cb)) (s+-subirrev s₁ fv₁ (ⅆ-or-r dd2 cb))
s+-subirrev (s-∀ s) (fv-∀-h fv) tf = s-∀ (s+-subirrev s fv (ⅆS∙∙-hit tf))
s+-subirrev (s-∀ s) (fv-∀-m fv) tf = s-∀ (s+-subirrev s fv (ⅆS∙∙-mis tf))

𝕗𝕧-total : ∀ (A : Type m)
         → ∃[ H ](A 𝕗𝕧 H)

s-subirrev : Ψ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ
           → Δ ⅆ Ω ≋ Ψ ⅆ Γ
           → Γ ⊆ Ω w/t B -- or Ω ⊢c B
           → Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Ω
s-subirrev {B = B} s dd cloB with 𝕗𝕧-total B
... | ⟨ H , fv ⟩ = s--subirrev s fv {!zm!}

helper : Δ ⅆ Ω ≋ Ψ ⅆ Γ
       → B 𝕗𝕧 H
       → Γ ⊆ Ω w/t B
       → Ψ ⅆ Γ ⊆ Δ ⅆ Ω kp H
helper (ⅆ⋈ regΓ) fvB extB = ⅆ⋈ regΓ
helper {H = hit H} (ⅆS∙ dd) fvB extB = ⅆS∙∙-hit (helper dd (fv-∀-h fvB) (ext-∀ extB))
helper {H = mis H} (ⅆS∙ dd) fvB extB = ⅆS∙∙-mis (helper dd (fv-∀-m fvB) (ext-∀ extB))
helper {H = hit H} (ⅆS^ dd) fvB extB = ⊥-elim {!!}
helper {H = mis H} (ⅆS^ dd) fvB extB = ⅆS^^-mis (helper dd {!!} {!!})
helper {H = hit H} (ⅆS=^ dd regA) fvB extB = ⊥-elim {!!}
helper {H = mis H} (ⅆS=^ dd regA) fvB extB = ⅆS==-mis-2 {!!} {!!}
helper {H = hit H} (ⅆS==1 dd regA) fvB extB = ⅆS==-hit (helper dd {!!} {!!}) {!!}
helper {H = mis H} (ⅆS==1 dd regA) fvB extB = ⅆS==-mis-1 (helper dd {!!} {!!}) {!!}
helper {H = hit H} (ⅆS==2 dd regA) fvB extB = ⅆS^=-hit (helper dd {!!} {!!})
helper {H = mis H} (ⅆS==2 dd regA) fvB extB = ⊥-elim {!!}


helper' : Δ ⅆ Ω ≋ Ψ ⅆ Γ
       → A 𝕗𝕧 H
       → Ω ⊢c A
       → Ψ ⅆ Γ ⊆ Δ ⅆ Ω kp H
helper' (ⅆ⋈ regΓ) fv cloB = ⅆ⋈ regΓ
helper' {H = hit H} (ⅆS∙ dd) fv cloB = ⅆS∙∙-hit (helper' dd (fv-∀-h fv) (⊢c-∀ cloB))
helper' {H = mis H} (ⅆS∙ dd) fv cloB = ⅆS∙∙-mis (helper' dd (fv-∀-m fv) (⊢c-∀ cloB))
helper' {H = hit H} (ⅆS^ dd) fv cloB = ⊥-elim {!!}
helper' {H = mis H} (ⅆS^ dd) fv cloB = ⅆS^^-mis (helper' dd {!!} {!!})
helper' {H = hit H} (ⅆS=^ dd regA) fv cloB = ⊥-elim {!!}
helper' {H = mis H} (ⅆS=^ dd regA) fv cloB = ⅆS==-mis-2 (helper' dd {!!} {!!}) {!!}
helper' {A = B} {H = hit H} (ⅆS==1 {A = A} dd regA) fv cloB = ⅆS==-hit (helper' dd (fv-∀-h fv) (⊢c-∀ {!!})) {!!}
helper' {H = mis H} (ⅆS==1 dd regA) fv cloB = ⅆS==-mis-1 (helper' dd (fv-∀-m fv) (⊢c-∀ {!!})) {!!}
helper' {H = hit H} (ⅆS==2 dd regA) fv cloB = ⅆS^=-hit (helper' dd (fv-∀-h fv) (⊢c-∀ {!!}))
helper' {H = mis H} (ⅆS==2 dd regA) fv cloB = ⅆS^=-mis (helper' dd (fv-∀-m fv) (⊢c-∀ {!!}))
