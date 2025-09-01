module Implicit.Interm2Algo.Inst where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm2Algo.EnvDiff
open import Implicit.Interm2Algo.OpenClose

postulate
  infs-sub' : 𝕣 Γ ⊨ Σ ⟹ A
          → SRegular Γ
          → Γ ⊢ A ≤⁺ Σ ⊣ Γ ↪ A

ss-≫-- : Γ ⊢ B ⌞ ≤⁻ ⌝ A ⊣ Δ
       → Δ ≫ A ⇘ B

ss-≫-+ : Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ
       → Δ ≫ A ⇘ B


ss-≫-- (s-int regΓ) = grd-int
ss-≫-- (s-var-∙ regΓ inΔ) = grd-var∙ inΔ
ss-≫-- (s-ex-r^ inst) = grd-var= (inst-∋:= inst)
ss-≫-- (s-ex-r= regΓ x-in) = grd-var= x-in
ss-≫-- (s-arr s s₁) = grd-arr (⊆-⊢c-≫' (ss-⊆ s₁) (ss+-⊢c s) (ss-≫-+ s)) (ss-≫-- s₁)
ss-≫-- (s-∀ s) = grd-∀ (ss-≫-- s)

ss-≫-+ (s-int regΓ) = grd-int
ss-≫-+ (s-var-∙ regΓ inΔ) = grd-var∙ inΔ
ss-≫-+ (s-ex-l^ inst) = grd-var= (inst-∋:= inst)
ss-≫-+ (s-ex-l= regΓ x-in) = grd-var= x-in
ss-≫-+ (s-arr s s₁) = grd-arr (⊆-⊢c-≫' (ss-⊆ s₁) (ss--⊢c s) (ss-≫-- s)) (ss-≫-+ s₁)
ss-≫-+ (s-∀ s) = grd-∀ (ss-≫-+ s)



∋=-∋:=-⊆ : Γ ∋= k
         → Δ ∋ k := T
         → Γ ⊆ Δ
         → Γ ∋ k := T
∋=-∋:=-⊆ Z (Z up) (svar ext regA) = Z up
∋=-∋:=-⊆ (S∙ in1) (S∙ in2 up) (uvar ext) = S∙ (∋=-∋:=-⊆ in1 in2 ext) up
∋=-∋:=-⊆ (S^ in1) (S^ in2 up) (evar ext) = S^ (∋=-∋:=-⊆ in1 in2 ext) up
∋=-∋:=-⊆ (S^ in1) (S= in2 up) (evar-sol ext regA) = S^ (∋=-∋:=-⊆ in1 in2 ext) up
∋=-∋:=-⊆ (S= in1) (S= in2 up) (svar ext regA) = S= (∋=-∋:=-⊆ in1 in2 ext) up


inst-false-1 : Γ ∋^ X
             → [ T / k ] Γ ⟹ Γ'
             → Γ' ∋∙ X
             → ⊥
inst-false-1 Z (⟹^0 up regA env) ()
inst-false-1 Z (⟹^S inst up1) ()
inst-false-1 (S∙ in1) (⟹∙S inst up1) (S∙ in2) = inst-false-1 in1 inst in2
inst-false-1 (S= in1) (⟹=S inst up1 regB) (S= in2) = inst-false-1 in1 inst in2
inst-false-1 (S^ in1) (⟹^0 up regA env) (S= in2) = ⊥-elim (∋^-∋∙-false in1 in2)
inst-false-1 (S^ in1) (⟹^S inst up1) (S^ in2) = inst-false-1 in1 inst in2

inst-affect-one : [ A / X ] Γ ⟹ Δ
                → Γ ∋^ k
                → Δ ∋= k
                → k ≡ X
inst-affect-one (⟹^0 up regA env) Z Z = refl
inst-affect-one (⟹^0 up regA env) (S^ in1) (S= in2) = ⊥-elim (∋^-∋=-false in1 in2)
inst-affect-one (⟹^S inst up1) (S^ in1) (S^ in2)
  with refl ← inst-affect-one inst in1 in2 = refl
inst-affect-one (⟹∙S inst up1) (S∙ in1) (S∙ in2)
  with refl ← inst-affect-one inst in1 in2 = refl
inst-affect-one (⟹=S inst up1 regB) (S= in1) (S= in2)
  with refl ← inst-affect-one inst in1 in2 = refl

⊆/x-unique : Γ ⊆ Δ₁ w/v k
           → Γ ⊆ Δ₂ w/v k
           → Δ₁ ∋ k := T
           → Δ₂ ∋ k := T
           → Δ₁ ≡ Δ₂
⊆/x-unique (ext-Z^ regΓ regA) (ext-Z^ regΓ₁ regA₁) (Z up) (Z up₁)
  with refl ← ↑ty-unique-inver up up₁
  = refl
⊆/x-unique (ext-Z= regΓ regA) (ext-Z= regΓ₁ regA₁) (Z up) (Z up₁) = refl
⊆/x-unique (ext-S^ ext1) (ext-S^ ext2) (S^ in1 up) (S^ in2 up₁)
  with refl ← ↑ty-unique-inver up up₁
  with refl ← ⊆/x-unique ext1 ext2 in1 in2
  = refl
⊆/x-unique (ext-S∙ ext1) (ext-S∙ ext2) (S∙ in1 up) (S∙ in2 up₁)
  with refl ← ↑ty-unique-inver up up₁
  with refl ← ⊆/x-unique ext1 ext2 in1 in2
  = refl
⊆/x-unique (ext-S= ext1 regA) (ext-S= ext2 regA₁) (S= in1 up) (S= in2 up₁)
  with refl ← ↑ty-unique-inver up up₁
  with refl ← ⊆/x-unique ext1 ext2 in1 in2
  = refl


inst-∋^-⊢c-eq : Γ ∋^ X
              → Γ ⊆ Γ' w/v k
              → Γ' ⊢c ‶ X
              → k ≡ X
inst-∋^-⊢c-eq Z (ext-Z^ regΓ regA) cloX = refl
inst-∋^-⊢c-eq Z (ext-S^ extx) (⊢c-var-∙ ())
inst-∋^-⊢c-eq Z (ext-S^ extx) (⊢c-var-= ())
inst-∋^-⊢c-eq (S∙ in1) (ext-Z∙ regΓ) (⊢c-var-∙ (S∙ inΔ)) = ⊥-elim (∋^-∋∙-false in1 inΔ)
inst-∋^-⊢c-eq (S∙ in1) (ext-S∙ extx) (⊢c-var-∙ (S∙ inΔ)) = cong #S (inst-∋^-⊢c-eq in1 extx (⊢c-var-∙ inΔ))
inst-∋^-⊢c-eq (S∙ in1) (ext-Z∙ regΓ) (⊢c-var-= (S∙ inΔ)) = ⊥-elim (∋^-∋=-false in1 inΔ)
inst-∋^-⊢c-eq (S∙ in1) (ext-S∙ extx) (⊢c-var-= (S∙ inΔ)) = cong #S (inst-∋^-⊢c-eq in1 extx (⊢c-var-= inΔ))
inst-∋^-⊢c-eq (S= in1) (ext-Z= regΓ regA) (⊢c-var-∙ (S= inΔ)) = ⊥-elim (∋^-∋∙-false in1 inΔ)
inst-∋^-⊢c-eq (S= in1) (ext-Z= regΓ regA) (⊢c-var-= (S= inΔ)) = ⊥-elim (∋^-∋=-false in1 inΔ)
inst-∋^-⊢c-eq (S= in1) (ext-S= extx regA) (⊢c-var-∙ (S= inΔ)) = cong #S (inst-∋^-⊢c-eq in1 extx (⊢c-var-∙ inΔ))
inst-∋^-⊢c-eq (S= in1) (ext-S= extx regA) (⊢c-var-= (S= inΔ)) = cong #S (inst-∋^-⊢c-eq in1 extx (⊢c-var-= inΔ))
inst-∋^-⊢c-eq (S^ in1) (ext-Z^ regΓ regA) (⊢c-var-∙ (S= inΔ)) = ⊥-elim (∋^-∋∙-false in1 inΔ)
inst-∋^-⊢c-eq (S^ in1) (ext-Z^ regΓ regA) (⊢c-var-= (S= inΔ)) = ⊥-elim (∋^-∋=-false in1 inΔ)
inst-∋^-⊢c-eq (S^ in1) (ext-S^ extx) (⊢c-var-∙ (S^ inΔ)) = cong #S (inst-∋^-⊢c-eq in1 extx (⊢c-var-∙ inΔ))
inst-∋^-⊢c-eq (S^ in1) (ext-S^ extx) (⊢c-var-= (S^ inΔ)) = cong #S (inst-∋^-⊢c-eq in1 extx (⊢c-var-= inΔ))

inst-⊢o-⊢c-ε : Γ ⊢o A
             → [ T / k ] Γ ⟹ Γ'
             → Γ' ⊢c A
             → k ε A
inst-⊢o-⊢c-ε (⊢o-var-^ x) inst cloA
  with refl ← inst-∋^-⊢c-eq x (inst-⊆/x inst) cloA = ε-var
inst-⊢o-⊢c-ε (⊢o-arr-l opnA) inst (⊢c-arr cloA cloA₁) = ε-arr-l (inst-⊢o-⊢c-ε opnA inst cloA)
inst-⊢o-⊢c-ε {k = k} (⊢o-arr-r {A = A} opnA) inst (⊢c-arr cloA cloA₁) with ε-dec {k = k} {A = A}
... | inj₁ x = ε-arr-l x
... | inj₂ y = ε-arr-r y (inst-⊢o-⊢c-ε opnA inst cloA₁)
inst-⊢o-⊢c-ε {T = T} (⊢o-∀ opnA) inst (⊢c-∀ cloA)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = ε-∀ (inst-⊢o-⊢c-ε opnA (⟹∙S inst upT) cloA)

s-unsol-sol-helper-eq : Γ ⊢o A
                      → Γ' ⊢c A
                      → [ T / k ] Γ ⟹ Γ'
                      → Γ ⊆ Ω w/t A
                      → Ω ∋ k := T
                      → Ω ≡ Γ'
s-unsol-sol-helper-eq (⊢o-var-^ x) (⊢c-var-∙ inΔ) inst (ext-var x₁) inΩ = ⊥-elim (inst-false-1 x inst inΔ)
s-unsol-sol-helper-eq (⊢o-var-^ x) (⊢c-var-= inΔ) inst (ext-var x₁) inΩ
  with refl ← inst-affect-one inst x inΔ = ⊆/x-unique x₁ (inst-⊆/x inst) inΩ (inst-∋:= inst)
s-unsol-sol-helper-eq (⊢o-arr-l opnA) (⊢c-arr cloA cloA₁) inst (ext-arr extA extA₁) inΩ
  with inΩ' ← ⊆/-^in-=out extA (inst-⊢o-⊢c-ε opnA inst cloA) (inst-∋^ inst)
  with refl ← s-unsol-sol-helper-eq opnA cloA inst extA (∋=-∋:=-⊆ inΩ' inΩ (⊆/-⊆ extA₁)) = sym (⊆/-⊢c-eq extA₁ cloA₁)
s-unsol-sol-helper-eq (⊢o-arr-r opnA) (⊢c-arr cloA cloA₁) inst (ext-arr extA extA₁) inΩ with ⊆/-openclose extA
... | inj₁ opnA
  with inΩ' ← ⊆/-^in-=out extA (inst-⊢o-⊢c-ε opnA inst cloA) (inst-∋^ inst)
  with refl ← s-unsol-sol-helper-eq opnA cloA inst extA (∋=-∋:=-⊆ inΩ' inΩ (⊆/-⊆ extA₁)) = sym (⊆/-⊢c-eq extA₁ cloA₁)
... | inj₂ cloA'
  with refl ← ⊆/-⊢c-eq extA cloA'
  = s-unsol-sol-helper-eq opnA cloA₁ inst extA₁ inΩ
s-unsol-sol-helper-eq {T = T} (⊢o-∀ opnA) (⊢c-∀ cloA) inst (ext-∀ extA) inΩ
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  with refl ← s-unsol-sol-helper-eq opnA cloA (⟹∙S inst upT) extA (S∙ inΩ upT) = refl


⊆/x-neq-∋^ : Γ ∋^ k
           → Γ ⊆ Δ w/v X
           → k ≢ X
           → Δ ∋^ k
⊆/x-neq-∋^ Z (ext-Z^ regΓ regA) neq = ⊥-elim (neq refl)
⊆/x-neq-∋^ Z (ext-S^ ext) neq = Z
⊆/x-neq-∋^ (S∙ inΓ) (ext-Z∙ regΓ) neq = S∙ inΓ
⊆/x-neq-∋^ (S∙ inΓ) (ext-S∙ ext) neq = S∙ (⊆/x-neq-∋^ inΓ ext (≢-pred neq))
⊆/x-neq-∋^ (S= inΓ) (ext-Z= regΓ regA) neq = S= inΓ
⊆/x-neq-∋^ (S= inΓ) (ext-S= ext regA) neq = S= (⊆/x-neq-∋^ inΓ ext (≢-pred neq))
⊆/x-neq-∋^ (S^ inΓ) (ext-Z^ regΓ regA) neq = S= inΓ
⊆/x-neq-∋^ (S^ inΓ) (ext-S^ ext) neq = S^ (⊆/x-neq-∋^ inΓ ext (≢-pred neq))

inst-∃ : Γ ∋^ k
         → Δ ∋ k := T -- simply for T is shifted
         → Γ ⊆ Δ
         → ∃[ Γ' ]([ T / k ] Γ ⟹ Γ')
inst-∃ Z (Z {A = A} up) (evar-sol {Γ = Γ} ext regA) = ⟨ Γ ,= A , ⟹^0 up (⊆-⊢r' regA ext) (⊆-sregular ext) ⟩
inst-∃ (S∙ inΓ) (S∙ inΔ up) (uvar ext) = ⟨ inst-∃ inΓ inΔ ext .proj₁ ,∙ , ⟹∙S (inst-∃ inΓ inΔ ext .proj₂) up ⟩
inst-∃ (S= inΓ) (S= {B = B} inΔ up) (svar ext regA) = ⟨ inst-∃ inΓ inΔ ext .proj₁ ,= B , ⟹=S (inst-∃ inΓ inΔ ext .proj₂) up regA ⟩
inst-∃ (S^ inΓ) (S^ inΔ up) (evar ext) = ⟨ inst-∃ inΓ inΔ ext .proj₁ ,^ , ⟹^S (inst-∃ inΓ inΔ ext .proj₂) up ⟩
inst-∃ (S^ inΓ) (S= inΔ up) (evar-sol ext regA) = ⟨ inst-∃ inΓ inΔ ext .proj₁ ,^ , ⟹^S (inst-∃ inΓ inΔ ext .proj₂) up ⟩

inst-seq : [ A / X ] Γ ⟹ Δ
         → [ B / k ] Δ ⟹ Δ'
         → [ B / k ] Γ ⟹ Γ'
         → k ≢ X
         → [ A / X ] Γ' ⟹ Δ'
inst-seq (⟹^0 up regA env) (⟹=S inst2 up1 regB) (⟹^S inst3 up2) neq
  with refl ← ↑ty-unique-inver up1 up2
  with refl ← inst-unique inst2 inst3
  = ⟹^0 up (⊆-⊢r regA (inst-⊆ inst2)) (⊆-sregular' (inst-⊆ inst2))
inst-seq (⟹^S inst1 up1) (⟹^0 up regA env) (⟹^0 up₁ regA₁ env₁) neq
  with refl ← ↑ty-unique-inver up up₁
  = ⟹=S inst1 up1 regA₁
inst-seq (⟹^S inst1 up1) (⟹^S inst2 up2) (⟹^S inst3 up3) neq
  with refl ← ↑ty-unique-inver up3 up2
  = ⟹^S (inst-seq inst1 inst2 inst3 (≢-pred neq)) up1
inst-seq (⟹∙S inst1 up1) (⟹∙S inst2 up2) (⟹∙S inst3 up3) neq
  with refl ← ↑ty-unique-inver up3 up2
  = ⟹∙S (inst-seq inst1 inst2 inst3 (≢-pred neq)) up1
inst-seq (⟹=S inst1 up1 regB) (⟹=S inst2 up2 regB₁) (⟹=S inst3 up3 regB₂) neq
  with refl ← ↑ty-unique-inver up3 up2
  = ⟹=S (inst-seq inst1 inst2 inst3 (≢-pred neq)) up1 (⊆-⊢r regB (inst-⊆ inst3))


ss-irrev-inst : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
              → [ T / k ] Γ ⟹ Γ'
              → [ T / k ] Δ ⟹ Δ'
              → Γ' ⊢ A ⌞ ≤ ⌝ B ⊣ Δ'
ss-irrev-inst (s-int regΓ) inst1 inst2
  with refl ← inst-unique inst1 inst2
  = s-int (⊆-sregular' (inst-⊆ inst1))
ss-irrev-inst (s-var-∙ regΓ inΔ) inst1 inst2
  with refl ← inst-unique inst1 inst2
  = s-var-∙ (⊆-sregular' (inst-⊆ inst1)) (⊆-∋∙ inΔ (inst-⊆ inst1))
ss-irrev-inst {k = k} (s-ex-l^ {X = X} inst) inst1 inst2 with k #≟ X
... | yes refl = ⊥-elim (∋^-∋=-false (inst-∋^ inst2) (∋:=to∋= (inst-∋:= inst)))
... | no ¬p = s-ex-l^ (inst-seq inst inst2 inst1 ¬p)
ss-irrev-inst {k = k} (s-ex-r^ {X = X} inst) inst1 inst2 with k #≟ X
... | yes refl = ⊥-elim (∋^-∋=-false (inst-∋^ inst2) (∋:=to∋= (inst-∋:= inst)))
... | no ¬p = s-ex-r^ (inst-seq inst inst2 inst1 ¬p)
ss-irrev-inst (s-ex-l= regΓ x-in) inst1 inst2
  with refl ← inst-unique inst1 inst2
  = s-ex-l= (⊆-sregular' (inst-⊆ inst1)) (⊆-∋:= x-in (inst-⊆ inst1))
ss-irrev-inst (s-ex-r= regΓ x-in) inst1 inst2
  with refl ← inst-unique inst1 inst2
  = s-ex-r= (⊆-sregular' (inst-⊆ inst1)) (⊆-∋:= x-in (inst-⊆ inst1))
ss-irrev-inst (s-arr ss ss₁) inst1 inst2
  with inΩ ← ⊆-∋^-middle (inst-∋^ inst1) (inst-∋^ inst2) (ss-⊆ ss) (ss-⊆ ss₁)
  with ⟨ Ω' , instΩ ⟩ ← inst-∃ inΩ (inst-∋:= inst2) (⊆-trans (ss-⊆ ss₁) (inst-⊆ inst2))
  = s-arr (ss-irrev-inst ss inst1 instΩ) (ss-irrev-inst ss₁ instΩ inst2)
ss-irrev-inst {T = T} (s-∀ ss) inst1 inst2
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = s-∀ (ss-irrev-inst ss (⟹∙S inst1 upT) (⟹∙S inst2 upT))



ss-unsol-sol : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
             → Δ ∋ k := T
             → [ T / k ] Γ ⟹ Γ'
             → Γ' ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
ss-unsol-sol (s-int regΓ) inΔ inst = ⊥-elim (∋^-∋=-false (inst-∋^ inst) (∋:=to∋= inΔ))
ss-unsol-sol (s-var-∙ regΓ inΔ₁) inΔ inst = ⊥-elim (∋^-∋=-false (inst-∋^ inst) (∋:=to∋= inΔ))
ss-unsol-sol {k = k} (s-ex-l^ {X = X} inst₁) inΔ inst with k #≟ X
... | yes refl
  with refl ← ∋:=-unique (inst-∋:= inst₁) inΔ
  with refl ← inst-unique inst inst₁
  = s-ex-l= (⊆-sregular' (inst-⊆ inst)) inΔ
... | no ¬p
  with inΔ' ← ⊆/x-neq-∋^ (inst-∋^ inst) (inst-⊆/x inst₁) ¬p
  = ⊥-elim (∋^-∋=-false inΔ' (∋:=to∋= inΔ))
ss-unsol-sol {k = k} (s-ex-r^ {X = X} inst₁) inΔ inst with k #≟ X
... | yes refl
  with refl ← ∋:=-unique (inst-∋:= inst₁) inΔ
  with refl ← inst-unique inst inst₁
  = s-ex-r= (⊆-sregular' (inst-⊆ inst)) inΔ
... | no ¬p
  with inΔ' ← ⊆/x-neq-∋^ (inst-∋^ inst) (inst-⊆/x inst₁) ¬p
  = ⊥-elim (∋^-∋=-false inΔ' (∋:=to∋= inΔ))
ss-unsol-sol (s-ex-l= regΓ x-in) inΔ inst = ⊥-elim (∋^-∋=-false (inst-∋^ inst) (∋:=to∋= inΔ))
ss-unsol-sol (s-ex-r= regΓ x-in) inΔ inst = ⊥-elim (∋^-∋=-false (inst-∋^ inst) (∋:=to∋= inΔ))
ss-unsol-sol (s-arr s s₁) inΔ inst with s-⊆-exsol (ss-⊆ s) (inst-∋^ inst)
... | is-ex inΓ
  with ⟨ Ω' , instΩ ⟩ ← inst-∃ inΓ inΔ (ss-⊆ s₁)
  = s-arr (ss-irrev-inst s inst instΩ) (ss-unsol-sol s₁ inΔ instΩ)
... | is-sol inΓ = s-arr (ss-unsol-sol s (∋=-∋:=-⊆ inΓ inΔ (ss-⊆ s₁)) inst) s₁
ss-unsol-sol {T = T} (s-∀ s) inΔ inst
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = s-∀ (ss-unsol-sol s (S∙ inΔ upT) (⟹∙S inst upT))


infix 3 _⊢wf_
data _⊢wf_ : Env n m → Type m → Set where
  ⊢wf-int :
      Δ ⊢wf Int
  ⊢wf-var-∙ :
      (inΔ : Δ ∋∙ X)
    → Δ ⊢wf ‶ X
  ⊢wf-var-= :
      (inΔ : Δ ∋= X)
    → Δ ⊢wf ‶ X
  ⊢wf-var-^ :
      Δ ∋^ X
    → Δ ⊢wf ‶ X
  ⊢wf-arr :
      Δ ⊢wf A
    → Δ ⊢wf B
    → Δ ⊢wf (A `→ B)
  ⊢wf-∀ :
      Δ ,∙ ⊢wf A
    → Δ ⊢wf `∀ A


⊆-∋=-⊢wf : Γ ⊆ Δ
         → Δ ∋= X
         → Γ ⊢wf ‶ X
⊆-∋=-⊢wf (uvar ext) (S∙ inΔ) with ⊆-∋=-⊢wf ext inΔ
... | ⊢wf-var-∙ inΔ₁ = ⊢wf-var-∙ (S∙ inΔ₁)
... | ⊢wf-var-= inΔ₁ = ⊢wf-var-= (S∙ inΔ₁)
... | ⊢wf-var-^ x = ⊢wf-var-^ (S∙ x)
⊆-∋=-⊢wf (evar ext) (S^ inΔ) with ⊆-∋=-⊢wf ext inΔ
... | ⊢wf-var-∙ inΔ₁ = ⊢wf-var-∙ (S^ inΔ₁)
... | ⊢wf-var-= inΔ₁ = ⊢wf-var-= (S^ inΔ₁)
... | ⊢wf-var-^ x = ⊢wf-var-^ (S^ x)
⊆-∋=-⊢wf (evar-sol ext regA) Z = ⊢wf-var-^ Z
⊆-∋=-⊢wf (evar-sol ext regA) (S= inΔ) with ⊆-∋=-⊢wf ext inΔ
... | ⊢wf-var-∙ inΔ₁ = ⊢wf-var-∙ (S^ inΔ₁)
... | ⊢wf-var-= inΔ₁ = ⊢wf-var-= (S^ inΔ₁)
... | ⊢wf-var-^ x = ⊢wf-var-^ (S^ x)
⊆-∋=-⊢wf (svar ext regA) Z = ⊢wf-var-= Z
⊆-∋=-⊢wf (svar ext regA) (S= inΔ) with ⊆-∋=-⊢wf ext inΔ
... | ⊢wf-var-∙ inΔ₁ = ⊢wf-var-∙ (S= inΔ₁)
... | ⊢wf-var-= inΔ₁ = ⊢wf-var-= (S= inΔ₁)
... | ⊢wf-var-^ x = ⊢wf-var-^ (S= x)

⊆-∋^-⊢wf : Γ ⊆ Δ
         → Δ ∋^ X
         → Γ ⊢wf ‶ X
⊆-∋^-⊢wf (uvar ext) (S∙ inΔ) with ⊆-∋^-⊢wf ext inΔ
... | ⊢wf-var-∙ inΔ₁ = ⊢wf-var-∙ (S∙ inΔ₁)
... | ⊢wf-var-= inΔ₁ = ⊢wf-var-= (S∙ inΔ₁)
... | ⊢wf-var-^ x = ⊢wf-var-^ (S∙ x)
⊆-∋^-⊢wf (evar ext) Z = ⊢wf-var-^ Z
⊆-∋^-⊢wf (evar ext) (S^ inΔ) with ⊆-∋^-⊢wf ext inΔ
... | ⊢wf-var-∙ inΔ₁ = ⊢wf-var-∙ (S^ inΔ₁)
... | ⊢wf-var-= inΔ₁ = ⊢wf-var-= (S^ inΔ₁)
... | ⊢wf-var-^ x = ⊢wf-var-^ (S^ x)
⊆-∋^-⊢wf (evar-sol ext regA) (S= inΔ) with ⊆-∋^-⊢wf ext inΔ
... | ⊢wf-var-∙ inΔ₁ = ⊢wf-var-∙ (S^ inΔ₁)
... | ⊢wf-var-= inΔ₁ = ⊢wf-var-= (S^ inΔ₁)
... | ⊢wf-var-^ x = ⊢wf-var-^ (S^ x)
⊆-∋^-⊢wf (svar ext regA) (S= inΔ) with ⊆-∋^-⊢wf ext inΔ
... | ⊢wf-var-∙ inΔ₁ = ⊢wf-var-∙ (S= inΔ₁)
... | ⊢wf-var-= inΔ₁ = ⊢wf-var-= (S= inΔ₁)
... | ⊢wf-var-^ x = ⊢wf-var-^ (S= x)

⊢wf-⊆ : Δ ⊢wf A
      → Γ ⊆ Δ
      → Γ ⊢wf A
⊢wf-⊆ ⊢wf-int ext = ⊢wf-int
⊢wf-⊆ (⊢wf-var-∙ inΔ) ext = ⊢wf-var-∙ (⊆-∋∙' inΔ ext)
⊢wf-⊆ (⊢wf-var-= inΔ) ext = ⊆-∋=-⊢wf ext inΔ
⊢wf-⊆ (⊢wf-var-^ x) ext = ⊆-∋^-⊢wf ext x
⊢wf-⊆ (⊢wf-arr wfA wfA₁) ext = ⊢wf-arr (⊢wf-⊆ wfA ext) (⊢wf-⊆ wfA₁ ext)
⊢wf-⊆ (⊢wf-∀ wfA) ext = ⊢wf-∀ (⊢wf-⊆ wfA (uvar ext))


⊆/x-⊢wf : Γ ⊆ Δ w/v X
        → Γ ⊢wf ‶ X
⊆/x-⊢wf (ext-Z^ regΓ regA) = ⊢wf-var-^ Z
⊆/x-⊢wf (ext-Z∙ regΓ) = ⊢wf-var-∙ Z
⊆/x-⊢wf (ext-Z= regΓ regA) = ⊢wf-var-= Z
⊆/x-⊢wf (ext-S^ ext) with ⊆/x-⊢wf ext
... | ⊢wf-var-∙ inΔ = ⊢wf-var-∙ (S^ inΔ)
... | ⊢wf-var-= inΔ = ⊢wf-var-= (S^ inΔ)
... | ⊢wf-var-^ x = ⊢wf-var-^ (S^ x)
⊆/x-⊢wf (ext-S∙ ext) with ⊆/x-⊢wf ext
... | ⊢wf-var-∙ inΔ = ⊢wf-var-∙ (S∙ inΔ)
... | ⊢wf-var-= inΔ = ⊢wf-var-= (S∙ inΔ)
... | ⊢wf-var-^ x = ⊢wf-var-^ (S∙ x)
⊆/x-⊢wf (ext-S= ext regA) with ⊆/x-⊢wf ext
... | ⊢wf-var-∙ inΔ = ⊢wf-var-∙ (S= inΔ)
... | ⊢wf-var-= inΔ = ⊢wf-var-= (S= inΔ)
... | ⊢wf-var-^ x = ⊢wf-var-^ (S= x)
⊆/x-⊢wf (ext-mark x x₁) = ⊢wf-var-∙ (S⋈ x₁)

⊆/-⊢wf : Γ ⊆ Δ w/t A
       → Γ ⊢wf A
⊆/-⊢wf (ext-int x) = ⊢wf-int
⊆/-⊢wf (ext-var x) = ⊆/x-⊢wf x
⊆/-⊢wf (ext-arr ext ext₁) = ⊢wf-arr (⊆/-⊢wf ext) (⊢wf-⊆ (⊆/-⊢wf ext₁) (⊆/-⊆ ext))
⊆/-⊢wf (ext-∀ ext) = ⊢wf-∀ (⊆/-⊢wf ext)

inst-openclose : Γ ⊢wf A
               → [ T / k ] Γ ⟹ Γ'
               → Γ' ⊢o A ⊎ Γ' ⊢c A
inst-openclose ⊢wf-int inst = inj₂ ⊢c-int
inst-openclose (⊢wf-var-∙ inΔ) inst = inj₂ (⊢c-var-∙ (⊆-∋∙ inΔ (inst-⊆ inst)))
inst-openclose (⊢wf-var-= inΔ) inst = inj₂ (⊢c-var-= (⊆-∋= inΔ (inst-⊆ inst)))
inst-openclose {k = k} (⊢wf-var-^ {X = X} x) inst with X #≟ k
... | yes refl = inj₂ (⊢c-var-= (inst-∋= inst))
... | no ¬p = inj₁ (⊢o-var-^ (⊆/x-neq-∋^ x (inst-⊆/x inst) ¬p))
inst-openclose (⊢wf-arr wfA wfA₁) inst with inst-openclose wfA inst | inst-openclose wfA₁ inst
... | inj₁ x | inj₁ x₁ = inj₁ (⊢o-arr-l x)
... | inj₁ x | inj₂ y = inj₁ (⊢o-arr-l x)
... | inj₂ y | inj₁ x = inj₁ (⊢o-arr-r x)
... | inj₂ y | inj₂ y₁ = inj₂ (⊢c-arr y y₁)
inst-openclose {T = T} (⊢wf-∀ wfA) inst
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  with inst-openclose wfA (⟹∙S inst upT)
... | inj₁ x = inj₁ (⊢o-∀ x)
... | inj₂ y = inj₂ (⊢c-∀ y)



s-unsol-sol : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
            → Δ ∋ k := T
            → [ T / k ] Γ ⟹ Γ'
            → Γ' ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
s-unsol-sol (s-empty regΓ cloA grd) inΔ inst = ⊥-elim (∋^-∋=-false (inst-∋^ inst) (∋:=to∋= inΔ))
s-unsol-sol (s-type ss) inΔ inst = s-type (ss-unsol-sol ss inΔ inst)
s-unsol-sol (s-term-c cloA ap ⊢e s) inΔ inst
  with extΓ ← inst-⊆ inst
  = s-term-c (⊆-⊢c cloA extΓ) (⊆-⊢c-≫' extΓ cloA ap) (t-irrev-⊆ ⊢e extΓ) (s-unsol-sol s inΔ inst)
s-unsol-sol (s-term-o opnA ⊢e ss s) inΔ inst
  with wfA ← ⊆/-⊢wf (ss--⊆/ ss)
  with extΓ ← inst-⊆ inst
  with inst-openclose wfA inst
... | inj₁ opnA
  with s-⊆-exsol (ss-⊆ ss) (inst-∋^ inst)
... | is-ex inΓ
  with ⟨ Ω' , instΩ ⟩ ← inst-∃ inΓ inΔ (s-⊆ s)
  = s-term-o opnA (t-irrev-⊆ ⊢e extΓ) (ss-irrev-inst ss inst instΩ) (s-unsol-sol s inΔ instΩ)
... | is-sol inΔ'
  = s-term-o opnA (t-irrev-⊆ ⊢e extΓ) (ss-unsol-sol ss (∋=-∋:=-⊆ inΔ' inΔ (s-⊆ s)) inst) s
s-unsol-sol (s-term-o opnA ⊢e ss s) inΔ inst | inj₂ cloA
  with inΩ' ← ⊆/-^in-=out (ss--⊆/ ss) (inst-⊢o-⊢c-ε opnA inst cloA) (inst-∋^ inst)
  with refl ← s-unsol-sol-helper-eq opnA cloA inst (ss--⊆/ ss) (∋=-∋:=-⊆ inΩ' inΔ (s-⊆ s))
  = s-term-c cloA (ss-≫-- ss) (subsumption0 (t-irrev-⊆ ⊢e extΓ)) s
s-unsol-sol {T = T} (s-∀l-y pk upB s upᶜ upᵉ upC upD) inΔ inst
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  with reg-S= r regA ← s-env-in s
  = s-∀l-y pk upB (s-unsol-sol s (S= inΔ upT) (⟹=S inst upT regA)) upᶜ upᵉ upC upD
s-unsol-sol {T = T} (s-∀l-n-y ¬pk s upᶜ upᵉ upC upD) inΔ inst
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = s-∀l-n-y ¬pk (s-unsol-sol s (S= inΔ upT) (⟹^S inst upT)) upᶜ upᵉ upC upD
s-unsol-sol {T = T} (s-∀l-n-n ¬pk s upᶜ upᵉ upC upD) inΔ inst
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = s-∀l-n-n ¬pk (s-unsol-sol s (S^ inΔ upT) (⟹^S inst upT)) upᶜ upᵉ upC upD
s-unsol-sol {T = T} (s-tapp s upᶜ) inΔ inst
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  with reg-S= r regA ← s-env-in s
  = s-tapp (s-unsol-sol s (S= inΔ upT) (⟹=S inst upT regA)) upᶜ
s-unsol-sol (s-svar-term x s) inΔ inst = ⊥-elim (∋^-∋=-false (inst-∋^ inst) (∋:=to∋= inΔ))
s-unsol-sol (s-svar-tapp x s) inΔ inst = ⊥-elim (∋^-∋=-false (inst-∋^ inst) (∋:=to∋= inΔ))
s-unsol-sol {k = k} (s-evar-infers {X = X} (infs-s ⊢e infs) inst₁) inΔ inst
  with extΓ ← inst-⊆ inst
  with k #≟ X
... | yes refl
  with refl ← ∋:=-unique inΔ (inst-∋:= inst₁)
  with refl ← inst-unique inst inst₁
  with ⊢r-arr regA regB ← ∋:=-⊢r (⊆-sregular' extΓ) inΔ
  = s-svar-term inΔ (s-term-c (⊢r-⊢c regA) (⊢r-≫-eq regA)
                (subsumption0 (t-irrev-⊆ ⊢e extΓ))
                (infs-sub' (infs-irrev-⊆ infs extΓ) (⊆-sregular' extΓ)))
... | no ¬p
  with inΔ' ← ⊆/x-neq-∋^ (inst-∋^ inst) (inst-⊆/x inst₁) ¬p
  = ⊥-elim (∋^-∋=-false inΔ' (∋:=to∋= inΔ))

s-unsol-sol0 : Γ ,^ ⊢ A ≤⁺ Σ ⊣ Δ ,= B ↪ C
             → Γ ,= B ⊢ A ≤⁺ Σ ⊣ Δ ,= B ↪ C
s-unsol-sol0 {B = B} s
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with reg-S= regA regA₁ ← s-env-out s
  with evar-sol ext regA₂ ← s-⊆ s
  = s-unsol-sol s (Z upB) (⟹^0 upB (⊆-⊢r' regA₂ ext) (⊆-sregular ext))
