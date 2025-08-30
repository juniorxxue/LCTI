module Implicit.Interm2Algo.Inst where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm2Algo.EnvDiff

postulate
  infs-sub' : 𝕣 Γ ⊨ Σ ⟹ A
          → SRegular Γ
          → Γ ⊢ A ≤⁺ Σ ⊣ Γ ↪ A


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


∋=-∋:=-⊆ : Γ ∋= k
         → Δ ∋ k := T
         → Γ ⊆ Δ
         → Γ ∋ k := T
∋=-∋:=-⊆ Z (Z up) (svar ext regA) = Z up
∋=-∋:=-⊆ (S∙ in1) (S∙ in2 up) (uvar ext) = S∙ (∋=-∋:=-⊆ in1 in2 ext) up
∋=-∋:=-⊆ (S^ in1) (S^ in2 up) (evar ext) = S^ (∋=-∋:=-⊆ in1 in2 ext) up
∋=-∋:=-⊆ (S^ in1) (S= in2 up) (evar-sol ext regA) = S^ (∋=-∋:=-⊆ in1 in2 ext) up
∋=-∋:=-⊆ (S= in1) (S= in2 up) (svar ext regA) = S= (∋=-∋:=-⊆ in1 in2 ext) up


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
  = s-term-c {!!} {!!} {!subsumption0 ⊢e!} {!!}
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
  = s-unsol-sol s (Z upB) (⟹^0 upB {!!} {!!})
