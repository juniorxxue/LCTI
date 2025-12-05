module Implicit.Interm2Algo.Main where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm.All

open import Implicit.Interm2Algo.Counter2Context
open import Implicit.Interm2Algo.ReExtension
open import Implicit.Interm2Algo.ExtIrrev
open import Implicit.Interm2Algo.EnvDiff
open import Implicit.Interm2Algo.OpenClose
open import Implicit.Interm2Algo.Find
open import Implicit.Interm2Algo.AuxLemmas
open import Implicit.Interm2Algo.NewSpine
open import Implicit.Interm2Algo.Inst


data WF1 : Env n m → Set where
  wf1-base : WF1 (Γ ⋈)
  wf1-sol  : WF1 Δ
           → WF1 (Δ ,= A)
  wf1-ex   : WF1 Δ
           → WF1 (Δ ,^)


data WF2 : Env n m → Set where
  wf2-base : WF1 Δ
           → WF2 Δ
  wf2-uni : WF2 Δ
          → WF2 (Δ ,∙)

data WFC : Env n m → Counter m → Set where
  wfc-z : WF1 Γ
        → WFC Γ Z
  wfc-∞ : WF2 Γ
        → WFC Γ ∞
  wfc-𝕚 : WF1 Γ
        → WFC Γ (𝕚 j)
  wfc-𝕔 : WF1 Γ
        → WFC Γ (𝕔 j)
  wfc-𝕥 : WF1 Γ
        → WFC Γ (𝕥₍ A ₎ j)

wf1-wfcj : WF1 Δ
         → WFC Δ j
wf1-wfcj {j = Z} wf1 = wfc-z wf1
wf1-wfcj {j = ∞} wf1 = wfc-∞ (wf2-base wf1)
wf1-wfcj {j = 𝕚 j} wf1 = wfc-𝕚 wf1
wf1-wfcj {j = 𝕔 j} wf1 = wfc-𝕔 wf1
wf1-wfcj {j = 𝕥₍ x ₎ j} wf1 = wfc-𝕥 wf1

wf1-⊆' : Γ ⊆ Δ
       → WF1 Δ
       → WF1 Γ
wf1-⊆' (evar ext1) (wf1-ex wfΔ) = wf1-ex (wf1-⊆' ext1 wfΔ)
wf1-⊆' (evar-sol ext1 regA) (wf1-sol wfΔ) = wf1-ex (wf1-⊆' ext1 wfΔ)
wf1-⊆' (svar ext1 regA) (wf1-sol wfΔ) = wf1-sol (wf1-⊆' ext1 wfΔ)
wf1-⊆' (mark regΓ) wfΔ = wfΔ


inst-∃-A : Γ ⊢r A
         → WF1 Γ
         → SRegular Γ
         → Γ ∋^ k
         → ∃[ Δ ]([ A / k ] Γ ⟹ Δ)
inst-∃-A {Γ = Δ ,^} regA (wf1-ex wfΓ) (reg-S^ regΓ) Z
  with ⟨ A' , pupA ⟩ ← ↑ty-surjective (⊢r-^∈-¬ε regA Z) = ⟨ Δ ,= A' , ⟹^0 pupA (⊢r-strengthen^0 regA pupA) regΓ ⟩
inst-∃-A {A = T} regA (wf1-sol wfΓ) (reg-S= {A = A} regΓ regA₁) (S= inΓ)
    with ⟨ T' , pupA ⟩ ← ↑ty-surjective (⊢r-=∈-¬ε regA Z)
    with ⟨ Δ' , inst' ⟩ ← inst-∃-A (⊢r-strengthen=0 regA pupA) wfΓ regΓ inΓ
    = ⟨ (Δ' ,= A) , ⟹=S inst' pupA regA₁ ⟩
inst-∃-A {A = T} regA (wf1-ex wfΓ) (reg-S^ regΓ) (S^ inΓ)
  with ⟨ T' , pupA ⟩ ← ↑ty-surjective (⊢r-^∈-¬ε regA Z)
  with ⟨ Δ' , inst' ⟩ ← inst-∃-A (⊢r-strengthen^0 regA pupA) wfΓ regΓ inΓ
  = ⟨ Δ' ,^ , ⟹^S inst' pupA ⟩

sound-peek : A ~pk~ Σ w/ k
           → Γ ⊢ ⟨ j , B ⟩ ~s Σ
           → peek A k j
sound-peek (pk-type x) ~∞ = peek-base x
sound-peek (pk-term pk) (~I ⊢e ~j) = peek-arr-i (sound-peek pk ~j)
sound-peek (pk-term pk) (~C ⊢e ~j) = peek-arr-c (sound-peek pk ~j)
sound-peek (pk-∀l pk upΣ upe) (~I {j = j} {A = A} {B = B} ⊢e ~j)
  with ⟨ j' , upj ⟩ ← ↑tyʲ0-total j
  with ⟨ A' , upA ⟩ ← ↑ty0-total A
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  = peek-∀-i (sound-peek pk (~weaken^0 (~I ⊢e ~j) (↑ty-arr upA upB) (↑tyᶜ-e upe upΣ) (↑tyʲ-𝕚 upj))) upj
sound-peek (pk-∀l pk upΣ upe) (~C {A% = A} {j = j} {B = B} ⊢e ~j)
  with ⟨ j' , upj ⟩ ← ↑tyʲ0-total j
  with ⟨ A' , upA ⟩ ← ↑ty0-total A
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  = peek-∀-c (sound-peek pk (~weaken^0 (~C ⊢e ~j) (↑ty-arr upA upB) (↑tyᶜ-e upe upΣ) (↑tyʲ-𝕔 upj))) upj
sound-peek (pk-tapp pk upΣ) (~T {j = j} ~j st)
  with ⟨ j' , upj ⟩ ← ↑tyʲ0-total j
  = peek-∀-t (sound-peek pk (~weaken^0 ~j st upΣ upj)) upj

complete-¬peek : ¬ (peek A k j)
               → Γ ⊢ ⟨ j , B ⟩ ~s Σ
               → ¬ (A ~pk~ Σ w/ k)
complete-¬peek npk ~j = λ x → npk (sound-peek x ~j)


complete-s :  Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → WFC Δ j
            → Γ ⊆ Δ w/t A w/c j
            → Γ ⊢ ⟨ j , B ⟩ ~s Σ
            → Complete A j Σ Γ Δ B
complete-s {j = Z} (s-refl regΔ cloA grd) wfc (⊆Z regΓ cloA') ~Z = normal (⊢c-¬ε' cloA) (s-empty regΔ cloA grd)
complete-s {j = ∞} s wfc (⊆∞ ext) ~∞ = ss-complete (complete-ss+ s ext)
complete-s {j = 𝕚 j} (s-arr₂ s s₁) (wfc-𝕚 x) (⊆I ext ext₁) (~I ⊢e j~Σ) with ⊆/-openclose ext
-- A is open
complete-s {j = 𝕚 j} (s-arr₂ {A = A} s s₁) (wfc-𝕚 x) (⊆I ext ext₁) (~I ⊢e ~j) | inj₁ opnA
  with ⟨ Ψ , diff ⟩ ← ⅆ-total (⊆/-⊆ ext) (⊆/c-⊆ ext₁)
  with ih ← complete-ss- {Γ = Ψ} s (ⅆ-⊆/ diff ext)
  with ih' ← s--subirrev-final ih diff (⊆/-⊢c ext)
  with complete-s s₁ (wf1-wfcj x) ext₁ (~irrev ~j (⊆/-⊆ ext))
... | normal cond s₂ = normal
  (λ where ⟨ k , ⟨ ε-arr x' inB , inΓ ⟩ ⟩ → cond ⟨ k , ⟨ inB , ⊆/-^in-^out (ss--⊆/ ih') x' inΓ ⟩ ⟩)
  (s-term-o opnA ⊢e ih' s₂)
... | special {k = k} inA inΓ^ tail newΔ s₂ with ε-dec {k = k} {A = A}
... | inj₁ inA' = ⊥-elim (complete-false₂ ext inA' inΓ^)
... | inj₂ ¬inA = special (ε-arr ¬inA inA) (⊆-^out-^in inΓ^ (ss-⊆ ih')) (ett-arr tail) newΔ (s-term-o opnA ⊢e ih' s₂)
-- A is close
complete-s {j = 𝕚 j} (s-arr₂ {A = A} s s₁) (wfc-𝕚 x) (⊆I ext ext₁) (~I ⊢e ~j) | inj₂ cloA
  with refl ← ⊆/-⊢c-eq ext cloA
  with grd ← ⊆-⊢c-≫ (⊆/c-⊆ ext₁) cloA (s--≫ s)
  with complete-s s₁ (wf1-wfcj x) ext₁ ~j
... | normal cond s₂ = normal (λ cond' → cond (case₁ cond')) (s-term-c cloA grd (subsumption0 ⊢e) s₂)
... | special {k = k} inA inΓ^ tail newΔ s₂ with ε-dec {k = k} {A = A}
... | inj₁ inA' = ⊥-elim (⊢c-^∈-false inA' inΓ^ cloA)
... | inj₂ ¬inA = special (ε-arr ¬inA inA) inΓ^ (ett-arr tail) newΔ (s-term-c cloA grd (subsumption0 ⊢e) s₂)
complete-s {j = 𝕚 j} (s-∀l s ic fd upC upD (↑tyʲ-𝕚 upj)) (wfc-𝕚 x) (⊆∀-I ext upj₁) ~j'@(~I {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S= r regA ← s-sregular s
  with refl ← ↑tyʲ-unique upj upj₁
  with weaken-j~ ← (~weaken^0 (~I ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕚 upj)
  with complete-s s (wfc-𝕚 (wf1-sol x)) (⊆/c-irrev-^=0 ext fd regA) weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₄ (case₂ cond'))) (s-∀l-n-y s₁ upΣ upe upC upD)
... | special {k = #0} inA Z tail (=⟹=0 up regA₁ env) s₁ = normal (case₅ inA) (s-∀l-n-y s₁ upΣ upe upC upD)
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹=S newΔ up1 regB) s₁ = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ
              (s-∀l-n-y s₁ upΣ upe upC upD)
complete-s  {j = 𝕚 j} (s-∀l-peek {B = B} s case-𝕚 pk upC upD (↑tyʲ-𝕚 upj)) (wfc-𝕚 x) (⊆∀-I ext upj₁) ~j'@(~I {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with reg-S= r regA ← s-sregular s
  with refl ← ↑tyʲ-unique upj upj₁
  with weaken-j~ ← (~weaken^0 (~I ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕚 upj)
  with com-pk ← (peek-a-~pk~ (peek→peek-a s pk (Z upB)) weaken-j~)
  with complete-s s (wfc-𝕚 (wf1-sol x)) (⊆/c-irrev-^=0' ext regA) weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₄ (case₂ cond'))) (s-∀l-y com-pk upB (s-unsol-sol0 s₁) upΣ upe upC upD)
... | special {k = #0} inA Z tail (=⟹=0 up regA₁ env) s₁
  with refl ← pk-tail-eq com-pk tail inA (s-id' s₁)
  = normal (case₅ inA) (s-∀l-y com-pk up (s-unsol-sol0 s₁) upΣ upe upC upD) -- some uniqueness needed
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹=S newΔ up1 regB) s₁
  = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ (s-∀l-y com-pk upB (s-unsol-sol0 s₁) upΣ upe upC upD)

complete-s {j = 𝕔 j} (s-∀l s ic fd upC upD (↑tyʲ-𝕔 upj)) (wfc-𝕔 x) (⊆∀-C ext upj₁) ~j'@(~C {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S= r regA ← s-sregular s
  with refl ← ↑tyʲ-unique upj upj₁
  with weaken-j~ ← (~weaken^0 (~C ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕔 upj)
  with complete-s s (wfc-𝕔 (wf1-sol x)) (⊆/c-irrev-^=0 ext fd regA) weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₄ (case₂ cond'))) (s-∀l-n-y s₁ upΣ upe upC upD)
... | special {k = #0} inA Z tail (=⟹=0 up regA₁ env) s₁ = normal (case₅ inA) (s-∀l-n-y s₁ upΣ upe upC upD)
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹=S newΔ up1 regB) s₁ = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ
              (s-∀l-n-y s₁ upΣ upe upC upD)
complete-s {j = 𝕚 j} (s-∀l x ic fd upC upD (↑tyʲ-𝕚 upj))
  (wfc-𝕚 x₁)
  (⊆∀-I-no ext upj₁)
  (~I ⊢e x₃)
  with refl ← ↑tyʲ-unique upj upj₁
  with () ← ⊆/c-find-∋= ext Z fd
complete-s {j = 𝕔 j} (s-∀l x ic fd upC upD (↑tyʲ-𝕔 upj))
  (wfc-𝕔 x₁)
  (⊆∀-C-no ext upj₁)
  (~C ⊢e x₃)
  with refl ← ↑tyʲ-unique upj upj₁
  with () ← ⊆/c-find-∋= ext Z fd

complete-s {j = 𝕚 j} (s-∀l-no-appear s ic fd upC upD (↑tyʲ-𝕚 upj)) (wfc-𝕚 x) (⊆∀-I ext upj₁) (~I ⊢e ~j) = ⊥-elim (ε-¬ε-false (find-ε-gen (⊆/c-find0 ext)) fd)
complete-s {j = 𝕚 j} (s-∀l-no-appear s ic fd upC upD (↑tyʲ-𝕚 upj)) (wfc-𝕚 x) (⊆∀-I-no ext upj₁) ~j'@(~I {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S^ r ← s-sregular s
  with refl ← ↑tyʲ-unique upj upj₁
  with weaken-j~ ← (~weaken^0 (~I ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕚 upj)
  with complete-s s (wfc-𝕚 (wf1-ex x)) ext weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₄ (case₂ cond'))) (s-∀l-n-n s₁ upΣ upe upC upD)
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹^S newΔ up1) s₁ =
  special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ (s-∀l-n-n s₁ upΣ upe upC upD)
complete-s {j = 𝕚 j} (s-svar-𝕚 x s) (wfc-𝕚 x₁) (⊆I-X regΓ cloA) ~j'@(~I ⊢e j~Σ)
  with complete-s s (wfc-𝕚 x₁) (s+-⊆/ s) ~j'
... | normal cond s₁ = normal (⊢c-¬ε' cloA) (s-svar-term x s₁)
... | special inA inΓ^ tail newΔ s₁ = ⊥-elim (complete-false₃ (∋:=-⊢r regΓ x) inA inΓ^)
complete-s {j = 𝕚 j} (s-svar-𝕚 x s) (wfc-𝕚 x₁) (⊆Inf-X extx iso) ~j'@(~I ⊢e ~j)
  with infs' ← (complete-infs (~I ⊢e ~j) (⊆-⊢r' (s+-polarity s) (⊆/x-⊆ extx)) iso)
  with ⊆/x-exsol' (⊆/x-⊆ extx) (∋:=to∋= x)
... | is-ex inΓ
  with ⟨ Δ′ , inst' ⟩ ← inst-∃-A (⊢r-𝕣 (infs-⊢r infs')) (wf1-⊆' (⊆/x-⊆ extx) x₁) (⊆-sregular (⊆/x-⊆ extx)) inΓ
  = special ε-var inΓ ett-var (inst-=⟹' inst' extx) (s-evar-infers infs' inst')
... | is-sol inΓ
  with refl ← ⊆/x-∋=-eq extx inΓ
  with complete-s s (wfc-𝕚 x₁) (s+-⊆/ s) ~j'
... | normal cond s₁ = normal (λ { ⟨ k' , ⟨ ε-var , inΓ' ⟩ ⟩ → ∋^-∋=-false inΓ' inΓ }) (s-svar-term x s₁)
... | special inA inΓ^ tail newΔ s₁ = ⊥-elim (⊢c-^∈-false (ε'-ε inA) inΓ^ (⊢r-⊢c (∋:=-⊢r (s-sregular s) x)))
complete-s {j = 𝕔 j} (s-arr₃ cloA grd s) (wfc-𝕔 x₁) (⊆C cloA₁ ext) (~C ⊢e ~j) with complete-s s (wf1-wfcj x₁) ext ~j
... | normal cond s₁ = normal (λ cond' → cond (case₁ cond')) (s-term-c cloA₁ (⊆-⊢c-≫ (⊆/c-⊆ ext) cloA₁ grd) ⊢e s₁)
... | special inA inΓ^ tail newΔ s₁ = special (ε-arr (⊢c-^∈-¬ε cloA₁ inΓ^) inA) inΓ^ (ett-arr tail) newΔ (s-term-c cloA₁ (⊆-⊢c-≫ (⊆/c-⊆ ext) cloA₁ grd) ⊢e s₁)
complete-s {j = 𝕔 j} (s-∀l-no-appear s ic fd upC upD (↑tyʲ-𝕔 upj)) (wfc-𝕔 x₁) (⊆∀-C ext upj₁) (~C ⊢e ~j) = ⊥-elim (ε-¬ε-false (find-ε-gen (⊆/c-find0 ext)) fd)
complete-s {j = 𝕔 j} (s-∀l-no-appear s ic fd upC upD (↑tyʲ-𝕔 upj)) (wfc-𝕔 x₁) (⊆∀-C-no ext upj₁) ~j'@(~C {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S^ r ← s-sregular s
  with refl ← ↑tyʲ-unique upj upj₁
  with weaken-j~ ← (~weaken^0 (~C ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕔 upj)
  with complete-s s (wfc-𝕔 (wf1-ex x₁)) ext weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₄ (case₂ cond'))) ((s-∀l-n-n s₁ upΣ upe upC upD))
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹^S newΔ up1) s₁
  = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ ((s-∀l-n-n s₁ upΣ upe upC upD))
complete-s {j = 𝕔 j} (s-svar-𝕔 x s) (wfc-𝕔 x₁) (⊆C-X regΓ cloA) ~j'@(~C ⊢e ~j)
  with complete-s s (wfc-𝕔 x₁) (s+-⊆/ s) ~j'
... | normal cond s₁ = normal (⊢c-¬ε' cloA) (s-svar-term x s₁)
... | special inA inΓ^ tail newΔ s₁ = ⊥-elim (complete-false₃ (∋:=-⊢r regΓ x) inA inΓ^)
complete-s {j = 𝕥₍ T ₎ j} (s-tapp s upj) (wfc-𝕥 wf) (⊆∀-T ext upj₁) (~T {Σ = Σ} ~j st)
  with refl ← ↑tyʲ-unique upj upj₁
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with reg-S= r regA ← s-sregular s
  with svar ext' regA₁ ← ⊆/c-⊆ ext
  with new~j ← ~weaken=0 ~j st upΣ upj regA₁
  with complete-s s (wf1-wfcj (wf1-sol wf)) ext new~j
... | normal cond s₁ = normal (λ cond' → cond (case₃ cond')) (s-tapp s₁ upΣ)
... | special inA (S= inΓ^) tail (=⟹=S newΔ up1 regB) s₁ = special (ε-∀ inA) inΓ^ (ett-∀-𝕥 tail up1) newΔ (s-tapp s₁ upΣ)
complete-s {j = 𝕥₍ T ₎ j} (s-svar-𝕥 x s) (wfc-𝕥 wf) (⊆T-X regΓ cloA) ~j'@(~T ~j st)
  with complete-s s (wfc-𝕥 wf) (s+-⊆/ s) ~j'
... | normal cond s₁ = normal (⊢c-¬ε' cloA) (s-svar-tapp x s₁)
... | special inA inΓ^ tail newΔ s₁ = ⊥-elim (complete-false₃ (∋:=-⊢r regΓ x) inA inΓ^)

complete-s (s-∀l-peek s ic pk upC upD upj) wf (⊆∀-I-no ext upj₁) ~j = ⊥-elim (ε-¬ε-false (peek-ε-gen pk) (⊆/c-no-appear ext Z Z))
complete-s  {j = 𝕔 j} (s-∀l-peek {B = B} s case-𝕔 pk upC upD (↑tyʲ-𝕔 upj)) (wfc-𝕔 x) (⊆∀-C ext upj₁) ~j'@(~C {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with reg-S= r regA ← s-sregular s
  with refl ← ↑tyʲ-unique upj upj₁
  with weaken-j~ ← (~weaken^0 (~C ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕔 upj)
  with com-pk ← (peek-a-~pk~ (peek→peek-a s pk (Z upB)) weaken-j~)
  with complete-s s (wfc-𝕔 (wf1-sol x)) (⊆/c-irrev-^=0' ext regA) weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₄ (case₂ cond'))) (s-∀l-y com-pk upB (s-unsol-sol0 s₁) upΣ upe upC upD)
... | special {k = #0} inA Z tail (=⟹=0 up regA₁ env) s₁
  with refl ← pk-tail-eq com-pk tail inA (s-id' s₁)
  = normal (case₅ inA) (s-∀l-y com-pk up (s-unsol-sol0 s₁) upΣ upe upC upD)
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹=S newΔ up1 regB) s₁
  = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ (s-∀l-y com-pk upB (s-unsol-sol0 s₁) upΣ upe upC upD)
complete-s (s-∀l-peek s ic pk upC upD upj) wf (⊆∀-C-no ext upj₁) ~j = ⊥-elim (ε-¬ε-false (peek-ε-gen pk) (⊆/c-no-appear ext Z Z))
complete-s {j = 𝕚 j} (s-∀l s ic fd upC upD (↑tyʲ-𝕚 upj)) (wfc-𝕚 x) (⊆∀-I-new ext upj₁) ~j'@(~I {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S= r regA ← s-sregular s
  with refl ← ↑tyʲ-unique upj upj₁
  with weaken-j~ ← (~weaken^0 (~I ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕚 upj)
  with complete-s s (wfc-𝕚 (wf1-sol x)) (⊆/c-irrev-^=0 (⊆/c-irrev-^0 ext fd) fd regA) weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₄ (case₂ cond'))) (s-∀l-n-y s₁ upΣ upe upC upD)
... | special {k = #0} inA Z tail (=⟹=0 up regA₁ env) s₁ = normal (case₅ inA) ((s-∀l-n-y s₁ upΣ upe upC upD))
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹=S newΔ up1 regB) s₁ = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ
  (s-∀l-n-y s₁ upΣ upe upC upD)
complete-s (s-∀l-peek {B = B} s case-𝕚 pk upC upD (↑tyʲ-𝕚 upj)) (wfc-𝕚 x) (⊆∀-I-new ext upj₁) ~j'@(~I {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S= r regA ← s-sregular s
  with svar ext' _ ← ⊆/c-⊆ ext
  with regA' ← ⊆-⊢r' regA ext'
  with refl ← ↑tyʲ-unique upj upj₁
  with weaken-j~ ← (~weaken=0 (~I ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕚 upj) regA'
  with com-pk ← (peek-a-~pk~ (peek→peek-a s pk (Z upB)) weaken-j~)
  with complete-s s (wfc-𝕚 (wf1-sol x)) (⊆/c-irrev-==0 ext regA') weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₃ cond')) (s-∀l-y com-pk upB s₁ upΣ upe upC upD)
... | special {k = #0} inA () tail newΔ s₁
... | special {k = #S k} inA (S= inΓ^) tail (=⟹=S newΔ up1 regB) s₁ = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ ((s-∀l-y com-pk upB s₁ upΣ upe upC upD))
complete-s {j = 𝕚 j} (s-∀l-no-appear s ic fd upC upD (↑tyʲ-𝕚 upj)) (wfc-𝕚 x) (⊆∀-I-new ext upj₁) ~j'@(~I {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S^ r ← s-sregular s
  with refl ← ↑tyʲ-unique upj upj₁
  with weaken-j~ ← (~weaken^0 (~I ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕚 upj)
  with complete-s s (wfc-𝕚 (wf1-ex x)) (⊆/c-irrev-^^0 ext fd) weaken-j~
... | normal cond s₁ = normal ((λ cond' → cond (case₄ (case₂ cond')))) (s-∀l-n-n s₁ upΣ upe upC upD)
... | special {k = #0} inA Z tail () s₁
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹^S newΔ up1) s₁
  = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ (s-∀l-n-n s₁ upΣ upe upC upD)
-- no worry, logic below duplicated
complete-s {j = 𝕔 j} (s-∀l s ic fd upC upD (↑tyʲ-𝕔 upj)) (wfc-𝕔 x) (⊆∀-C-new ext upj₁) ~j'@(~C {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S= r regA ← s-sregular s
  with refl ← ↑tyʲ-unique upj upj₁
  with weaken-j~ ← (~weaken^0 (~C ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕔 upj)
  with complete-s s (wfc-𝕔 (wf1-sol x)) (⊆/c-irrev-^=0 (⊆/c-irrev-^0 ext fd) fd regA) weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₄ (case₂ cond'))) (s-∀l-n-y s₁ upΣ upe upC upD)
... | special {k = #0} inA Z tail (=⟹=0 up regA₁ env) s₁ = normal (case₅ inA) ((s-∀l-n-y s₁ upΣ upe upC upD))
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹=S newΔ up1 regB) s₁ = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ
  (s-∀l-n-y s₁ upΣ upe upC upD)
complete-s (s-∀l-peek {B = B} s case-𝕔 pk upC upD (↑tyʲ-𝕔 upj)) (wfc-𝕔 x) (⊆∀-C-new ext upj₁) ~j'@(~C {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S= r regA ← s-sregular s
  with svar ext' _ ← ⊆/c-⊆ ext
  with regA' ← ⊆-⊢r' regA ext'
  with refl ← ↑tyʲ-unique upj upj₁
  with weaken-j~ ← (~weaken=0 (~C ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕔 upj) regA'
  with com-pk ← (peek-a-~pk~ (peek→peek-a s pk (Z upB)) weaken-j~)
  with complete-s s (wfc-𝕔 (wf1-sol x)) (⊆/c-irrev-==0 ext regA') weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₃ cond')) (s-∀l-y com-pk upB s₁ upΣ upe upC upD)
... | special {k = #0} inA () tail newΔ s₁
... | special {k = #S k} inA (S= inΓ^) tail (=⟹=S newΔ up1 regB) s₁ = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ ((s-∀l-y com-pk upB s₁ upΣ upe upC upD))
complete-s {j = 𝕔 j} (s-∀l-no-appear s ic fd upC upD (↑tyʲ-𝕔 upj)) (wfc-𝕔 x) (⊆∀-C-new ext upj₁) ~j'@(~C {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S^ r ← s-sregular s
  with refl ← ↑tyʲ-unique upj upj₁
  with weaken-j~ ← (~weaken^0 (~C ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕔 upj)
  with complete-s s (wfc-𝕔 (wf1-ex x)) (⊆/c-irrev-^^0 ext fd) weaken-j~
... | normal cond s₁ = normal ((λ cond' → cond (case₄ (case₂ cond')))) (s-∀l-n-n s₁ upΣ upe upC upD)
... | special {k = #0} inA Z tail () s₁
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹^S newΔ up1) s₁
  = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ (s-∀l-n-n s₁ upΣ upe upC upD)

----------------------------------------------------------------------
--+                          Corollaries                           +--
----------------------------------------------------------------------

wfc-⋈ : WFC (Γ ⋈) j
wfc-⋈ {j = Z} = wfc-z wf1-base
wfc-⋈ {j = ∞} = wfc-∞ (wf2-base wf1-base)
wfc-⋈ {j = 𝕚 j} = wfc-𝕚 wf1-base
wfc-⋈ {j = 𝕔 j} = wfc-𝕔 wf1-base
wfc-⋈ {j = 𝕥₍ x ₎ j} = wfc-𝕥 wf1-base


complete-s0 : Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → Γ ⊢ ⟨ j , B ⟩ ~t Σ
            → Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ B
complete-s0 s j~Σ with complete-s s wfc-⋈ (s+-⊆/ s) (~t-~s j~Σ)
... | normal cond s₁ = s₁
