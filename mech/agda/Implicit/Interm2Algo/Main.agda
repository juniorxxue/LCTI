module Implicit.Interm2Algo.Main where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm.All

open import Implicit.Interm2Algo.Counter2Context
open import Implicit.Interm2Algo.ExtIrrev
open import Implicit.Interm2Algo.EnvDiff
open import Implicit.Interm2Algo.OpenClose
open import Implicit.Interm2Algo.Find
open import Implicit.Interm2Algo.AuxLemmas

s-empty-inv : Δ ⊢ `■ # A ⌞ ≤⁺ ⌝ B
            → Δ ≫ A ⇘ B
s-empty-inv (s-refl regΔ cloA grd) = grd
s-empty-inv (s-svar-l x s)
  with refl ← ⊢r-≫-eq' (∋:=-⊢r (s-sregular s) x) (s-empty-inv s) = grd-var= x

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

data WFC : Env n m → Mask → Set where
  wfc-z : WF1 Γ
        → WFC Γ `■
  wfc-∞ : WF2 Γ
        → WFC Γ `□
  wfc-s : WF1 Γ
        → WFC Γ (i · j)

wf1-wfcj : WF1 Δ
         → WFC Δ j
wf1-wfcj {j = ` □} wf1 = wfc-∞ (wf2-base wf1)
wf1-wfcj {j = ` ■} wf1 = wfc-z wf1
wf1-wfcj {j = x · j} wf1 = wfc-s wf1

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


complete-s :  Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → WFC Δ j
            → Γ ⊆ Δ w/t A w/c j
            → Γ ⊢ ⟨ j , B ⟩ ~s Σ
            → Complete A j Σ Γ Δ B
complete-s (s-refl regΔ cloA grd) wfc (⊆Z regΓ) ~Z = normal (⊢c-¬ε' cloA) (s-empty regΔ cloA grd)
complete-s {j = ` □} s wfc (⊆∞ ext) ~∞ = ss-complete (complete-ss+ s ext)
complete-s (s-arr₂ s s₁) (wfc-s x) (⊆I ext ext₁) (~I ⊢e j~Σ) with ⊆/-openclose ext
complete-s (s-arr₂ {A = A} s s₁) (wfc-s x) (⊆I ext ext₁) (~I ⊢e ~j) | inj₁ opnA
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
complete-s (s-arr₂ {A = A} s s₁) (wfc-s x) (⊆I ext ext₁) (~I ⊢e ~j) | inj₂ cloA
  with refl ← ⊆/-⊢c-eq ext cloA
  with grd ← ⊆-⊢c-≫ (⊆/c-⊆ ext₁) cloA (s--≫ s)
  with complete-s s₁ (wf1-wfcj x) ext₁ ~j
... | normal cond s₂ = normal (λ cond' → cond (case₁ cond')) (s-term-c cloA grd (subsumption0 ⊢e) s₂)
... | special {k = k} inA inΓ^ tail newΔ s₂ with ε-dec {k = k} {A = A}
... | inj₁ inA' = ⊥-elim (⊢c-^∈-false inA' inΓ^ cloA)
... | inj₂ ¬inA = special (ε-arr ¬inA inA) inΓ^ (ett-arr tail) newΔ (s-term-c cloA grd (subsumption0 ⊢e) s₂)
complete-s (s-arr₃ cloA grd s) (wfc-s x₁) (⊆C cloA₁ ext) (~C ⊢e ~j) with complete-s s (wf1-wfcj x₁) ext ~j
... | normal cond s₁ = normal (λ cond' → cond (case₁ cond')) (s-term-c cloA₁ (⊆-⊢c-≫ (⊆/c-⊆ ext) cloA₁ grd) ⊢e s₁)
... | special inA inΓ^ tail newΔ s₁ = special (ε-arr (⊢c-^∈-¬ε cloA₁ inΓ^) inA) inΓ^ (ett-arr tail) newΔ (s-term-c cloA₁ (⊆-⊢c-≫ (⊆/c-⊆ ext) cloA₁ grd) ⊢e s₁)
complete-s (s-∀l s fd upC upD) (wfc-s x) (⊆∀ ext) ~j'@(~I {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S= r regA ← s-sregular s
  with weaken-j~ ← (~weaken^0 (~I ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ))
  with complete-s s (wfc-s (wf1-sol x)) (⊆/c-irrev-^=0 ext fd regA) weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₄ (case₂ cond'))) (s-∀l s₁ upΣ upe upC upD)
... | special {k = #0} inA Z tail (=⟹=0 up regA₁ env) s₁ = normal (case₅ inA) (s-∀l s₁ upΣ upe upC upD)
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹=S newΔ up1 regB) s₁ = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ (s-∀l s₁ upΣ upe upC upD)
complete-s (s-∀l s fd upC upD) (wfc-s x₁) (⊆∀ ext) ~j'@(~C {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S= r regA ← s-sregular s
  with weaken-j~ ← (~weaken^0 (~C ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ))
  with complete-s s (wfc-s (wf1-sol x₁)) (⊆/c-irrev-^=0 ext fd regA) weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₄ (case₂ cond'))) (s-∀l s₁ upΣ upe upC upD)
... | special {k = #0} inA Z tail (=⟹=0 up regA₁ env) s₁ = normal (case₅ inA) (s-∀l s₁ upΣ upe upC upD)
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹=S newΔ up1 regB) s₁ = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ (s-∀l s₁ upΣ upe upC upD)
complete-s (s-∀l s fd upC upD) (wfc-s x) (⊆∀-no ext) j~Σ
  with () ← ⊆/c-find-∋= ext Z fd
complete-s (s-∀l-no-appear s fd upC upD) (wfc-s x) (⊆∀ ext) j~Σ = ⊥-elim (ε-¬ε-false (find-ε-gen (⊆/c-find0 ext)) fd)
complete-s (s-∀l-no-appear s fd upC upD) (wfc-s x) (⊆∀-no ext) ~j'@(~I {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S^ r ← s-sregular s
  with weaken-j~ ← (~weaken^0 (~I ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ))
  with complete-s s (wfc-s (wf1-ex x)) ext weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₄ (case₂ cond'))) (s-∀l-no s₁ upΣ upe upC upD)
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹^S newΔ up1) s₁ = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ (s-∀l-no s₁ upΣ upe upC upD)
complete-s (s-∀l-no-appear s fd upC upD) (wfc-s x) (⊆∀-no ext) ~j'@(~C {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S^ r ← s-sregular s
  with weaken-j~ ← (~weaken^0 (~C ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ))
  with complete-s s (wfc-s (wf1-ex x)) ext weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₄ (case₂ cond'))) (s-∀l-no s₁ upΣ upe upC upD)
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹^S newΔ up1) s₁ = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ (s-∀l-no s₁ upΣ upe upC upD)
complete-s (s-svar-l inΔ s) (wfc-z x) (⊆Z regΓ) ~Z
  with refl ← ⊢r-≫-eq' (∋:=-⊢r (s-sregular s) inΔ) (s-empty-inv s)
  = normal (⊢c-¬ε' (⊢c-var-= (∋:=to∋= inΔ))) (s-empty regΓ (⊢c-var-= (∋:=to∋= inΔ)) (grd-var= inΔ))
complete-s (s-svar-l x s) (wfc-s x₁) (⊆X regΓ cloA) ~j'@(~I ⊢e j~Σ)
  with complete-s s (wfc-s x₁) (s+-⊆/ s) ~j'
... | normal cond s₁ = normal (⊢c-¬ε' cloA) (s-svar-term x s₁)
... | special inA inΓ^ tail newΔ s₁ = ⊥-elim (complete-false₃ (∋:=-⊢r regΓ x) inA inΓ^)
complete-s (s-svar-l x s) (wfc-s x₁) (⊆X regΓ cloA) ~j'@(~C ⊢e ~j)
  with complete-s s (wfc-s x₁) (s+-⊆/ s) ~j'
... | normal cond s₁ = normal (⊢c-¬ε' cloA) (s-svar-term x s₁)
... | special inA inΓ^ tail newΔ s₁ = ⊥-elim (complete-false₃ (∋:=-⊢r regΓ x) inA inΓ^)
complete-s (s-svar-l inΔ s) (wfc-s x₁) (⊆Inf-X extx iso) ~j'@(~I ⊢e ~j)
  with infs' ← (complete-infs (~I ⊢e ~j) (⊆-⊢r' (s+-polarity s) (⊆/x-⊆ extx)) iso)
  with ⊆/x-exsol' (⊆/x-⊆ extx) (∋:=to∋= inΔ)
... | is-ex inΓ
  with ⟨ Δ′ , inst' ⟩ ← inst-∃-A (⊢r-𝕣 (infs-⊢r infs')) (wf1-⊆' (⊆/x-⊆ extx) x₁) (⊆-sregular (⊆/x-⊆ extx)) inΓ
  = special ε-var inΓ ett-var (inst-=⟹' inst' extx) (s-evar-infers infs' inst')
... | is-sol inΓ
  with refl ← ⊆/x-∋=-eq extx inΓ
  with complete-s s (wfc-s x₁) (s+-⊆/ s) ~j'
... | normal cond s₁ = normal (λ { ⟨ k' , ⟨ ε-var , inΓ' ⟩ ⟩ → ∋^-∋=-false inΓ' inΓ }) (s-svar-term inΔ s₁)
... | special inA inΓ^ tail newΔ s₁ = ⊥-elim (⊢c-^∈-false (ε'-ε inA) inΓ^ (⊢r-⊢c (∋:=-⊢r (s-sregular s) inΔ)))

----------------------------------------------------------------------
--+                          Corollaries                           +--
----------------------------------------------------------------------

wfc-⋈ : WFC (Γ ⋈) j
wfc-⋈ {j = ` □} = wfc-∞ (wf2-base wf1-base)
wfc-⋈ {j = ` ■} = wfc-z wf1-base
wfc-⋈ {j = x · j} = wfc-s wf1-base


complete-s0 : Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → Γ ⊢ ⟨ j , B ⟩ ~t Σ
            → Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ B
complete-s0 s j~Σ with complete-s s wfc-⋈ (s+-⊆/ s) (~t-~s j~Σ)
... | normal cond s₁ = s₁
