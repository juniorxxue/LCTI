module Implicit.Interm2Algo.Main where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.Regularity
open import Implicit.Interm.Properties.Polarity
open import Implicit.Interm.Ground
open import Implicit.Interm2Algo.Counter2Context
open import Implicit.Interm2Algo.ExtIrrev
open import Implicit.Interm2Algo.EnvDiff
open import Implicit.Interm2Algo.OpenClose
open import Implicit.Interm2Algo.Find
open import Implicit.Interm2Algo.AuxLemmas

complete-s :  Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → Γ ⊆ Δ w/t A w/c j
            → Γ ⊢ ⟨ j , B ⟩ ~s Σ
            → Complete A j Σ Γ Δ B

complete-s {j = Z} (s-refl regΔ cloA grd) (⊆Z regΓ) ~Z = normal (⊢c-¬ε' cloA) (s-empty regΔ cloA grd)
complete-s {j = ∞} s (⊆∞ ext) ~∞ = ss-complete (complete-ss+ s ext)
complete-s {j = 𝕚 j} (s-arr₂ s s₁) (⊆I ext ext₁) (~I ⊢e ~j) with ⊆/-openclose ext
-- A is open
complete-s {j = 𝕚 j} (s-arr₂ {A = A} s s₁) (⊆I ext ext₁) (~I ⊢e ~j) | inj₁ opnA
  with ⟨ Ψ , diff ⟩ ← ⅆ-total (⊆/-⊆ ext) (⊆/c-⊆ ext₁)
  with ih ← complete-ss- {Γ = Ψ} s (ⅆ-⊆/ diff ext)
  with ih' ← s--subirrev-final ih diff (⊆/-⊢c ext)
  with complete-s s₁ ext₁ (~irrev ~j (⊆/-⊆ ext))
... | normal cond s₂ = normal
  (λ where ⟨ k , ⟨ ε-arr x' inB , inΓ ⟩ ⟩ → cond ⟨ k , ⟨ inB , ⊆/-^in-^out (ss--⊆/ ih') x' inΓ ⟩ ⟩)
  (s-term-o opnA ⊢e ih' s₂)
... | special {k = k} inA inΓ^ tail newΔ s₂ with ε-dec {k = k} {A = A}
... | inj₁ inA' = ⊥-elim (complete-false₂ ext inA' inΓ^)
... | inj₂ ¬inA = special (ε-arr ¬inA inA) (⊆-^out-^in inΓ^ (ss-⊆ ih')) (ett-arr tail) newΔ (s-term-o opnA ⊢e ih' s₂)
-- A is close
complete-s {j = 𝕚 j} (s-arr₂ {A = A} s s₁) (⊆I ext ext₁) (~I ⊢e ~j) | inj₂ cloA
  with refl ← ⊆/-⊢c-eq ext cloA
  with grd ← ⊆-⊢c-≫ (⊆/c-⊆ ext₁) cloA (s--≫ s)
  with complete-s s₁ ext₁ ~j
... | normal cond s₂ = normal (λ cond' → cond (case₁ cond')) (s-term-c cloA grd (subsumption0 ⊢e) s₂)
... | special {k = k} inA inΓ^ tail newΔ s₂ with ε-dec {k = k} {A = A}
... | inj₁ inA' = ⊥-elim (⊢c-^∈-false inA' inΓ^ cloA)
... | inj₂ ¬inA = special (ε-arr ¬inA inA) inΓ^ (ett-arr tail) newΔ (s-term-c cloA grd (subsumption0 ⊢e) s₂)
complete-s {j = 𝕚 j} (s-∀l s ic fd upC upD (↑tyʲ-𝕚 upj)) (⊆∀-I ext upj₁) ~j'@(~I {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S= r regA ← s-sregular s
  with refl ← ↑tyʲ-unique upj upj₁
  with weaken-j~ ← (~weaken^0 (~I ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕚 upj)
  with complete-s s (⊆/c-irrev-^=0 ext fd regA) weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₄ (case₂ cond'))) (s-∀l s₁ upΣ upe upC upD)
... | special {k = #0} inA Z tail (=⟹=0 up regA₁ env) s₁ = normal (case₅ inA) (s-∀l s₁ upΣ upe upC upD)
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹=S newΔ up1 regB) s₁ = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ (s-∀l s₁ upΣ upe upC upD)
complete-s {j = 𝕚 j} (s-∀l s ic fd upC upD (↑tyʲ-𝕚 upj)) (⊆∀-I-no ext upj₁) (~I ⊢e ~j)
  with refl ← ↑tyʲ-unique upj upj₁
  with () ← ⊆/c-find-∋= ext Z fd
complete-s {j = 𝕚 j} (s-∀l-no-appear s ic fd upC upD (↑tyʲ-𝕚 upj)) (⊆∀-I ext upj₁) (~I ⊢e ~j) = ⊥-elim (ε-¬ε-false (find-ε-gen (⊆/c-find0 ext)) fd)
complete-s {j = 𝕚 j} (s-∀l-no-appear s ic fd upC upD (↑tyʲ-𝕚 upj)) (⊆∀-I-no ext upj₁) ~j'@(~I {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S^ r ← s-sregular s
  with refl ← ↑tyʲ-unique upj upj₁
  with weaken-j~ ← (~weaken^0 (~I ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕚 upj)
  with complete-s s ext weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₄ (case₂ cond'))) (s-∀l-no s₁ upΣ upe upC upD)
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹^S newΔ up1) s₁ = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ (s-∀l-no s₁ upΣ upe upC upD)
complete-s {j = 𝕚 j} (s-svar-𝕚 x s) (⊆I-X regΓ cloA) ~j'@(~I ⊢e ~j)
  with complete-s s (s+-⊆/ s) ~j'
... | normal cond s₁ = normal (⊢c-¬ε' cloA) (s-svar-term x s₁)
... | special inA inΓ^ tail newΔ s₁ = ⊥-elim (complete-false₃ (∋:=-⊢r regΓ x) inA inΓ^)
complete-s {j = 𝕚 j} (s-svar-𝕚 x s) (⊆Inf-X extx iso) ~j'@(~I ⊢e ~j)
  with infs' ← (complete-infs (~I ⊢e ~j) (⊆-⊢r' (s+-polarity s) (⊆/x-⊆ extx)) iso)
  with ⊆/x-exsol' (⊆/x-⊆ extx) (∋:=to∋= x)
... | is-ex inΓ = special ε-var inΓ ett-var {!!} (s-evar-infers infs' {!!})
... | is-sol inΓ
  with refl ← ⊆/x-∋=-eq extx inΓ
  with complete-s s (s+-⊆/ s) ~j'
... | normal cond s₁ = normal (λ { ⟨ k' , ⟨ ε-var , inΓ' ⟩ ⟩ → ∋^-∋=-false inΓ' inΓ }) (s-svar-term x s₁)
... | special inA inΓ^ tail newΔ s₁ = ⊥-elim (⊢c-^∈-false (ε'-ε inA) inΓ^ (⊢r-⊢c (∋:=-⊢r (s-sregular s) x)))
complete-s {j = 𝕔 j} (s-arr₃ cloA grd s) (⊆C cloA₁ ext) (~C ⊢e ~j) with complete-s s ext ~j
... | normal cond s₁ = normal (λ cond' → cond (case₁ cond')) (s-term-c cloA₁ (⊆-⊢c-≫ (⊆/c-⊆ ext) cloA₁ grd) ⊢e s₁)
... | special inA inΓ^ tail newΔ s₁
  = special (ε-arr (⊢c-^∈-¬ε cloA₁ inΓ^) inA) inΓ^ (ett-arr tail) newΔ (s-term-c cloA₁ (⊆-⊢c-≫ (⊆/c-⊆ ext) cloA₁ grd) ⊢e s₁)
-- copy the logic from forall-L-i
complete-s {j = 𝕔 j} (s-∀l s ic fd upC upD (↑tyʲ-𝕔 upj)) (⊆∀-C ext upj₁) ~j'@(~C {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S= r regA ← s-sregular s
  with refl ← ↑tyʲ-unique upj upj₁
  with weaken-j~ ← (~weaken^0 (~C ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕔 upj)
  with complete-s s (⊆/c-irrev-^=0 ext fd regA) weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₄ (case₂ cond'))) (s-∀l s₁ upΣ upe upC upD)
... | special {k = #0} inA Z tail (=⟹=0 up regA₁ env) s₁ = normal (case₅ inA) (s-∀l s₁ upΣ upe upC upD)
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹=S newΔ up1 regB) s₁ = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ (s-∀l s₁ upΣ upe upC upD)
complete-s {j = 𝕔 j} (s-∀l s ic fd upC upD (↑tyʲ-𝕔 upj)) (⊆∀-C-no ext upj₁) (~C ⊢e ~j)
  with refl ← ↑tyʲ-unique upj upj₁
  with () ← ⊆/c-find-∋= ext Z fd
complete-s {j = 𝕔 j} (s-∀l-no-appear s ic fd upC upD (↑tyʲ-𝕔 upj)) (⊆∀-C ext upj₁) (~C ⊢e ~j) = ⊥-elim (ε-¬ε-false (find-ε-gen (⊆/c-find0 ext)) fd)
complete-s {j = 𝕔 j} (s-∀l-no-appear s ic fd upC upD (↑tyʲ-𝕔 upj)) (⊆∀-C-no ext upj₁) ~j'@(~C {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with reg-S^ r ← s-sregular s
  with refl ← ↑tyʲ-unique upj upj₁
  with weaken-j~ ← (~weaken^0 (~C ⊢e ~j) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕔 upj)
  with complete-s s ext weaken-j~
... | normal cond s₁ = normal (λ cond' → cond (case₄ (case₂ cond'))) (s-∀l-no s₁ upΣ upe upC upD)
... | special {k = #S k} inA (S^ inΓ^) tail (=⟹^S newΔ up1) s₁ = special (ε-∀ inA) inΓ^ (ett-∀-𝕚 tail upC upD up1) newΔ (s-∀l-no s₁ upΣ upe upC upD)
complete-s {j = 𝕔 j} (s-svar-𝕔 x s) (⊆C-X regΓ cloA) ~j'@(~C ⊢e ~j)
  with complete-s s (s+-⊆/ s) ~j'
... | normal cond s₁ = normal (⊢c-¬ε' cloA) (s-svar-term x s₁)
... | special inA inΓ^ tail newΔ s₁ = ⊥-elim (complete-false₃ (∋:=-⊢r regΓ x) inA inΓ^)
complete-s {j = 𝕥₍ T ₎ j} (s-tapp s upj) (⊆∀-T ext upj₁) (~T {Σ = Σ} ~j st)
  with refl ← ↑tyʲ-unique upj upj₁
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with reg-S= r regA ← s-sregular s
  with svar ext' regA₁ ← ⊆/c-⊆ ext
  with new~j ← ~weaken=0 ~j (st-↑ty (⊢r-¬ε (s+-polarity s) Z) st) upΣ upj regA₁
  with complete-s s ext new~j
... | normal cond s₁ = normal (λ cond' → cond (case₃ cond')) (s-tapp s₁ upΣ)
... | special inA (S= inΓ^) tail (=⟹=S newΔ up1 regB) s₁ = special (ε-∀ inA) inΓ^ (ett-∀-𝕥 tail up1) newΔ (s-tapp s₁ upΣ)
complete-s {j = 𝕥₍ T ₎ j} (s-svar-𝕥 x s) (⊆T-X regΓ cloA) ~j'@(~T ~j st)
  with complete-s s (s+-⊆/ s) ~j'
... | normal cond s₁ = normal (⊢c-¬ε' cloA) (s-svar-tapp x s₁)
... | special inA inΓ^ tail newΔ s₁ = ⊥-elim (complete-false₃ (∋:=-⊢r regΓ x) inA inΓ^)
