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

data Complete (A : Type m) (j : Counter m) (Σ : Context n m) (Γ : Env n m) (Δ : Env n m) (B : Type m) : Set where
  normal : ¬ (∃[ k ](k ε' A) × Γ ∋^ k)
               → Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
               → Complete A j Σ Γ Δ B

  special : ∀ {k Δ'}
               → k ε' A
               → Γ ∋^ k
               → A ≤ B ⟹ T
               → [ T / k ] Δ =⟹ Δ'
               → Γ ⊢ A ≤⁺ Σ ⊣ Δ' ↪ B
               → Complete A j Σ Γ Δ B


complete-s :  Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → Γ ⊆ Δ w/t A w/c j
            → Γ ⊢ ⟨ j , B ⟩ ~s Σ
            → Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B

complete-s {j = Z} (s-refl regΔ cloA grd) (⊆Z regΓ) ~Z = s-empty regΔ cloA grd
complete-s {j = ∞} s (⊆∞ x) ~∞ = s-type (complete-ss+ s x)
complete-s {j = 𝕚 j} {Γ = Γ} (s-arr₂ {A = A} s s₁) (⊆I ext ext₁) (~I ⊢e j~Σ) with ⊆/-openclose ext
... | inj₁ opnA
  with ⟨ Ψ , diff ⟩ ← ⅆ-total (⊆/-⊆ ext) (⊆/c-⊆ ext₁)
  with ih ← complete-ss- {Γ = Ψ} s (ⅆ-⊆/ diff ext)
  = s-term-o opnA ⊢e (s--subirrev-final ih diff (⊆/-⊢c ext)) (complete-s s₁ ext₁ (~irrev j~Σ (⊆/-⊆ ext)))
... | inj₂ cloA
  with refl ← ⊆/-⊢c-eq ext cloA = s-term-c cloA (⊆-⊢c-≫ (⊆/c-⊆ ext₁) cloA (s--≫ s)) (subsumption0 ⊢e) (complete-s s₁ ext₁ j~Σ)
complete-s {j = 𝕔 j} (s-arr₃ cloA grd s) (⊆C cloA' ext) (~C ⊢e j~Σ) = s-term-c cloA' (⊆-⊢c-≫ (⊆/c-⊆ ext) cloA' grd) ⊢e (complete-s s ext j~Σ)
complete-s (s-∀l s ic fd upC upD (↑tyʲ-𝕚 upj)) (⊆∀-I ext upj') j~'@(~I {Σ = Σ} {e = e} ⊢e j~) with ↑tyᶜ0-total Σ | ↑tyᵉ0-total e | s-sregular s
... | ⟨ Σ' , upΣ ⟩ | ⟨ e' , upe ⟩ | reg-S= r regA
  with refl ← ↑tyʲ-unique upj upj' = let weaken-j~ = (~weaken^0 (~I ⊢e j~) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕚 upj)
                                     in s-∀l (complete-s s (⊆/c-irrev-^=0 ext fd regA) weaken-j~) upΣ upe upC upD
complete-s (s-∀l s ic fd upC upD (↑tyʲ-𝕔 upj)) (⊆∀-C ext upj') j~'@(~C {Σ = Σ} {e = e} ⊢e j~) with ↑tyᶜ0-total Σ | ↑tyᵉ0-total e | s-sregular s
... | ⟨ Σ' , upΣ ⟩ | ⟨ e' , upe ⟩ | reg-S= r regA
  with refl ← ↑tyʲ-unique upj upj' = let weaken-j~ = (~weaken^0 (~C ⊢e j~) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕔 upj)
                                     in s-∀l (complete-s s (⊆/c-irrev-^=0 ext fd regA) weaken-j~) upΣ upe upC upD
complete-s (s-tapp s upj) (⊆∀-T ext upj₁) (~T {Σ = Σ} ~j st)
  with refl ← ↑tyʲ-unique upj upj₁
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with reg-S= r regA ← s-sregular s
  with svar ext' regA₁ ← ⊆/c-⊆ ext = s-tapp (complete-s s ext (~weaken=0 ~j (st-↑ty (⊢r-¬ε (s+-polarity s) Z) st) upΣ upj regA₁)) upΣ
complete-s (s-svar-𝕚 inΓ s) (⊆I-X regΓ cloA) (~I ⊢e ~j) = s-svar-term inΓ (complete-s s (s+-⊆/ s) (~I ⊢e ~j))
complete-s (s-svar-𝕔 inΓ s) (⊆C-X regΓ cloA) (~C ⊢e ~j) = s-svar-term inΓ (complete-s s (s+-⊆/ s) (~C ⊢e ~j))
complete-s (s-svar-𝕥 inΓ s) (⊆T-X regΓ cloA) (~T ~j st) = s-svar-tapp inΓ (complete-s s (s+-⊆/ s) (~T ~j st))
complete-s (s-∀l s ic fd upC upD (↑tyʲ-𝕚 upj)) (⊆∀-I-no ext upj₁) (~I ⊢e j~)
  with refl ← ↑tyʲ-unique upj upj₁
  with () ← ⊆/c-find-∋= ext Z fd
complete-s (s-∀l s ic fd upC upD (↑tyʲ-𝕔 upj)) (⊆∀-C-no ext upj₁) (~C ⊢e j~)
  with refl ← ↑tyʲ-unique upj upj₁
  with () ← ⊆/c-find-∋= ext Z fd
complete-s (s-∀l-no-appear s case-𝕚 fd upC upD (↑tyʲ-𝕚 upj)) (⊆∀-I ext upj₁) (~I ⊢e j~) = ⊥-elim (ε-¬ε-false (find-ε-gen (⊆/c-find0 ext)) fd)
complete-s (s-∀l-no-appear s case-𝕔 fd upC upD (↑tyʲ-𝕔 upj)) (⊆∀-C ext upj₁) (~C ⊢e j~) = ⊥-elim (ε-¬ε-false (find-ε-gen (⊆/c-find0 ext)) fd)
complete-s (s-∀l-no-appear s case-𝕚 fd upC upD (↑tyʲ-𝕚 upj)) (⊆∀-I-no ext upj₁) j~'@(~I {Σ = Σ} {e = e} ⊢e j~) with ↑tyᶜ0-total Σ | ↑tyᵉ0-total e
... | ⟨ Σ' , upΣ ⟩ | ⟨ e' , upe ⟩
  with refl ← ↑tyʲ-unique upj upj₁
  = let weaken-j~ = (~weaken^0 (~I ⊢e j~) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕚 upj)
    in s-∀l-no (complete-s s ext weaken-j~) upΣ upe upC upD
complete-s (s-∀l-no-appear s case-𝕔 fd upC upD (↑tyʲ-𝕔 upj)) (⊆∀-C-no ext upj₁) j~'@(~C {Σ = Σ} {e = e} ⊢e j~) with ↑tyᶜ0-total Σ | ↑tyᵉ0-total e
... | ⟨ Σ' , upΣ ⟩ | ⟨ e' , upe ⟩
  with refl ← ↑tyʲ-unique upj upj₁
  = let weaken-j~ = (~weaken^0 (~C ⊢e j~) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ)) (↑tyʲ-𝕔 upj)
    in s-∀l-no (complete-s s ext weaken-j~) upΣ upe upC upD
complete-s (s-svar-𝕚 inΓ s) (⊆Inf-X extx iso) (~I ⊢e j~) = {!!}
