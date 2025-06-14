module Implicit.Interm2Algo.AuxLemmas where

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

s+-⊆/ : Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
      → Δ ⊆ Δ w/t A w/c j

s--⊆/ : Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ B
      → Δ ⊆ Δ w/t B
s--⊆/ (s-int regΔ) = ext-int regΔ
s--⊆/ (s-var-∙ regΔ inΔ) = ext-var (reg-⊆/x∙ regΔ inΔ)
s--⊆/ (s-arr₁ s s₁) with s+-⊆/ s
... | ⊆∞ ext = ext-arr ext (s--⊆/ s₁)
s--⊆/ (s-∀ s) = ext-∀ (s--⊆/ s)
s--⊆/ (s-svar-r x inΔ) = ext-var (⊆/x-refl x (⊢c-var-= (∋:=to∋= inΔ)))

s+-⊆/ (s-refl regΔ cloA grd) = (⊆Z regΔ)
s+-⊆/ (s-int regΔ) = ⊆∞ (ext-int regΔ)
s+-⊆/ (s-var-∙ regΔ inΔ) = ⊆∞ (ext-var (reg-⊆/x∙ regΔ inΔ))
s+-⊆/ (s-arr₁ s s₁) with s+-⊆/ s₁
... | ⊆∞ x = ⊆∞ (ext-arr (s--⊆/ s) x)
s+-⊆/ (s-arr₂ s s₁) = ⊆I (s--⊆/ s) (s+-⊆/ s₁)
s+-⊆/ (s-arr₃ cloA grd s) = ⊆C cloA (s+-⊆/ s)
s+-⊆/ (s-∀ s) with s+-⊆/ s
... | ⊆∞ x = ⊆∞ (ext-∀ x)
s+-⊆/ (s-∀l s ic fd upC upD upj) with s+-⊆/ s
s+-⊆/ (s-∀l s case-𝕚 fd upC upD (↑tyʲ-𝕚 upj)) | r = ⊆∀-I (⊆/c-irrev-^0 r fd) upj
s+-⊆/ (s-∀l s case-𝕔 fd upC upD (↑tyʲ-𝕔 upj)) | r = ⊆∀-C (⊆/c-irrev-^0 r fd) upj
s+-⊆/ (s-∀l-no-appear s ic fd upC upD upj) with s+-⊆/ s
s+-⊆/ (s-∀l-no-appear s case-𝕚 fd upC upD (↑tyʲ-𝕚 upj)) | r = ⊆∀-I-no r upj
s+-⊆/ (s-∀l-no-appear s case-𝕔 fd upC upD (↑tyʲ-𝕔 upj)) | r = ⊆∀-C-no r upj
s+-⊆/ (s-svar-l x inΔ) = ⊆∞ (ext-var (⊆/x-refl x (⊢c-var-= (∋:=to∋= inΔ))))
s+-⊆/ (s-tapp s upj) = ⊆∀-T (s+-⊆/ s) upj
s+-⊆/ (s-svar-𝕚 inΓ s) = ⊆I-X (s-sregular s) (⊢c-var-= (∋:=to∋= inΓ))
s+-⊆/ (s-svar-𝕔 inΓ s) = ⊆C-X (s-sregular s) (⊢c-var-= (∋:=to∋= inΓ))
s+-⊆/ (s-svar-𝕥 inΓ s) = ⊆T-X (s-sregular s) (⊢c-var-= (∋:=to∋= inΓ))


infix 3 _≤_⟹_
data _≤_⟹_ : Type m → Type m → Type m → Set where
  ett-var : ‶ X ≤ B ⟹ B
  ett-arr : B ≤ D ⟹ T
          → A `→ B ≤ C `→ D ⟹ T
  ett-∀-𝕚 : A ≤ B' `→ C' ⟹ T'
          → (upB : ↑ty0 B ⇘ B')
          → (upC : ↑ty0 C ⇘ C')
          → (upT : ↑ty0 T ⇘ T')
          → `∀ A ≤ B `→ C ⟹ T
  ett-∀-𝕥 : A ≤ C ⟹ T'
          → (upT : ↑ty0 T ⇘ T')
          → `∀ A ≤ `∀ C ⟹ T

infix 3 _ε'_
data _ε'_ : Fin m → Type m → Set where
  ε-var : k ε' (‶ k)
  ε-arr : k ¬ε A
        → k ε' B
        → k ε' (A `→ B)
  ε-∀ : #S k ε' A
      → k ε' (`∀ A)



complete-ss+ : Δ ⊢ ∞ # A ⌞ ≤⁺ ⌝ B
             → Γ ⊆ Δ w/t A
             → Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ

complete-ss- : Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ B
             → Γ ⊆ Δ w/t B
             → Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ


complete-ss+ (s-int regΔ) ext with ⊆/-⊢c-eq ext ⊢c-int
... | refl = s-int regΔ
complete-ss+ (s-var-∙ regΔ inΔ) (ext-var x) with ⊆/-⊢c-eq (ext-var x) (⊢c-var-∙ (⊆/-∙out-∙in inΔ x))
... | refl = s-var-∙ regΔ inΔ
complete-ss+ (s-arr₁ s s₁) (ext-arr ext ext₁)
  with ⟨ Ψ , diff ⟩ ← ⅆ-total (⊆/-⊆ ext) (⊆/-⊆ ext₁)
  with ih ← complete-ss- {Γ = Ψ} s (ⅆ-⊆/ diff ext)
  = s-arr (s--subirrev-final ih diff (⊆/-⊢c ext)) (complete-ss+ s₁ ext₁)
complete-ss+ (s-∀ s) (ext-∀ ext) = s-∀ (complete-ss+ s ext)
complete-ss+ (s-svar-l x inΔ) ext'@(ext-var x₁) with ⊆/x-=out-in x₁ (∋:=to∋= inΔ)
... | is-ex inΓ = s-ex-l^ (⊆/x-^in-=out-inst inΓ inΔ x₁)
... | is-sol inΓ with refl ← ⊆/-⊢c-eq ext' (⊢c-var-= inΓ) = s-ex-l= x inΔ

complete-ss- (s-int regΔ) ext with ⊆/-⊢c-eq ext ⊢c-int
... | refl = s-int regΔ
complete-ss- (s-var-∙ regΔ inΔ) (ext-var x) with ⊆/-⊢c-eq (ext-var x) (⊢c-var-∙ (⊆/-∙out-∙in inΔ x))
... | refl = s-var-∙ regΔ inΔ
complete-ss- (s-arr₁ s s₁) (ext-arr ext ext₁)
  with ⟨ Ψ , diff ⟩  ← ⅆ-total (⊆/-⊆ ext) (⊆/-⊆ ext₁)
  with ih ← complete-ss+ {Γ = Ψ} s (ⅆ-⊆/ diff ext)
  = s-arr (s+-subirrev-final ih diff (⊆/-⊢c ext)) (complete-ss- s₁ ext₁)
complete-ss- (s-∀ s) (ext-∀ ext) = s-∀ (complete-ss- s ext)
complete-ss- (s-svar-r x inΔ) ext'@(ext-var x₁) with ⊆/x-=out-in x₁ (∋:=to∋= inΔ)
... | is-ex inΓ = s-ex-r^ (⊆/x-^in-=out-inst inΓ inΔ x₁)
... | is-sol inΓ with refl ← ⊆/-⊢c-eq ext' (⊢c-var-= inΓ) = s-ex-r= x inΔ
