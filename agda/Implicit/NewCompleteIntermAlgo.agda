module Implicit.NewCompleteIntermAlgo where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm.Base
open import Implicit.NewCompleteIntermAlgoAux

postulate
  open-close : ∀ (Γ : Env n m) A → Γ ⊢c A ⊎ Γ ⊢o A
  subsumption0 : Γ ⊢ □ ⇒ e ⇒ A
             → Γ ⊢ τ A ⇒ e ⇒ A


infix 3 _⊆_w/t_w/c_
data _⊆_w/t_w/c_ : Env n m → Env n m → Type m → Counter → Set where
  ⊆Z : Γ ⊆ Γ w/t A w/c Z
  ⊆∞ : Γ ⊆ Δ w/t A
     → Γ ⊆ Δ w/t A w/c ∞
  ⊆I : (ext : Γ ⊆ Ω w/t A)
     → Ω ⊆ Δ w/t B w/c j
     → Γ ⊆ Δ w/t (A `→ B) w/c (𝕚 j)
  ⊆C : (Γ ⊢c A)
     → Γ ⊆ Δ w/t B w/c j
     → Γ ⊆ Δ w/t (A `→ B) w/c (𝕔 j)
  ⊆∀-I : Γ ,∙ ⊆ Δ ,∙ w/t A w/c (𝕚 j)
     → Γ ⊆ Δ w/t `∀ A w/c (𝕚 j)
  ⊆∀-C : Γ ,∙ ⊆ Δ ,∙ w/t A w/c (𝕔 j)
     → Γ ⊆ Δ w/t `∀ A w/c (𝕔 j)

complete-ss+ : Δ ⊢ ∞ # A ⌞ ≤⁺ ⌝ B
             → Γ ⊆ Δ w/t A
             → Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ

complete-ss- : Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ B
             → Γ ⊆ Δ w/t B
             → Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ

complete-s :  Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → Γ ⊆ Δ w/t A w/c j
            → Γ ⊢ ⟨ j , B ⟩ ~s Σ
            → Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B

complete-ss+ (s-int regΔ) ext with ⊆/-⊢c-eq ext ⊢c-int
... | refl = s-int regΔ
complete-ss+ (s-var-∙ regΔ inΔ) (ext-var x) with ⊆/-⊢c-eq (ext-var x) (⊢c-var-∙ (⊆/-∙out-∙in inΔ x))
... | refl = s-var-∙ regΔ inΔ

complete-ss+ (s-arr₁ s s₁) (ext-arr ext ext₁) with ⅆ-total (⊆/-⊆ ext) (⊆/-⊆ ext₁)
... | ⟨ Ψ , diff ⟩ = s-arr {!complete-ss- s!} (complete-ss+ s₁ ext₁)
complete-ss+ (s-∀ s) (ext-∀ ext) = s-∀ (complete-ss+ s ext)
complete-ss+ (s-var-sub-l x inΔ) (ext-var x₁) = {!!}

complete-ss- s ext = {!!}

complete-s {j = Z} (s-refl regΔ cloA grd) ⊆Z ~Z = s-empty regΔ cloA grd
complete-s {j = ∞} s (⊆∞ x) ~∞ = s-type (complete-ss+ s x)
complete-s {j = 𝕚 j} {Γ = Γ} (s-arr₂ {A = A} s s₁) (⊆I ext ext₁) (~I ⊢e j~Σ) with open-close Γ A
... | inj₁ cloA
  with refl ← ⊆/-⊢c-eq ext cloA = s-term-c cloA {!!} (subsumption0 ⊢e) (complete-s s₁ ext₁ j~Σ)
... | inj₂ opnA = s-term-o opnA ⊢e {!complete-ss- s !} (complete-s s₁ ext₁ (~irrev j~Σ (⊆/-⊆ ext)))
complete-s {j = 𝕔 j} (s-arr₃ cloA grd s) (⊆C cloA' ext) (~C ⊢e j~Σ) = s-term-c cloA' {!!} ⊢e (complete-s s ext j~Σ)
complete-s (s-∀l s ic fd upC upD) (⊆∀-I ext) j~'@(~I ⊢e j~) = s-∀l (complete-s s {!ext!} {!j~'!}) {!!} {!!} upC upD
complete-s (s-∀l s ic fd upC upD) (⊆∀-C ext) j~ = {!!}


s+-⊆/ : Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
     → Δ ⊆ Δ w/t A w/c j

s--⊆/ : Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ B
      → Δ ⊆ Δ w/t B

s+-⊆/ (s-refl regΔ cloA grd) = ⊆Z
s+-⊆/ (s-int regΔ) = ⊆∞ (ext-int regΔ)
s+-⊆/ (s-var-∙ regΔ inΔ) = ⊆∞ (ext-var (reg-⊆/x∙ regΔ inΔ))
s+-⊆/ (s-arr₁ s s₁) with s+-⊆/ s₁
... | ⊆∞ x = ⊆∞ (ext-arr (s--⊆/ s) x)
s+-⊆/ (s-arr₂ s s₁) = ⊆I (s--⊆/ s) (s+-⊆/ s₁)
s+-⊆/ (s-arr₃ cloA grd s) = ⊆C cloA (s+-⊆/ s)
s+-⊆/ (s-∀ s) with s+-⊆/ s
... | ⊆∞ x = ⊆∞ (ext-∀ x)
s+-⊆/ (s-∀l s ic fd upC upD) with s+-⊆/ s
s+-⊆/ (s-∀l s case-𝕚 fd upC upD) | r = ⊆∀-I {!!}
s+-⊆/ (s-∀l s case-𝕔 fd upC upD) | r = ⊆∀-C {!!}
s+-⊆/ (s-var-sub-l x inΔ) = ⊆∞ (ext-var {!!})

complete-s0 : Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → Γ ⊢ ⟨ j , B ⟩ ~t Σ
            → Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ B
complete-s0 s j~Σ = complete-s s (s+-⊆/ s) (~t-~s j~Σ)

{-
reg-⊆/ : Γ ⊢r A
       → Γ ⊆ Γ w/t A w/c j
reg-⊆/ {j = Z} regA = ⊆Z
reg-⊆/ {j = ∞} regA = ⊆∞ {!!}
reg-⊆/ {j = 𝕚 j} ⊢r-int = {!!}
reg-⊆/ {j = 𝕚 j} (⊢r-var-∙ inΓ) = {!!}
reg-⊆/ {j = 𝕚 j} (⊢r-arr regA regA₁) = {!!}
reg-⊆/ {j = 𝕚 j} (⊢r-∀ regA) = ⊆∀-I (reg-⊆/ regA)
reg-⊆/ {j = 𝕔 j} regA = {!!}
-}

complete : Γ ⊢ j # e ⦂ A
         → Γ ⊢ ⟨ j , A ⟩ ~t Σ
         → Γ ⊢ Σ ⇒ e ⇒ A
complete (⊢lit cloΓ) ~Z = ⊢lit cloΓ
complete (⊢var cloΓ x∈Γ) ~Z = ⊢var cloΓ x∈Γ
complete (⊢ann ⊢e) ~Z = ⊢ann (complete ⊢e ~∞)
complete (⊢lam₁ ⊢e) ~∞ = ⊢lam₁ (complete ⊢e ~∞)
complete (⊢lam₂ ⊢e) (~I {Σ = Σ} ⊢e₁ j~Σ) with ↑tmᶜ0-total Σ
... | ⟨ Σ' , upΣ ⟩ = ⊢lam₂ ⊢e₁ upΣ (complete ⊢e (~weaken,0 j~Σ upΣ))
complete (⊢app₁ ⊢e ⊢e₁) j~Σ = ⊢app (complete ⊢e (~C (complete ⊢e₁ ~∞) j~Σ))
complete (⊢app₂ ⊢e ⊢e₁) j~Σ = ⊢app (complete ⊢e (~I (complete ⊢e₁ ~Z) j~Σ))
complete (⊢sub ⊢e B≤A x j≢Z) j~Σ = ⊢sub (complete ⊢e ~Z) (nonempty j≢Z j~Σ) x (complete-s0 B≤A j~Σ)
  where nonempty : NonZ j
                 → Γ ⊢ ⟨ j , A ⟩ ~t Σ
                 → NonEmpty Σ
        nonempty nz-∞ ~∞ = ne-τ
        nonempty nz-I (~I ⊢e j~Σ) = ne-app
        nonempty nz-C (~C ⊢e j~Σ) = ne-app
complete (⊢tabs ⊢e) ~Z = ⊢tabs (complete ⊢e ~Z)
