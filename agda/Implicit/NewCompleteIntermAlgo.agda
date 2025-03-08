module Implicit.NewCompleteIntermAlgo where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm.Base
open import Implicit.Interm.Ground
open import Implicit.NewCompleteIntermAlgoAux
open import Implicit.NewCompleteIntermAlgoAux2

postulate
  open-close : ∀ (Γ : Env n m) A → Γ ⊢c A ⊎ Γ ⊢o A
  subsumption0 : Γ ⊢ □ ⇒ e ⇒ A
             → Γ ⊢ τ A ⇒ e ⇒ A

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
complete-ss+ (s-var-sub-l x inΔ) ext'@(ext-var x₁) with ⊆/x-=out-in x₁ (∋:=to∋= inΔ)
... | is-ex inΓ = s-ex-l^ (⊆/x-^in-=out-inst inΓ inΔ x₁)
... | is-sol inΓ with refl ← ⊆/-⊢c-eq ext' (⊢c-var-= inΓ) = s-ex-l= x inΔ

complete-ss- (s-int regΔ) ext with ⊆/-⊢c-eq ext ⊢c-int
... | refl = s-int regΔ
complete-ss- (s-var-∙ regΔ inΔ) (ext-var x) with ⊆/-⊢c-eq (ext-var x) (⊢c-var-∙ (⊆/-∙out-∙in inΔ x))
... | refl = s-var-∙ regΔ inΔ
complete-ss- (s-arr₁ s s₁) (ext-arr ext ext₁) with ⅆ-total (⊆/-⊆ ext) (⊆/-⊆ ext₁)
... | ⟨ Ψ , diff ⟩ = s-arr {!complete-ss- s!} (complete-ss- s₁ ext₁)
complete-ss- (s-∀ s) (ext-∀ ext) = s-∀ (complete-ss- s ext)
complete-ss- (s-var-sub-r x inΔ) ext'@(ext-var x₁) with ⊆/x-=out-in x₁ (∋:=to∋= inΔ)
... | is-ex inΓ = s-ex-r^ (⊆/x-^in-=out-inst inΓ inΔ x₁)
... | is-sol inΓ with refl ← ⊆/-⊢c-eq ext' (⊢c-var-= inΓ) = s-ex-r= x inΔ

complete-s {j = Z} (s-refl regΔ cloA grd) (⊆Z regΓ) ~Z = s-empty regΔ cloA grd
complete-s {j = ∞} s (⊆∞ x) ~∞ = s-type (complete-ss+ s x)
complete-s {j = 𝕚 j} {Γ = Γ} (s-arr₂ {A = A} s s₁) (⊆I ext ext₁) (~I ⊢e j~Σ) with open-close Γ A
... | inj₁ cloA
  with refl ← ⊆/-⊢c-eq ext cloA = s-term-c cloA (⊆-⊢c-≫ (⊆/c-⊆ ext₁) cloA (s--≫ s)) (subsumption0 ⊢e) (complete-s s₁ ext₁ j~Σ)
... | inj₂ opnA = s-term-o opnA ⊢e {!complete-ss- !} (complete-s s₁ ext₁ (~irrev j~Σ (⊆/-⊆ ext)))
complete-s {j = 𝕔 j} (s-arr₃ cloA grd s) (⊆C cloA' ext) (~C ⊢e j~Σ) = s-term-c cloA' (⊆-⊢c-≫ (⊆/c-⊆ ext) cloA' grd) ⊢e (complete-s s ext j~Σ)
complete-s (s-∀l s ic fd upC upD) (⊆∀-I ext) j~'@(~I {Σ = Σ} {e = e} ⊢e j~) with ↑tyᶜ0-total Σ | ↑tyᵉ0-total e
... | ⟨ Σ' , upΣ ⟩ | ⟨ e' , upe ⟩ = let weaken-j~ = (~weaken^0 (~I ⊢e j~) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ))
                                    in s-∀l (complete-s s {!!} weaken-j~ ) upΣ upe upC upD
complete-s (s-∀l s ic fd upC upD) (⊆∀-C ext) j~'@(~C {Σ = Σ} {e = e} ⊢e j~) with ↑tyᶜ0-total Σ | ↑tyᵉ0-total e
... | ⟨ Σ' , upΣ ⟩ | ⟨ e' , upe ⟩ = let weaken-j~ = (~weaken^0 (~C ⊢e j~) (↑ty-arr upC upD) (↑tyᶜ-e upe upΣ))
                                    in s-∀l (complete-s s {!!} weaken-j~) upΣ upe upC upD


s+-⊆/ : Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
      → Δ ⊆ Δ w/t A w/c j

s--⊆/ : Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ B
      → Δ ⊆ Δ w/t B

s+-⊆/ (s-refl regΔ cloA grd) = (⊆Z regΔ)
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
s+-⊆/ (s-var-sub-l x inΔ) = ⊆∞ (ext-var (⊆/x-⊢c x (⊢c-var-= (∋:=to∋= inΔ))))

complete-s0 : Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → Γ ⊢ ⟨ j , B ⟩ ~t Σ
            → Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ B
complete-s0 s j~Σ = complete-s s (s+-⊆/ s) (~t-~s j~Σ)

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
