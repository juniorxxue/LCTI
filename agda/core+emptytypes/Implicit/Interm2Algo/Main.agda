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

-- complete-s0 : Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ B
--             → Γ ⊢ ⟨ j , B ⟩ ~t Σ
--             → Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ B
-- complete-s0 s j~Σ = complete-s s (s+-⊆/ s) (~t-~s j~Σ)

-- complete : Γ ⊢ j # e ⦂ A
--          → Γ ⊢ ⟨ j , A ⟩ ~t Σ
--          → Γ ⊢ Σ ⇒ e ⇒ A
-- complete (⊢lit cloΓ) ~Z = ⊢lit cloΓ
-- complete (⊢var cloΓ x∈Γ) ~Z = ⊢var cloΓ x∈Γ
-- complete (⊢ann ⊢e) ~Z = ⊢ann (complete ⊢e ~∞)
-- complete (⊢lam₁ ⊢e) ~∞ = ⊢lam₁ (complete ⊢e ~∞)
-- complete (⊢lam₂ ⊢e) (~I {Σ = Σ} ⊢e₁ j~Σ)
--   with reg-S, regΓ regA ← t-tregular ⊢e
--   with ⟨ Σ' , upΣ ⟩ ← ↑tmᶜ0-total Σ
--   = ⊢lam₂ ⊢e₁ upΣ (complete ⊢e (~weaken,0 j~Σ upΣ regA))
-- complete (⊢app₁ ⊢e ⊢e₁) j~Σ = ⊢app (complete ⊢e (~C (complete ⊢e₁ ~∞) j~Σ))
-- complete (⊢app₂ ⊢e ⊢e₁) j~Σ = ⊢app (complete ⊢e (~I (complete ⊢e₁ ~Z) j~Σ))
-- complete (⊢sub ⊢e B≤A x j≢Z) j~Σ = ⊢sub (complete ⊢e ~Z) (nonempty j≢Z j~Σ) x (complete-s0 B≤A j~Σ)
--   where nonempty : NonZ j
--                  → Γ ⊢ ⟨ j , A ⟩ ~t Σ
--                  → NonEmpty Σ
--         nonempty nz-∞ ~∞ = ne-τ
--         nonempty nz-I (~I ⊢e j~Σ) = ne-app
--         nonempty nz-C (~C ⊢e j~Σ) = ne-app
--         nonempty nz-T (~T ~j st) = ne-tapp
-- complete (⊢tabs ⊢e) ~Z = ⊢tabs (complete ⊢e ~Z)
-- complete (⊢tapp ⊢e st) ~j = ⊢tapp (complete ⊢e (~T ~j st)) st

-- -- corollaries
-- complete-0 : Γ ⊢ Z # e ⦂ A
--            → Γ ⊢ □ ⇒ e ⇒ A
-- complete-0 ⊢e = complete ⊢e ~Z

-- complete-∞ : Γ ⊢ ∞ # e ⦂ A
--            → Γ ⊢ τ A ⇒ e ⇒ A
-- complete-∞ ⊢e = complete ⊢e ~∞
