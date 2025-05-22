module Implicit.Interm2Algo.Main where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm.All
open import Implicit.Interm2Algo.Counter2Context
open import Implicit.Interm2Algo.NewExtIrrev
open import Implicit.Interm2Algo.EnvDiff
open import Implicit.Interm2Algo.OpenClose
open import Implicit.Interm2Algo.SwapSS

complete-ss+ : Δ ⊢ `∞ # A ⌞ ≤⁺ ⌝ B
             → Γ ⊆ Δ w/t A
             → Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ

complete-ss- : Δ ⊢ `∞ # A ⌞ ≤⁻ ⌝ B
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
... | is-ex inΓ = {!!}
-- s-ex-l^ (⊆/x-^in-=out-inst inΓ inΔ x₁)
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
... | is-ex inΓ = {!!}
-- s-ex-r^ (⊆/x-^in-=out-inst inΓ inΔ x₁)
... | is-sol inΓ with refl ← ⊆/-⊢c-eq ext' (⊢c-var-= inΓ) = s-ex-r= x inΔ

complete-s-n : Δ ⊢ (`𝕟 i) # A ⌞ ≤⁻ ⌝ B
              → Γ ⊆ Δ w/t B w/n i
              → ⟨ i , A ⟩ ~₁ P
              → Γ ⊢ B ≤⁺ `p P ⊣ Δ ↪ A
complete-s-n (s-refl- regΔ cloA grd) (⊆/n-Z regΓ) ~₁Z = s-empty regΔ cloA grd
complete-s-n (s-arr-n s s₁) (⊆/n-S ext ext₁) (~₁S ~p)
  with ⟨ Ψ , diff ⟩  ← ⅆ-total (⊆/-⊆ ext) (⊆/n-⊆ ext₁)
  with ih ← complete-ss+ {Γ = Ψ} s (ⅆ-⊆/ diff ext)
  = s-term-p (swap-ss (s+-subirrev-final ih diff (⊆/-⊢c ext))) (complete-s-n s₁ ext₁ ~p)

complete-s :  Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → Γ ⊆ Δ w/t A w/c j
            → Γ ⊢ ⟨ j , B ⟩ ~s Σ
            → Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
complete-s {j = 𝔼 ∞} s (⊆/c-𝔼 (⊆/e-∞ ext)) (~𝔼 ~₂∞) = s-type (complete-ss+ s ext)
complete-s {j = 𝔼 (𝕟 0)} (s-refl+ regΔ cloA grd) (⊆/c-𝔼 (⊆/e-𝕟 (⊆/n-Z regΓ))) (~𝔼 (~₂p ~₁Z)) = s-empty regΔ cloA grd
complete-s {j = 𝕊₍ ∞ ₎ j} (s-arr₂ s s₁) (⊆/c-𝕊 (⊆/e!-∞ cloA) ext) (~𝕊 ~₂∞ ⊢e ~j) = s-term-c cloA {!!} ⊢e (complete-s s₁ ext ~j)
complete-s {j = 𝕊₍ 𝕟 i ₎ j} (s-arr₂ s s₁) (⊆/c-𝕊 ext-e ext) (~𝕊 (~₂p ~₁) ⊢e ~j) with ⊆/e!-openclose ext-e
... | inj₁ opnA = s-term-o opnA {!!} {!!} {!!} {!!}
... | inj₂ cloA = s-term-c cloA {!!} (subsumption0 ⊢e) (complete-s s₁ {!!} ~j)
complete-s {j = 𝕊₍ 𝕖 ₎ j} (s-∀l s upC upD upj) ext (~𝕊 ~a ⊢e ~j)
  = s-∀l (complete-s s {!!} {!!}) {!!} {!!} upC upD
complete-s {j = 𝕋₍ A ₎ j} s ext ~j = {!!}

lemma : Δ ⊢ 𝔼 (𝕟 i) # C ⌞ ≤⁻ ⌝ A
      → ⟨ i , C ⟩ ~₁ P
      → Γ ⊢ A ↦₁ P


{-
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
-}

{-

s+-⊆/ : Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
      → Δ ⊆ Δ w/t A w/c j

s--⊆/ : Δ ⊢ `∞ # A ⌞ ≤⁻ ⌝ B
      → Δ ⊆ Δ w/t B

s--⊆/-n : Δ ⊢ (`𝕟 i) # A ⌞ ≤⁻ ⌝ B
        → Δ ⊆ Δ w/t B w/n i

s--⊆/-n (s-refl- regΔ cloA grd) = ⊆/n-Z regΔ
s--⊆/-n (s-arr-n s s₁) with s+-⊆/ s
... | ⊆/c-𝔼 (⊆/e-∞ ext) = ⊆/n-S ext (s--⊆/-n s₁)
-}


-- complete-s0 : Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ B
--             → Γ ⊢ ⟨ j , B ⟩ ~t Σ
--             → Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ B
-- complete-s0 s j~Σ = complete-s s (s+-⊆/ s) (~t-~s j~Σ)

-- match1-~ : Match1 A i
--          → ∃[ P ]( ⟨ i , A ⟩ ~₁ P )
-- match1-~ m1-z = ⟨ □ , ~₁Z ⟩
-- match1-~ {A = A `→ B} (m1-s mt1) = ⟨ A ◐↝ match1-~ mt1 .proj₁ , ~₁S (match1-~ mt1 .proj₂) ⟩

-- match2-~ : Match2 A 𝕖
--         → ∃[ δ ]( ⟨ 𝕖 , A ⟩ ~₂ δ )
-- match2-~ {A = A} m2-∞ = ⟨ τ A , ~₂∞ ⟩
-- match2-~ {A = A} (m2-n mt1)
--   with ⟨ P , ~j ⟩ ← match1-~ mt1 = ⟨ p P , ~₂p ~j ⟩

-- complete : Γ ⊢ j # e ⦂ A
--          → Γ ⊢ ⟨ j , A ⟩ ~t Σ
--          → Γ ⊢ Σ ⇒ e ⇒ A
-- complete (⊢lit regΓ) ~j = {!!}
-- complete (⊢var regΓ x∈Γ) ~j = {!!}
-- complete (⊢ann ⊢e) ~j = {!!}
-- complete (⊢lam₁ ⊢e) ~j = {!!}
-- complete (⊢lam₂ ⊢e) (~𝕊 {Σ = Σ} (~₂p ~₁Z) ⊢e₁ ~j)
--   with reg-S, regΓ regA ← t-tregular ⊢e
--   with ⟨ Σ' , upΣ ⟩ ← ↑tmᶜ0-total Σ = ⊢lam₂ ⊢e₁ upΣ (complete ⊢e (~weaken,0 ~j upΣ regA))
-- complete (⊢lam₃ ⊢e) (~𝔼 (~₂p (~₁S ~j))) = ⊢lam₃ (complete ⊢e (~𝔼 (~₂p ~j)))
-- complete (⊢app ⊢e ⊢e₁) ~j
--   with m-𝔼 mt ← t-match ⊢e₁
--   with ⟨ δ , ~j' ⟩ ← match2-~ mt = ⊢app (complete ⊢e (~𝕊 ~j' (complete ⊢e₁ (~𝔼 ~j')) ~j))
-- complete (⊢sub ⊢e B≤A gc j≢Z) ~j = ⊢sub (complete ⊢e (~𝔼 (~₂p ~₁Z))) {!!} gc (complete-s0 B≤A ~j)
-- complete (⊢tabs ⊢e) (~𝔼 (~₂p ~₁Z)) = ⊢tabs (complete ⊢e (~𝔼 (~₂p ~₁Z)))
-- complete (⊢tapp ⊢e st) ~j = ⊢tapp (complete ⊢e (~𝕋 ~j st)) st

-- -- corollaries
-- complete-0 : Γ ⊢ `𝕫 # e ⦂ A
--            → Γ ⊢ `□ ⇒ e ⇒ A
-- complete-0 ⊢e = complete ⊢e (~𝔼 (~₂p ~₁Z))

-- complete-∞ : Γ ⊢ `∞ # e ⦂ A
--            → Γ ⊢ `τ A ⇒ e ⇒ A
-- complete-∞ ⊢e = complete ⊢e (~𝔼 ~₂∞)
