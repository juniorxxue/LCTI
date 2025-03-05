module Implicit.NewCompleteIntermAlgo where

open import Implicit.Language.All
open import Implicit.Algo.Base
-- open import Implicit.Algo.Properties.NewPolarity
open import Implicit.Interm.Base
-- open import Implicit.Interm.Ground
-- open import Implicit.Interm.Properties.Polarity


reg-⊆/x : SEnv Δ
        → Δ ∋∙ X
        → Δ ⊆ Δ w/v X
reg-⊆/x senv Z = ext-Z∙
reg-⊆/x (S, senv) (S, inΔ) = ext-S, (reg-⊆/x senv inΔ)
reg-⊆/x (S∙ senv) (S∙ inΔ) = ext-S∙ (reg-⊆/x senv inΔ)
reg-⊆/x (S= senv) (S= inΔ) = ext-S= (reg-⊆/x senv inΔ)
reg-⊆/x (S^ senv) (S^ inΔ) = ext-S^ (reg-⊆/x senv inΔ)
reg-⊆/x (Z⋈ x) (S⋈ inΔ) = ext-mark x

reg-⊆/ : SEnv Δ
       → Δ ⊢r A
       → Δ ⊆ Δ w/t A
reg-⊆/ senv ⊢r-int = ext-int
reg-⊆/ senv (⊢r-var-∙ inΓ) = ext-var (reg-⊆/x senv inΓ)
reg-⊆/ senv (⊢r-arr regA regA₁) = ext-arr (reg-⊆/ senv regA) (reg-⊆/ senv regA₁)
reg-⊆/ senv (⊢r-∀ regA) = ext-∀ (reg-⊆/ (S∙ senv) regA)


⊆/-:=-^ : Δ ∋= X
        → Γ ⊆ Δ w/v X
        → Γ ∋^ X
⊆/-:=-^ (Z x) (ext-Z^ cloA) = Z x
⊆/-:=-^ (S, inΔ) (ext-S, ext) = S, (⊆/-:=-^ inΔ ext)
⊆/-:=-^ (S∙ inΔ) (ext-S∙ ext) = S∙ (⊆/-:=-^ inΔ ext)
⊆/-:=-^ (S^ inΔ) (ext-S^ ext) = S^ (⊆/-:=-^ inΔ ext)
⊆/-:=-^ (S= inΔ) (ext-S= ext) = S= (⊆/-:=-^ inΔ ext)

∋∙-⊆/ : Γ ∋∙ X
      → SEnv Γ
      → Γ ⊆ Γ w/v X
∋∙-⊆/ Z (S∙ senv) = ext-Z∙
∋∙-⊆/ (S, inΓ) (S, senv) = ext-S, (∋∙-⊆/ inΓ senv)
∋∙-⊆/ (S∙ inΓ) (S∙ senv) = ext-S∙ (∋∙-⊆/ inΓ senv)
∋∙-⊆/ (S= inΓ) (S= senv) = ext-S= (∋∙-⊆/ inΓ senv)
∋∙-⊆/ (S^ inΓ) (S^ senv) = ext-S^ (∋∙-⊆/ inΓ senv)
∋∙-⊆/ (S⋈ inΓ) (Z⋈ x) = ext-mark x


infix 3 _⊢_~_
data _⊢_~_ : Env n m → Counter × Type m → Context n m → Set where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~I : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : 𝕣 Γ ⊢ □ ⇒ e ⇒ A)
    → Γ ⊆ Ω w/t A
    → Ω ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ~ ([ e ]↝ Σ)

  ~C : ∀ {Γ : Env n m} {j B Σ e}
    → (⊢e : 𝕣 Γ ⊢ τ A% ⇒ e ⇒ A%)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕔 j , A% `→ B ⟩ ~ ([ e ]↝ Σ)

complete : Γ ⊢ j # e ⦂ A
         → Γ ⋈ ⊢ ⟨ j , A ⟩ ~ Σ
         → Γ ⊢ Σ ⇒ e ⇒ A
complete (⊢lit cloΓ) ~Z = ⊢lit cloΓ
complete (⊢var cloΓ x∈Γ) ~Z = ⊢var cloΓ x∈Γ
complete (⊢ann ⊢e) ~Z = ⊢ann (complete ⊢e ~∞)
complete (⊢lam₁ ⊢e) ~∞ = ⊢lam₁ (complete ⊢e ~∞)
complete (⊢lam₂ ⊢e) (~I ⊢e₁ x ~j) = ⊢lam₂ ⊢e₁ {!!} (complete ⊢e {!!})
complete (⊢app₁ ⊢e ⊢e₁) ~j = ⊢app (complete ⊢e (~C (complete ⊢e₁ ~∞) ~j))
complete (⊢app₂ ⊢e ⊢e₁) ~j = ⊢app (complete ⊢e (~I (complete ⊢e₁ ~Z) (reg-⊆/ (Z⋈ {!!}) {!!}) ~j))
complete (⊢sub ⊢e B≤A x j≢Z) ~j = ⊢sub (complete ⊢e ~Z) _ x (complete-s0 B≤A ~j) where postulate
   complete-s0 : Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ B
               → Γ ⋈ ⊢ ⟨ j , B ⟩ ~ Σ
               → Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ B
complete (⊢tabs ⊢e) ~Z = ⊢tabs (complete ⊢e ~Z)

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

postulate
  open-close : ∀ (Γ : Env n m) A → Γ ⊢c A ⊎ Γ ⊢o A


complete-ss+ : Δ ⊢ ∞ # A ⌞ ≤⁺ ⌝ B
             → Γ ⊆ Δ w/t A
             → Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ

complete-ss- : Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ B
             → Γ ⊆ Δ w/t B
             → Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ

complete-s :  Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → Γ ⊆ Δ w/t A w/c j
            → Γ ⊢ ⟨ j , B ⟩ ~ Σ
            → Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B

complete-ss+ (s-int regΔ) ext = {!!}
complete-ss+ (s-var-∙ regΔ inΔ) ext = {!!}
complete-ss+ (s-arr₁ s s₁) (ext-arr ext ext₁) = s-arr {!complete-ss- s!} (complete-ss+ s₁ ext₁)
complete-ss+ (s-∀ s) ext = {!!}
complete-ss+ (s-var-sub-l x inΔ) (ext-var x₁) = {!!}

complete-s {j = Z} (s-refl regΔ cloA grd) ⊆Z ~Z = s-empty regΔ cloA grd
complete-s {j = ∞} s (⊆∞ x) ~∞ = s-type (complete-ss+ s x)
complete-s {j = 𝕚 j} (s-arr₂ s s₁) (⊆I ext ext₁) (~I ⊢e x j~Σ) = s-term-c {!!} {!!} {!!} {!!}
complete-s (s-∀l s ic fd upC upD) (⊆∀-I ext) j~ = {!!}
complete-s (s-∀l s ic fd upC upD) (⊆∀-C ext) j~ = {!!}
complete-s {j = 𝕔 j} (s-arr₃ cloA grd s) (⊆C cloA' ext) (~C ⊢e j~Σ) = s-term-c cloA' {!!} ⊢e (complete-s s ext j~Σ)

complete-s0 : Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → Γ ⊢ ⟨ j , B ⟩ ~ Σ
            → Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ B
complete-s0 {j = j} s ~j = complete-s s {!!} {!!}

s-⊆/ : Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
     → Δ ⊆ Δ w/t A w/c j
s-⊆/ (s-refl regΔ cloA grd) = ⊆Z
s-⊆/ (s-int regΔ) = ⊆∞ ext-int
s-⊆/ (s-var-∙ regΔ inΔ) = ⊆∞ (ext-var {!!})
s-⊆/ (s-arr₁ s s₁) = ⊆∞ (ext-arr {!!} {!!})
s-⊆/ (s-arr₂ s s₁) = ⊆I {!!} (s-⊆/ s₁)
s-⊆/ (s-arr₃ cloA grd s) = ⊆C cloA (s-⊆/ s)
s-⊆/ (s-∀ s) with s-⊆/ s
... | ⊆∞ x = ⊆∞ (ext-∀ x)
s-⊆/ (s-∀l s ic fd upC upD) with s-⊆/ s
... | r = {!!}
s-⊆/ (s-var-sub-l x inΔ) = ⊆∞ {!!}

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
