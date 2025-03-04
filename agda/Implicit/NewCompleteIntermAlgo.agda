module Implicit.NewCompleteIntermAlgo where

open import Implicit.Language.All hiding (_⊆_w/v_; _⊆_w/t_)
open import Implicit.Algo.Base
-- open import Implicit.Algo.Properties.NewPolarity
open import Implicit.Interm.Base
open import Implicit.Interm.Ground
-- open import Implicit.Interm.Properties.Polarity


infix 3 _⊆_w/v_
data _⊆_w/v_ : Env n m → Env n m → Fin m → Set where
  ext-Z^ : (cloA : Γ ⊢c A)
         → Γ ,^ ⊆ Γ ,= A w/v #0
  ext-Z∙ : Γ ,∙ ⊆ Γ ,∙ w/v #0
  ext-S, : Γ ⊆ Δ w/v k
         → Γ , A ⊆ Δ , A w/v k
  ext-S^ : Γ ⊆ Δ w/v k
         → Γ ,^ ⊆ Δ ,^ w/v #S k
  ext-S∙ : Γ ⊆ Δ w/v k
         → Γ ,∙ ⊆ Δ ,∙ w/v #S k
  ext-S= : Γ ⊆ Δ w/v k
         → Γ ,= A ⊆ Δ ,= A w/v #S k
  ext-mark : TypEnv Γ
         → Γ ⋈ ⊆ Γ ⋈ w/v k

infix 3 _⊆_w/t_
data _⊆_w/t_ : Env n m → Env n m → Type m → Set where
  ext-int : Γ ⊆ Γ w/t Int
  ext-var : Γ ⊆ Δ w/v X
          → Γ ⊆ Δ w/t ‶ X
  ext-arr : Γ ⊆ Ω w/t A
          → Ω ⊆ Δ w/t B
          → Γ ⊆ Δ w/t A `→ B
  ext-∀   : Γ ,∙ ⊆ Δ ,∙ w/t A
          → Γ ⊆ Δ w/t `∀ A


⊆/-:=-^ : Δ ∋=² X
        → Γ ⊆ Δ w/v X
        → Γ ∋^² X
⊆/-:=-^ Z^ (ext-Z^ cloA) = Z^
⊆/-:=-^ (S, inΔ) (ext-S, ext) = S, (⊆/-:=-^ inΔ ext)
⊆/-:=-^ (S∙ inΔ) (ext-S∙ ext) = S∙ (⊆/-:=-^ inΔ ext)
⊆/-:=-^ (S^ inΔ) (ext-S^ ext) = S^ (⊆/-:=-^ inΔ ext)
⊆/-:=-^ (S= inΔ) (ext-S= ext) = S= (⊆/-:=-^ inΔ ext)

∋∙-⊆/ : Γ ∋∙ X
      → SubEnv Γ
      → Γ ⊆ Γ w/v X
∋∙-⊆/ Z (S∙ senv) = ext-Z∙
∋∙-⊆/ (S, inΓ) (S, senv) = ext-S, (∋∙-⊆/ inΓ senv)
∋∙-⊆/ (S∙ inΓ) (S∙ senv) = ext-S∙ (∋∙-⊆/ inΓ senv)
∋∙-⊆/ (S= inΓ) (S= senv) = ext-S= (∋∙-⊆/ inΓ senv)
∋∙-⊆/ (S^ inΓ) (S^ senv) = ext-S^ (∋∙-⊆/ inΓ senv)
∋∙-⊆/ (S⋈ inΓ) (Z⋈ x) = ext-mark x

∋=¹-⊆/ : Γ ∋=¹ X
       → SubEnv Γ
       → Γ ⊆ Γ w/v X
∋=¹-⊆/ (S, inΓ) (S, senv) = ext-S, (∋=¹-⊆/ inΓ senv)
∋=¹-⊆/ (S∙ inΓ) (S∙ senv) = ext-S∙ (∋=¹-⊆/ inΓ senv)
∋=¹-⊆/ (S^ inΓ) (S^ senv) = ext-S^ (∋=¹-⊆/ inΓ senv)
∋=¹-⊆/ (S= inΓ) (S= senv) = ext-S= (∋=¹-⊆/ inΓ senv)
∋=¹-⊆/ (S⋈ x) (Z⋈ x₁) = ext-mark x₁

⊢c¹-⊆/ : Γ ⊢c¹ A
       → SubEnv Γ
       → Γ ⊆ Γ w/t A

∋:=¹-⊢c¹ : Γ ∋ X :=¹ A
        → SubClosed Γ
        → Γ ⊢c¹ A
∋:=¹-⊢c¹ (S, inΓ) (clo-S, sclo cloA) = {!!}
∋:=¹-⊢c¹ (S∙ inΓ up) (clo-S∙ sclo) = {!∋:=¹-⊢c¹ inΓ sclo!}
∋:=¹-⊢c¹ (S^ inΓ up) (clo-S^ sclo) = {!∋:=¹-⊢c¹ inΓ sclo!}
∋:=¹-⊢c¹ (S= inΓ up) (clo-S= sclo cloA) = {!∋:=¹-⊢c¹ inΓ sclo!}
∋:=¹-⊢c¹ (S⋈ x) (clo-Z x₁) = {!!}

infix 3 _⊢_~_
data _⊢_~_ : Env n m → Counter × Type m → Context n m → Set where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~I : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ □ ⇒ e ⇒ A)
    → Γ ⊆ Ω w/t A
    → Ω ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ~ ([ e ]↝ Σ)

  ~C : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ τ A ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕔 j , A `→ B ⟩ ~ ([ e ]↝ Σ)

infix 3 _⊆_w/t_w/c_
data _⊆_w/t_w/c_ : Env n m → Env n m → Type m → Counter → Set where
  ⊆Z : Γ ⊆ Γ w/t A w/c Z
  ⊆∞ : Γ ⊆ Δ w/t A
     → Γ ⊆ Δ w/t A w/c ∞
  ⊆I : (ext : Γ ⊆ Ω w/t A)
     → Ω ⊆ Δ w/t B w/c j
     → Γ ⊆ Δ w/t (A `→ B) w/c (𝕚 j)
  ⊆C : Γ ⊆ Δ w/t B w/c j
     → Γ ⊆ Δ w/t (A `→ B) w/c (𝕔 j)
  ⊆∀-I : Γ ,∙ ⊆ Δ ,∙ w/t A w/c (𝕚 j)
     → Γ ⊆ Δ w/t `∀ A w/c (𝕚 j)
  ⊆∀-C : Γ ,∙ ⊆ Δ ,∙ w/t A w/c (𝕔 j)
     → Γ ⊆ Δ w/t `∀ A w/c (𝕔 j)

postulate
  open-close : ∀ (Γ : Env n m) A → Γ ⊢c A ⊎ Γ ⊢o A


complete-ss+ : Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
             → Γ ⊆ Δ w/t A
             → Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ

complete-ss- : Δ ⊢ j # A ⌞ ≤⁻ ⌝ B
             → Γ ⊆ Δ w/t B
             → Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ

complete-s :  Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → Γ ⊆ Δ w/t A
            → Γ ⊢ ⟨ j , B ⟩ ~ Σ
            → Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
