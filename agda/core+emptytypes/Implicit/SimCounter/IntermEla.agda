module Implicit.SimCounter.IntermEla where

open import Implicit.Language.All
open import Implicit.SimCounter.RegularNew
open import Implicit.SimCounter.Interm

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------

variable
  A✦ B✦ C✦ D✦ : Type m

infix 3 _⊢_#_⌞_⌝_↡_
data _⊢_#_⌞_⌝_↡_ : Env n m → Counter m → Type m → Polar → Type m → Type m → Set where
  s-refl :
      (regΔ : SRegularS Δ)
    → (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊢ Z # A ⌞ ≤⁺ ⌝ A% ↡ A
  s-int :
      (regΔ : SRegularS Δ)
    → Δ ⊢ ∞ # Int ⌞ ≤ ⌝ Int ↡ Int
  s-var-∙ :
      (regΔ : SRegularS Δ)
    → (inΔ : Δ ∋∙ X)
    → Δ ⊢ ∞ # ‶ X ⌞ ≤ ⌝ ‶ X ↡ ‶ X
  s-arr₁ :
      Δ ⊢ ∞ # C ⌞ ⋆ ≤ ⌝ A ↡ C✦
    → Δ ⊢ ∞ # B ⌞ ≤ ⌝ D ↡ D✦
    → Δ ⊢ ∞ # A `→ B ⌞ ≤ ⌝ C `→ D ↡ C✦ `→ D✦
  s-arr₂ :
      Δ ⊢ ∞ # C ⌞ ≤⁻ ⌝ A ↡ C✦
    → Δ ⊢ j # B ⌞ ≤⁺ ⌝ D ↡ D✦
    → Δ ⊢ 𝕚 j # A `→ B ⌞ ≤⁺ ⌝ C `→ D ↡ C✦ `→ D✦
  s-arr₃ :
      (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊢ j # B ⌞ ≤⁺ ⌝ D ↡ D✦
    → Δ ⊢ 𝕔 j # A `→ B ⌞ ≤⁺ ⌝ A% `→ D ↡ A `→ D✦
  s-∀ :
      Δ ,∙ ⊢ ∞ # A ⌞ ≤ ⌝ B ↡ B✦
    → Δ ⊢ ∞ # `∀ A ⌞ ≤ ⌝ `∀ B ↡ `∀ B✦
  s-∀l :
       Δ ⊢ j # A* ⌞ ≤⁺ ⌝ C `→ D ↡ C✦ -- not ensured as function type
    → (ic : (𝕚𝕔 j))
    → (fd : find A #0 j')
    → (upj : ↑tyʲ0 j ⇘ j')
    → (st : ⟦ B ⟧ A ⇘ A*)
    → (regB : Δ ⊢t B)
    → Δ ⊢ j # `∀ A ⌞ ≤⁺ ⌝ C `→ D ↡ C✦
  s-∀l-no-appear :
      Δ ⊢ j # A* ⌞ ≤⁺ ⌝ C `→ D ↡ C✦
    → (ic : (𝕚𝕔 j))
    → (fd : #0 ¬ε A)
    → (upj : ↑tyʲ0 j ⇘ j')
    → (st : ⟦ B ⟧ A ⇘ A*)
    → (regB : Δ ⊢t B)
    → Δ ⊢ j # `∀ A ⌞ ≤⁺ ⌝ C `→ D  ↡ C✦
  s-tapp :
      Δ ,= B ⊢ j' # A ⌞ ≤⁺ ⌝ C ↡ C✦
    → (upj : ↑tyʲ0 j ⇘ j')
    → Δ ⊢ 𝕥₍ B ₎ j # `∀ A ⌞ ≤⁺ ⌝ `∀ C ↡ `∀ C✦
  s-svar-l : ∀ {X A}
    → (SRegularS Δ)
    → (inΔ : Δ ∋ X := A)
    → Δ ⊢ ∞ # ‶ X ⌞ ≤⁺ ⌝ A ↡ ‶ X
  s-svar-r : ∀ {X A}
    → (SRegularS Δ)
    → (inΔ : Δ ∋ X := A)
    → Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ ‶ X ↡ ‶ X
  s-svar-𝕚 :
      Δ ∋ X := C
    → Δ ⊢ (𝕚 j) # C ⌞ ≤⁺ ⌝ A `→ B ↡ D✦
    → Δ ⊢ (𝕚 j) # ‶ X ⌞ ≤⁺ ⌝ A `→ B ↡ (‶ X)
  s-svar-𝕔 :
      Δ ∋ X := C
    → Δ ⊢ (𝕔 j) # C ⌞ ≤⁺ ⌝ A `→ B ↡ D✦
    → Δ ⊢ (𝕔 j) # ‶ X ⌞ ≤⁺ ⌝ A `→ B ↡ (‶ X)
  s-svar-𝕥 :
      Δ ∋ X := B
    → Δ ⊢ (𝕥₍ A ₎ j) # B ⌞ ≤⁺ ⌝ `∀ C ↡ D✦
    → Δ ⊢ (𝕥₍ A ₎ j) # ‶ X ⌞ ≤⁺ ⌝ `∀ C ↡ (‶ X)

{-
data FunType (A : Type m) : Set where
  justfun : ∀ {B C}
          → A ≡ B `→ C
          → FunType A

ela-destruct-fun : Δ ⊢ j # A* ⌞ ≤⁺ ⌝ C `→ D ↡ A✦
                 → FunType A✦
ela-destruct-fun (s-refl regΔ cloA (grd-var= x)) = {!!}
ela-destruct-fun (s-refl regΔ cloA (grd-arr grd grd₁)) = {!!}
ela-destruct-fun (s-arr₁ s s₁) = justfun refl
ela-destruct-fun (s-arr₂ s s₁) = justfun refl
ela-destruct-fun (s-arr₃ cloA grd s) = justfun refl
ela-destruct-fun (s-∀l s ic fd upj st regB) = ela-destruct-fun s
ela-destruct-fun (s-∀l-no-appear s ic fd upj st regB) = ela-destruct-fun s
ela-destruct-fun (s-svar-l x inΔ) = {!!}
ela-destruct-fun (s-svar-𝕚 x s) = {!!}
ela-destruct-fun (s-svar-𝕔 x s) = {!!}
-}

sound-ela : Δ ⊢ j # A ⌞ ≤ ⌝ B
          → ∃[ B✦ ](Δ ⊢ j # A ⌞ ≤ ⌝ B ↡ B✦)
sound-ela (s-refl {A = A} regΔ cloA grd) = ⟨ A , s-refl regΔ cloA grd ⟩
sound-ela (s-int regΔ) = ⟨ Int , s-int regΔ ⟩
sound-ela (s-var-∙ {X = X} regΔ inΔ) = ⟨ ‶ X , s-var-∙ regΔ inΔ ⟩
sound-ela (s-arr₁ s s₁) = ⟨ sound-ela s .proj₁ `→ sound-ela s₁ .proj₁ ,
                           s-arr₁ (sound-ela s .proj₂) (sound-ela s₁ .proj₂) ⟩
sound-ela (s-arr₂ s s₁) = ⟨ sound-ela s .proj₁ `→ sound-ela s₁ .proj₁ ,
                           s-arr₂ (sound-ela s .proj₂) (sound-ela s₁ .proj₂) ⟩
sound-ela (s-arr₃ {A = A} cloA grd s) = ⟨ A `→ sound-ela s .proj₁ , s-arr₃ cloA grd (sound-ela s .proj₂) ⟩
sound-ela (s-∀ s) = ⟨ `∀ sound-ela s .proj₁ , s-∀ (sound-ela s .proj₂) ⟩
sound-ela (s-∀l s ic fd upj st regB) = ⟨ sound-ela s .proj₁ , s-∀l (sound-ela s .proj₂) ic fd upj st regB ⟩
sound-ela (s-∀l-no-appear s ic fd upj st regB) = ⟨ sound-ela s .proj₁ ,
                                                  s-∀l-no-appear (sound-ela s .proj₂) ic fd upj st regB ⟩
sound-ela (s-tapp s upj) = ⟨ `∀ sound-ela s .proj₁ , s-tapp (sound-ela s .proj₂) upj ⟩
sound-ela (s-svar-l {X = X} x inΔ) = ⟨ ‶ X , s-svar-l x inΔ ⟩
sound-ela (s-svar-r {X = X} x inΔ) = ⟨ ‶ X , s-svar-r x inΔ ⟩
sound-ela (s-svar-𝕚 {X = X} x s) = ⟨ ‶ X , s-svar-𝕚 x (sound-ela s .proj₂) ⟩
-- ⟨ sound-ela s .proj₁ , s-svar-𝕚 x (sound-ela s .proj₂) ⟩
sound-ela (s-svar-𝕔 {X = X} x s) = ⟨ ‶ X , s-svar-𝕔 x (sound-ela s .proj₂) ⟩
-- ⟨ sound-ela s .proj₁ , s-svar-𝕔 x (sound-ela s .proj₂) ⟩
sound-ela (s-svar-𝕥 {X = X} x s) = ⟨ ‶ X , s-svar-𝕥 x (sound-ela s .proj₂) ⟩
-- ⟨ sound-ela s .proj₁ , s-svar-𝕥 x (sound-ela s .proj₂) ⟩
