module Implicit.SimCounter.Completeness where

open import Implicit.Language.All
open import Implicit.Decl.Typing
open import Implicit.Decl.SubtypingV2
open import Implicit.SimCounter.Typing
open import Implicit.SimCounter.Subtyping

{-
infix 3 _⊢_#_≤_⟿_#_≤_
data _⊢_#_≤_⟿_#_≤_ : Env n m → Counter m → Type m → Type m → SCounter → Type m → Type m → Set where
  s-refl :
      (regΔ : SRegular Δ)
    → (cloA : Δ ⊢r A)
    → Δ ⊢ Z # A ≤ A ⟿ Z # A ≤ A
  s-int :
      (regΔ : SRegular Δ)
    → Δ ⊢ ∞ # Int ≤ Int ⟿ ∞ # Int ≤ Int
  s-var-∙ :
      (regΔ : SRegular Δ)
    → (inΔ : Δ ∋∙ X)
    → Δ ⊢ ∞ # ‶ X ≤ ‶ X ⟿ ∞ # ‶ X ≤ ‶ X
  s-arr₁ :
      Δ ⊢ ∞ # C ≤ A ⟿ ∞ # C ≤ A
    → Δ ⊢ ∞ # B ≤ D ⟿ ∞ # B ≤ D
    → Δ ⊢ ∞ # A `→ B ≤ C `→ D ⟿ ∞ # A `→ B ≤ C `→ D
  s-arr₂ :
      Δ ⊢ ∞ # C ≤ A ⟿ ∞ # C₁ ≤ A₁
    → Δ ⊢ j # B ≤ D ⟿ 𝕟 # B₁ ≤ D₁
    → Δ ⊢ 𝕚 j # A `→ B ≤ C `→ D ⟿ 𝕚 𝕟 # A₁ `→ B₁ ≤ C₁ `→ D₁
  s-arr₃ :
      (regA : Δ ⊢r A)
    → Δ ⊢ j # B ≤ D ⟿ 𝕟 # B₁ ≤ D₁
    → Δ ⊢ 𝕔 j # A `→ B ≤ A `→ D ⟿ 𝕔 𝕟 # A₁ `→ B₁ ≤ A₁ `→ D₁
  s-∀ :
      Δ ,∙ ⊢ ∞ # A ≤ B ⟿ ∞ # A ≤ B
    → Δ ⊢ ∞ # `∀ A ≤ `∀ B ⟿ ∞ # `∀ A ≤ `∀ B
  s-∀l :
      (regB : Γ ⊢r B)
    → (st : ⟦ B ⟧ A ⇘ A*)
    → Γ ⊢ j # A* ≤ C `→ D ⟿ 𝕟 # A*₁ ≤ C₁ `→ D₁
    → (ic : (𝕚𝕔 j))
    → (fd : find A #0 j')
    → (upj : ↑tyʲ0 j ⇘ j')
    → Γ ⊢ j # `∀ A ≤ C `→ D ⟿ 𝕟 # `∀ A
  s-∀l-no-appear :
      (regB : Γ ⊢r B)
    → (st : ⟦ B ⟧ A ⇘ A*)
    → Γ ⊢ j # A* ≤ C `→ D
    → (ic : (𝕚𝕔 j))
    → (fd : #0 ¬ε A)
    → Γ ⊢ j # `∀ A ≤ C `→ D
  s-tapp :
      (Δ ,= B) ≫ A ⇘ A%
    → (Δ ,= B) ≫ C ⇘ C%
    → (regA : Δ ,∙ ⊢r A)
    → Δ ,∙ ⊢ j' # A% ≤ C%
    → (upj : ↑tyʲ0 j ⇘ j')
    → Δ ⊢ 𝕥₍ B ₎ j # `∀ A ≤ `∀ C
-}



infix 3 _R_
data _R_ : Counter m × Type m → SCounter × Type m → Set where
  R-Z : ⟨ Z , A ⟩ R ⟨ Z , A ⟩
  R-∞ : ⟨ ∞ , A ⟩ R ⟨ ∞ , A ⟩
  R-𝕚 : ⟨ j , B ⟩ R ⟨ 𝕟 , C ⟩
      → ⟨ 𝕚 j , A `→ B ⟩ R ⟨ 𝕚 𝕟 , A `→ C ⟩
  R-𝕔 : ⟨ j , B ⟩ R ⟨ 𝕟 , C ⟩
      → ⟨ 𝕔 j , A `→ B ⟩ R ⟨ 𝕔 𝕟 , A `→ C ⟩
  R-𝕥 : ⟨ j , A ⟩ R ⟨ 𝕟 , B* ⟩
      → ⟦ T ⟧ B ⇘ B*
      → (upA : ↑ty0 A ⇘ A')
      → ⟨ 𝕥₍ T ₎ j , `∀ A' ⟩ R ⟨ 𝕥 𝕟 , `∀ B ⟩

infix 3 _⊢⟦_,_,_⟧R⟦_,_,_⟧
data _⊢⟦_,_,_⟧R⟦_,_,_⟧ : Env n m → SCounter → Type m → Type m → Counter m → Type m → Type m → Set where
  R-Z : Γ ⊢⟦ Z , A , A ⟧R⟦ Z , A , A ⟧
  R-∞ : Γ ⊢⟦ ∞ , A , A ⟧R⟦ ∞ , A , A ⟧
  R-𝕚 : Γ ⊢⟦ 𝕟 , A , B ⟧R⟦ j , C , D ⟧
      → Γ ⊢⟦ 𝕚 𝕟 , T `→ A , T `→ B ⟧R⟦ 𝕚 j , T `→ C , T `→ D ⟧
  R-𝕔 : Γ ⊢⟦ 𝕟 , A , B ⟧R⟦ j , C , D ⟧
      → Γ ⊢⟦ 𝕔 𝕟 , T `→ A , T `→ B ⟧R⟦ 𝕔 j , T `→ C , T `→ D ⟧
  R-∀-𝕚 : Γ ⊢⟦ 𝕚 𝕟 , A* , B₁ `→ B₂ ⟧R⟦ 𝕚 j , C* , D₁ `→ D₂ ⟧
        → ⟦ T ⟧ A ⇘ A*
        → ⟦ T ⟧ C ⇘ C*
        → Γ ⊢⟦ 𝕚 𝕟 , `∀ A , B₁ `→ B₂ ⟧R⟦ 𝕚 j , `∀ C , D₁ `→ D₂ ⟧
  R-∀-𝕔 : Γ ⊢⟦ 𝕔 𝕟 , A* , B₁ `→ B₂ ⟧R⟦ 𝕔 j , C* , D₁ `→ D₂ ⟧
        → ⟦ T ⟧ A ⇘ A*
        → ⟦ T ⟧ C ⇘ C*
        → Γ ⊢⟦ 𝕔 𝕟 , `∀ A , B₁ `→ B₂ ⟧R⟦ 𝕔 j , `∀ C , D₁ `→ D₂ ⟧
  R-𝕥 : Γ ,∙ ⊢⟦ 𝕟 , A , B ⟧R⟦ j' , C* , D* ⟧
      → (grdC : Γ ,= T ≫ C ⇘ C*)
      → (grdD : Γ ,= T ≫ D ⇘ D*)
      → (upj : ↑tyʲ0 j ⇘ j')
      → Γ ⊢⟦ 𝕥 𝕟 , `∀ A , `∀ B ⟧R⟦ 𝕥₍ T ₎ j , `∀ C , `∀ D ⟧

new→old-s' : Γ ⊨ 𝕟 # A ≤ B
          → Γ ⊢⟦ 𝕟 , A , B ⟧R⟦ j , C , D ⟧
          → Γ ⊢ j # C ≤ D
new→old-s' (s-refl regΔ cloA) rr = {!!}
new→old-s' (s-int regΔ) rr = {!!}
new→old-s' (s-var-∙ regΔ inΔ) rr = {!!}
new→old-s' (s-arr₁ s s₁) rr = {!!}
new→old-s' (s-arr₂ s s₁) rr = {!!}
new→old-s' (s-arr₃ regA s) rr = {!!}
new→old-s' (s-∀ s) rr = {!!}
new→old-s' (s-∀l regB st s ic fd) (R-∀-𝕚 rr x x₁) = {!!}
new→old-s' (s-∀l regB st s ic fd) (R-∀-𝕔 rr x x₁) = {!!}
new→old-s' (s-∀l-no-appear regB st s ic fd) rr = {!!}
new→old-s' (s-tapp s) rr = {!!}

-- new→old-s : Γ ⊨ 𝕟 # A ≤ C
--           → ⟨ j , B ⟩ R ⟨ 𝕟 , C ⟩
--           → Γ ⊢ j # A ≤ B
-- new→old-s (s-refl regΔ cloA) R-Z = s-refl regΔ cloA
-- new→old-s (s-int regΔ) R-∞ = s-int regΔ
-- new→old-s (s-var-∙ regΔ inΔ) R-∞ = s-var-∙ regΔ inΔ
-- new→old-s (s-arr₁ s s₁) R-∞ = s-arr₁ (new→old-s s R-∞) (new→old-s s₁ R-∞)
-- new→old-s (s-arr₂ s s₁) (R-𝕚 rr) = s-arr₂ (new→old-s s R-∞) (new→old-s s₁ rr)
-- new→old-s (s-arr₃ regA s) (R-𝕔 rr) = s-arr₃ regA (new→old-s s rr)
-- new→old-s (s-∀ s) R-∞ = s-∀ (new→old-s s R-∞)
-- new→old-s (s-∀l regB st s ic fd) rr = {!!}
-- new→old-s (s-∀l-no-appear regB st s ic fd) rr = {!!}
-- new→old-s (s-tapp s) (R-𝕥 rr x upA) = s-tapp {!!} {!!} {!new→old-s s!} {!!}


-- new→old : Γ ⊨ 𝕟 # e ⦂ B
--         → ⟨ j , A ⟩ R ⟨ 𝕟 , B ⟩
--         → Γ ⊢ j # e ⦂ A
-- new→old (⊨lit regΓ) R-Z = ⊢lit regΓ
-- new→old (⊨var regΓ x∈Γ) R-Z = ⊢var regΓ x∈Γ
-- new→old (⊨ann ⊢e) R-Z = ⊢ann (new→old ⊢e R-∞)
-- new→old (⊨lam₁ ⊢e) R-∞ = ⊢lam₁ (new→old ⊢e R-∞)
-- new→old (⊨lam₂ ⊢e) (R-𝕚 rr) = ⊢lam₂ (new→old ⊢e rr)
-- new→old (⊨app₁ ⊢e ⊢e₁) rr = ⊢app₁ (new→old ⊢e (R-𝕔 rr)) (new→old ⊢e₁ R-∞)
-- new→old (⊨app₂ ⊢e ⊢e₁) rr = ⊢app₂ (new→old ⊢e (R-𝕚 rr)) (new→old ⊢e₁ R-Z)
-- new→old (⊨sub ⊢e B≤A gc 𝕟≢Z) rr = ⊢sub (new→old ⊢e R-Z) {!!} gc {!!}
-- new→old (⊨tabs ⊢e) R-Z = ⊢tabs (new→old ⊢e R-Z)
-- new→old {A = A} (⊨tapp ⊢e st) rr
--   with ⟨ A' , upA ⟩ ← ↑ty0-total A = ⊢tapp (new→old ⊢e (R-𝕥 rr st upA)) (↑ty-st upA)
