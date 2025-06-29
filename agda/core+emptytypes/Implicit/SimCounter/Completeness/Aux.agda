module Implicit.SimCounter.Completeness.Aux where

open import Implicit.Language.All
open import Implicit.AuxLemmas
open import Implicit.Interm.All
open import Implicit.SimCounter.Typing
open import Implicit.SimCounter.Subtyping2


-- first we deal with bound variable
data Bound : Env n m → SCounter × Type m → Counter m × Type m → Set where
  bd-z : Bound Γ (⟨ Z , A ⟩) (⟨ Z , A ⟩)
  bd-∞ : Bound Γ (⟨ ∞ , A ⟩) (⟨ ∞ , A ⟩)
  bd-c : Bound Γ (⟨ 𝕟 , B ⟩) (⟨ j , C ⟩)
       → Bound Γ (⟨ 𝕔 𝕟 , A `→ B ⟩) (⟨ 𝕔 j , A `→ C ⟩)
  bd-i : Bound Γ (⟨ 𝕟 , B ⟩) (⟨ j , C ⟩)
       → Bound Γ (⟨ 𝕚 𝕟 , A `→ B ⟩) (⟨ 𝕚 j , A `→ C ⟩)
  bd-t : Bound (Γ ,∙) (⟨ 𝕟 , A ⟩) (⟨ j' , B ⟩)
       → Γ ⊢t T
       → ⟦ T ⟧ B ⇘ A*
       → ↑ty0 A* ⇘ C
       → ↑tyʲ0 j ⇘ j'
       → Bound Γ (⟨ 𝕥 𝕟 , `∀ A ⟩) (⟨ 𝕥₍ T ₎ j , `∀ C ⟩)

data Free : Env n m → Env n m → Set where
  fr-⋈ : Free (Γ ⋈) (Γ ⋈)
  fr-S∙= : Free Γ Δ
        → Δ ⊢t A
        → Free (Γ ,∙) (Δ ,= A)
  fr-S∙ : Free Γ Δ
        → Free (Γ ,∙) (Δ ,∙)
  fr-S= : Free Γ Δ
        → Free (Γ ,= A) (Δ ,= A)

free-wfs : WFS Γ H
         → Free Γ Δ
         → WFS Δ H
free-wfs (wfs-base x) fr-⋈ = wfs-base x
free-wfs (wfs-mis∙ wfs) (fr-S∙= fr x) = wfs-mis= (free-wfs wfs fr)
free-wfs (wfs-mis∙ wfs) (fr-S∙ fr) = wfs-mis∙ (free-wfs wfs fr)
free-wfs (wfs-mis= wfs) (fr-S= fr) = wfs-mis= (free-wfs wfs fr)

free-⊢t : Γ ⊢t A
        → Free Γ Δ
        → Δ ⊢t A
free-⊢t (justts fv-Int wfs) fr = justts fv-Int (free-wfs wfs fr)
free-⊢t (justts fv-var wfs) fr = justts fv-var (free-wfs wfs fr)
free-⊢t (justts (fv-arr fv fv₁ x) wfs) fr = justts (fv-arr fv fv₁ x) (free-wfs wfs fr)
free-⊢t (justts (fv-∀-h fv) wfs) fr = justts (fv-∀-h fv) (free-wfs wfs fr)
free-⊢t (justts (fv-∀-m fv) wfs) fr = justts (fv-∀-m fv) (free-wfs wfs fr)

free-sregulars : SRegularS Γ
               → Free Γ Δ
               → SRegularS Δ
free-sregulars (reg-Z regΓ) fr-⋈ = reg-Z regΓ
free-sregulars (reg-S∙ regΓ) (fr-S∙= fr x) = reg-S= (free-sregulars regΓ fr) x
free-sregulars (reg-S∙ regΓ) (fr-S∙ fr) = reg-S∙ (free-sregulars regΓ fr)
free-sregulars (reg-S= regΓ regA) (fr-S= fr) = reg-S= (free-sregulars regΓ fr) (free-⊢t regA fr)

postulate
  free-⊢c : Γ ⊢c A
        → Free Γ Δ
        → Δ ⊢c A

free-∋:=' : Γ ∋ X := A
         → Free Γ Δ
         → Δ ∋ X := A
free-∋:=' (Z up) (fr-S= fr) = Z up
free-∋:=' (S∙ inΓ up) (fr-S∙= fr x) = S= (free-∋:=' inΓ fr) up
free-∋:=' (S∙ inΓ up) (fr-S∙ fr) = S∙ (free-∋:=' inΓ fr) up
free-∋:=' (S= inΓ up) (fr-S= fr) = S= (free-∋:=' inΓ fr) up


≫-⊢t-eq' : Γ ⊢t A
         → Γ ≫ A ⇘ B
         → A ≡ B
≫-⊢t-eq' (justts x x₁) grd-int = refl
≫-⊢t-eq' (justts fv-var x₁) (grd-var= x₂) = ⊥-elim {!!}
≫-⊢t-eq' (justts x x₁) (grd-var∙ x₂) = refl
≫-⊢t-eq' (justts (fv-arr x x₂ x₃) x₁) (grd-arr grd grd₁) = cong₂ _`→_ (≫-⊢t-eq' (justts x {!!}) grd) {!!}
≫-⊢t-eq' (justts (fv-∀-h x) x₁) (grd-∀ grd) = cong `∀_ (≫-⊢t-eq' (justts x {!!}) grd)
≫-⊢t-eq' (justts (fv-∀-m x) x₁) (grd-∀ grd) = cong `∀_ (≫-⊢t-eq' (justts x (wfs-mis∙ x₁)) grd)
