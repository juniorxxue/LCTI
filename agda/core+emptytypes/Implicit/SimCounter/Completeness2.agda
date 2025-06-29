module Implicit.SimCounter.Completeness2 where

open import Implicit.Language.All
open import Implicit.AuxLemmas
open import Implicit.Interm.All
open import Implicit.SimCounter.Typing
open import Implicit.SimCounter.Subtyping2

-- first we deal with bound variable
data Bound : SCounter × Type m → Counter m × Type m → Set where
  bd-z : Bound (⟨ Z , A ⟩) (⟨ Z , A ⟩)
  bd-∞ : Bound (⟨ ∞ , A ⟩) (⟨ ∞ , A ⟩)
  bd-c : Bound (⟨ 𝕟 , B ⟩) (⟨ j , C ⟩)
       → Bound (⟨ 𝕔 𝕟 , A `→ B ⟩) (⟨ 𝕔 j , A `→ C ⟩)
  bd-i : Bound (⟨ 𝕟 , B ⟩) (⟨ j , C ⟩)
       → Bound (⟨ 𝕚 𝕟 , A `→ B ⟩) (⟨ 𝕚 j , A `→ C ⟩)
  bd-t : Bound (⟨ 𝕟 , A ⟩) (⟨ j' , B ⟩)
       → Γ ⊢r T
       → ⟦ T ⟧ B ⇘ A*
       → ↑ty0 A* ⇘ C
       → ↑tyʲ0 j ⇘ j'
       → Bound (⟨ 𝕥 𝕟 , `∀ A ⟩) (⟨ 𝕥₍ T ₎ j , `∀ C ⟩)


data WFT : Env n m → HitMis m → Set where
  wft-base : WFT ∅ ∅
  wft-hit  : WFT Γ H
           → WFT (Γ ,∙) (hit H)
  wft-mis∙ : WFT Γ H
           → WFT (Γ ,∙) (mis H)
  wft-mis= : WFT Γ H
           → WFT (Γ ,= A) (mis H)
  wft-mis^ : WFT Γ H
           → WFT (Γ ,^) (mis H)
  wft-,   : WFT Γ H
           → WFT (Γ , A) H

data WFS : Env n m → HitMis m → Set where
  wfs-base : WFT Γ H
           → WFS (Γ ⋈) H
  wfs-mis∙ : WFS Γ H
           → WFS (Γ ,∙) (mis H)
  wfs-mis= : WFS Γ H
           → WFS (Γ ,= A) (mis H)
  wfs-mis^ : WFS Γ H
           → WFS (Γ ,^) (mis H)


infix 3 _⊢t_
data _⊢t_ (Γ : Env n m) (A : Type m) : Set where
  justts : ∀ {H}
         → A 𝕗𝕧 H
         → WFS Γ H
         → Γ ⊢t A

data Free : Env n m → Env n m → Set where
  fr-⋈ : Free (Γ ⋈) (Γ ⋈)
  fr-S∙= : Free Γ Δ
        → Δ ⊢r A
        → Free (Γ ,∙) (Δ ,= A)
  fr-S∙ : Free Γ Δ
        → Free (Γ ,∙) (Δ ,∙)
  fr-S= : Free Γ Δ
        → Free (Γ ,= A) (Δ ,= A)


free-wfs-mkMis : ∀ {m} {Γ Δ : Env n m}
               → WFS Γ (mkMis {m})
               → Free Γ Δ
               → WFS Δ (mkMis {m})
free-wfs-mkMis (wfs-base x) fr-⋈ = wfs-base x
free-wfs-mkMis (wfs-mis∙ wfs) (fr-S∙= fr x) = wfs-mis= (free-wfs-mkMis wfs fr)
free-wfs-mkMis (wfs-mis∙ wfs) (fr-S∙ fr) = wfs-mis∙ (free-wfs-mkMis wfs fr)
free-wfs-mkMis (wfs-mis= wfs) (fr-S= fr) = wfs-mis= (free-wfs-mkMis wfs fr)

free-wfs-mkHit : WFS Γ (mkHit X)
               → Free Γ Δ
               → WFS Δ (mkHit X)
free-wfs-mkHit (wfs-base x) fr-⋈ = wfs-base x
free-wfs-mkHit {X = #S X} (wfs-mis∙ wfs) (fr-S∙= fr x) = wfs-mis= (free-wfs-mkHit wfs fr)
free-wfs-mkHit {X = #S X} (wfs-mis∙ wfs) (fr-S∙ fr) = wfs-mis∙ (free-wfs-mkHit wfs fr)
free-wfs-mkHit {X = #S X} (wfs-mis= wfs) (fr-S= fr) = wfs-mis= (free-wfs-mkHit wfs fr)

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


free-≫-⊢c : Γ ≫ A ⇘ B
          → Γ ⊢c A
          → Free Γ Δ
          → Δ ≫ A ⇘ B


complete : Γ ⊨ 𝕟 # A ⌞ ≤⁺ ⌝ B
         → Bound (⟨ 𝕟 , B ⟩) (⟨ j , C ⟩)
         → Free Γ Δ
         → Δ ≫ C ⇘ D
         → Δ ⊢ j # A ⌞ ≤⁺ ⌝ D

complete- : Γ ⊨ ∞ # A ⌞ ≤⁻ ⌝ B
         → Free Γ Δ
         → Δ ≫ A ⇘ C
         → Δ ⊢ ∞ # C ⌞ ≤⁻ ⌝ B

complete (s-refl regΔ cloA grd₁) bd-z fr grd
  with regB ← ⊢c-≫-⊢r regΔ cloA grd₁
  = s-refl ? (free-⊢c cloA fr) {!!}
  -- (free-≫-⊢c grd₁ cloA fr)
complete (s-int regΔ) bd-∞ fr grd-int = s-int ?
complete (s-var-∙ regΔ inΔ) bd-∞ fr (grd-var= x) = s-svar-l ? ?
complete (s-var-∙ regΔ inΔ) bd-∞ fr (grd-var∙ x) = s-var-∙  ? ?
complete (s-arr₁ s s₁) bd-∞ fr (grd-arr grd grd₁) = s-arr₁ (complete- s fr grd) (complete s₁ bd-∞ fr grd₁)
complete (s-arr₂ s s₁) (bd-i bd) fr (grd-arr grd grd₁) = s-arr₂ (complete- s fr grd) (complete s₁ bd fr grd₁)
complete (s-arr₃ cloA grd₁ s) (bd-c bd) fr (grd-arr grd grd₂)
  with regA% ← ⊢c-≫-⊢r {!!} cloA grd₁
  = s-arr₃ (free-⊢c cloA fr) {!!} (complete s bd fr grd₂)
complete (s-∀ s) bd-∞ fr (grd-∀ grd) = s-∀ (complete s bd-∞ (fr-S∙ fr) grd)
complete (s-∀l s ic fd upC upD) (bd-c bd) fr (grd-arr grd grd₁) = s-∀l (complete s {!!} (fr-S= fr) {!!}) case-𝕔 {!!} {!!} {!!} {!!}
complete (s-∀l s ic fd upC upD) (bd-i bd) fr grd = {!!}
complete (s-tapp s) (bd-t bd regT x x₁ x₂) fr (grd-∀ grd) = s-tapp (complete s bd (fr-S∙= fr {!!}) {!!}) x₂
complete (s-svar-l x inΔ) bd-∞ fr grd
  = ?
complete (s-svar-𝕚 x s) (bd-i bd) fr (grd-arr grd grd₁) = {!!}
-- s-svar-𝕚 (free-∋:= {!!} x fr {!!}) (complete s (bd-i bd) fr (grd-arr grd grd₁))
-- s-svar-𝕚 (free-∋:= x fr) (complete s (bd-i bd) fr (grd-arr grd grd₁))
complete (s-svar-𝕔 x s) (bd-c bd) fr (grd-arr grd grd₁) = {!!}
-- s-svar-𝕔 (free-∋:= x fr) (complete s (bd-c bd) fr (grd-arr grd grd₁))
complete (s-svar-𝕥 x s) (bd-t bd x₁ x₂ x₃ x₄) fr (grd-∀ grd) = {!!}
-- s-svar-𝕥 (free-∋:= x fr) (complete s (bd-t bd x₁ x₂ x₃ x₄) fr (grd-∀ grd))

complete- (s-int regΔ) fr grd-int = ?
complete- (s-var-∙ regΔ inΔ) fr (grd-var= x) = ?
complete- (s-var-∙ regΔ inΔ) fr (grd-var∙ x) = ?
complete- (s-arr₁ s s₁) fr (grd-arr grd grd₁) = s-arr₁ (complete s bd-∞ fr grd) (complete- s₁ fr grd₁)
complete- (s-∀ s) fr (grd-∀ grd) = s-∀ (complete- s (fr-S∙ fr) grd)
complete- (s-svar-r x inΔ) fr grd
   = ?
