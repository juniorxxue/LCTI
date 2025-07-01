{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}
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
  bd-t : Bound (Γ ,= T) (⟨ 𝕟 , A ⟩) (⟨ j' , B ⟩)
       → (upj : ↑tyʲ0 j ⇘ j')
       → (regT : Γ ⊢t T)
       → Bound Γ (⟨ 𝕥 𝕟 , `∀ A ⟩) (⟨ 𝕥₍ T ₎ j , `∀ B ⟩)


postulate
  bound-weaken=0 : Bound Γ (⟨ 𝕟 , A ⟩) (⟨ j , B ⟩)
               → Γ ⊢r T
               → ↑tyʲ0 j ⇘ j'
               → ↑ty0 A ⇘ A'
               → ↑ty0 B ⇘ B'
               → Bound (Γ ,= T) (⟨ 𝕟 , A' ⟩) (⟨ j' , B' ⟩)

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





free-∋:=' : Γ ∋ X := A
         → Free Γ Δ
         → Δ ∋ X := A
free-∋:=' (Z up) (fr-S= fr) = Z up
free-∋:=' (S∙ inΓ up) (fr-S∙= fr x) = S= (free-∋:=' inΓ fr) up
free-∋:=' (S∙ inΓ up) (fr-S∙ fr) = S∙ (free-∋:=' inΓ fr) up
free-∋:=' (S= inΓ up) (fr-S= fr) = S= (free-∋:=' inΓ fr) up

free-∋= : Γ ∋= X
         → Free Γ Δ
         → Δ ∋= X
free-∋= Z (fr-S= fr) = Z
free-∋= (S∙ inΓ) (fr-S∙= fr x) = S= (free-∋= inΓ fr)
free-∋= (S∙ inΓ) (fr-S∙ fr) = S∙ (free-∋= inΓ fr)
free-∋= (S= inΓ) (fr-S= fr) = S= (free-∋= inΓ fr)

free-∋∙ : Γ ∋∙ X
         → Free Γ Δ
         → (Δ ∋∙ X) ⊎ (Δ ∋= X)
free-∋∙ Z (fr-S∙= fr x) = inj₂ Z
free-∋∙ Z (fr-S∙ fr) = inj₁ Z
free-∋∙ (S∙ inΓ) (fr-S∙= fr x) with free-∋∙ inΓ fr
... | inj₁ x₁ = inj₁ (S= x₁)
... | inj₂ y = inj₂ (S= y)
free-∋∙ (S∙ inΓ) (fr-S∙ fr) with free-∋∙ inΓ fr
... | inj₁ x = inj₁ (S∙ x)
... | inj₂ y = inj₂ (S∙ y)
free-∋∙ (S= inΓ) (fr-S= fr) with free-∋∙ inΓ fr
... | inj₁ x = inj₁ (S= x)
... | inj₂ y = inj₂ (S= y)
free-∋∙ (S⋈ inΓ) fr-⋈ = inj₁ (S⋈ inΓ)

wfs-wfr : WFS Γ H
        → WFR Γ H
wfs-wfr (wfs-base x) = wfr-base x
wfs-wfr (wfs-mis∙ wfs) = wfr-mis∙ (wfs-wfr wfs)
wfs-wfr (wfs-mis= wfs) = wfr-mis= (wfs-wfr wfs)
wfs-wfr (wfs-mis^ wfs) = wfr-mis^ (wfs-wfr wfs)

⊢t-⊢r' : Γ ⊢t A
       → Γ ⊢r' A
⊢t-⊢r' (justts x x₁) = justrs x (wfs-wfr x₁)

wft-∋∙ : WFT Γ (mkHit X)
       → Γ ∋∙ X
wft-∋∙ {X = #0} (wft-hit wft) = Z
wft-∋∙ {X = #0} (wft-, wft) = S, (wft-∋∙ wft)
wft-∋∙ {X = #S X} (wft-mis∙ wft) = S∙ (wft-∋∙ wft)
wft-∋∙ {X = #S X} (wft-mis= wft) = S= (wft-∋∙ wft)
wft-∋∙ {X = #S X} (wft-mis^ wft) = S^ (wft-∋∙ wft)
wft-∋∙ {X = #S X} (wft-, wft) = S, (wft-∋∙ wft)

wfr-∋∙ : WFR Γ (mkHit X)
       → Γ ∋∙ X
wfr-∋∙ {X = #0} (wfr-base x) = S⋈ (wft-∋∙ x)
wfr-∋∙ {X = #0} (wfr-hit wfr) = Z
wfr-∋∙ {X = #S X} (wfr-base {Γ = Γ} x) = S⋈ (wft-∋∙ x)
wfr-∋∙ {X = #S X} (wfr-mis∙ wfr) = S∙ (wfr-∋∙ wfr)
wfr-∋∙ {X = #S X} (wfr-mis= wfr) = S= (wfr-∋∙ wfr)
wfr-∋∙ {X = #S X} (wfr-mis^ wfr) = S^ (wfr-∋∙ wfr)

wft-or-l : WFT Γ H
         → orHit H₁ H₂ H
         → WFT Γ H₁
wft-or-l wft-base Z = wft-base
wft-or-l (wft-hit wft) (S-hm orh) = wft-hit (wft-or-l wft orh)
wft-or-l (wft-hit wft) (S-mh orh) = wft-mis∙ (wft-or-l wft orh)
wft-or-l (wft-hit wft) (S-hh orh) = wft-hit (wft-or-l wft orh)
wft-or-l (wft-mis∙ wft) (s-mm orh) = wft-mis∙ (wft-or-l wft orh)
wft-or-l (wft-mis= wft) (s-mm orh) = wft-mis= (wft-or-l wft orh)
wft-or-l (wft-mis^ wft) (s-mm orh) = wft-mis^ (wft-or-l wft orh)
wft-or-l (wft-, wft) orh = wft-, (wft-or-l wft orh)


wfr-or-l : WFR Γ H
         → orHit H₁ H₂ H
         → WFR Γ H₁
wfr-or-l wfr Z = wfr
wfr-or-l (wfr-base x) (S-hm or) = wfr-base (wft-or-l x (S-hh or))
wfr-or-l (wfr-hit wfr) (S-hm or) = wfr-hit (wfr-or-l wfr or)
wfr-or-l (wfr-base x) (S-mh or) = wfr-base (wft-or-l x (S-mh or))
wfr-or-l (wfr-hit wfr) (S-mh or) = wfr-mis∙ (wfr-or-l wfr or)
wfr-or-l (wfr-base x) (S-hh or) = wfr-base (wft-or-l x (S-hh or))
wfr-or-l (wfr-hit wfr) (S-hh or) = wfr-hit (wfr-or-l wfr or)
wfr-or-l (wfr-base x) (s-mm or) = wfr-base (wft-or-l x (s-mm or))
wfr-or-l (wfr-mis∙ wfr) (s-mm or) = wfr-mis∙ (wfr-or-l wfr or)
wfr-or-l (wfr-mis= wfr) (s-mm or) = wfr-mis= (wfr-or-l wfr or)
wfr-or-l (wfr-mis^ wfr) (s-mm or) = wfr-mis^ (wfr-or-l wfr or)

wft-or-r : WFT Γ H
         → orHit H₁ H₂ H
         → WFT Γ H₂
wft-or-r wft-base Z = wft-base
wft-or-r (wft-hit wft) (S-hm orh) = wft-mis∙ (wft-or-r wft orh)
wft-or-r (wft-hit wft) (S-mh orh) = wft-hit (wft-or-r wft orh)
wft-or-r (wft-hit wft) (S-hh orh) = wft-hit (wft-or-r wft orh)
wft-or-r (wft-mis∙ wft) (s-mm orh) = wft-mis∙ (wft-or-r wft orh)
wft-or-r (wft-mis= wft) (s-mm orh) = wft-mis= (wft-or-r wft orh)
wft-or-r (wft-mis^ wft) (s-mm orh) = wft-mis^ (wft-or-r wft orh)
wft-or-r (wft-, wft) orh = wft-, (wft-or-r wft orh)

wfr-or-r : WFR Γ H
         → orHit H₁ H₂ H
         → WFR Γ H₂
wfr-or-r (wfr-base x) or = wfr-base (wft-or-r x or)
wfr-or-r (wfr-hit wfr) (S-hm or) = wfr-mis∙ (wfr-or-r wfr or)
wfr-or-r (wfr-hit wfr) (S-mh or) = wfr-hit (wfr-or-r wfr or)
wfr-or-r (wfr-hit wfr) (S-hh or) = wfr-hit (wfr-or-r wfr or)
wfr-or-r (wfr-mis∙ wfr) (s-mm or) = wfr-mis∙ (wfr-or-r wfr or)
wfr-or-r (wfr-mis= wfr) (s-mm or) = wfr-mis= (wfr-or-r wfr or)
wfr-or-r (wfr-mis^ wfr) (s-mm or) = wfr-mis^ (wfr-or-r wfr or)

⊢r'⊢r : Γ ⊢r' A
      → Γ ⊢r A
⊢r'⊢r (justrs fv-Int x₁) = ⊢r-int
⊢r'⊢r (justrs fv-var x₁) = ⊢r-var-∙ (wfr-∋∙ x₁)
⊢r'⊢r (justrs (fv-arr x x₂ x₃) x₁) = ⊢r-arr (⊢r'⊢r (justrs x (wfr-or-l x₁ x₃))) (⊢r'⊢r (justrs x₂ (wfr-or-r x₁ x₃)))
⊢r'⊢r (justrs (fv-∀-h x) x₁) = ⊢r-∀ (⊢r'⊢r (justrs x (wfr-hit x₁)))
⊢r'⊢r (justrs (fv-∀-m x) x₁) = ⊢r-∀ (⊢r'⊢r (justrs x (wfr-mis∙ x₁)))

⊢t-⊢r : Γ ⊢t A
      → Γ ⊢r A
⊢t-⊢r regA = ⊢r'⊢r (⊢t-⊢r' regA)


≫-⊢t-eq' : Γ ⊢t A
         → Γ ≫ A ⇘ B
         → A ≡ B
≫-⊢t-eq' regA grd = ⊢r-≫-eq' (⊢t-⊢r regA) grd

tregulars-tregular : TRegularS Γ
                   → TRegular Γ
tregulars-tregular reg-Z = reg-Z
tregulars-tregular (reg-S, regΓ regA) = reg-S, (tregulars-tregular regΓ) (⊢t-⊢r regA)
tregulars-tregular (reg-S∙ regΓ) = reg-S∙ (tregulars-tregular regΓ)
tregulars-tregular (reg-S^ regΓ) = reg-S^ (tregulars-tregular regΓ)
tregulars-tregular (reg-S= regΓ regA) = reg-S= (tregulars-tregular regΓ) (⊢t-⊢r regA)

sregulars-sregular : SRegularS Γ
                   → SRegular Γ
sregulars-sregular (reg-Z regΓ) = reg-Z (tregulars-tregular regΓ)
sregulars-sregular (reg-S∙ regΓ) = reg-S∙ (sregulars-sregular regΓ)
sregulars-sregular (reg-S^ regΓ) = reg-S^ (sregulars-sregular regΓ)
sregulars-sregular (reg-S= regΓ regA) = reg-S= (sregulars-sregular regΓ) (⊢t-⊢r regA)


free-sregular : SRegularS Γ
              → Free Γ Δ
              → SRegular Δ
free-sregular regΓ fr = sregulars-sregular (free-sregulars regΓ fr)


free-⊢c : Γ ⊢c A
        → Free Γ Δ
        → Δ ⊢c A
free-⊢c ⊢c-int fr = ⊢c-int
free-⊢c (⊢c-var-∙ inΔ) fr with free-∋∙ inΔ fr
... | inj₁ x = ⊢c-var-∙ x
... | inj₂ y = ⊢c-var-= y
free-⊢c (⊢c-var-= inΔ) fr = ⊢c-var-= (free-∋= inΔ fr)
free-⊢c (⊢c-arr cloA cloA₁) fr = ⊢c-arr (free-⊢c cloA fr) (free-⊢c cloA₁ fr)
free-⊢c (⊢c-∀ cloA) fr = ⊢c-∀ (free-⊢c cloA (fr-S∙ fr))

{-
⊢c-≫-⊢t : SRegularS Γ
        → Γ ⊢c A
        → Γ ≫ A ⇘ B
        → Γ ⊢t A
⊢c-≫-⊢t regΓ ⊢c-int grd = justts fv-Int {!!}
⊢c-≫-⊢t regΓ (⊢c-var-∙ inΔ) (grd-var= x) = ⊥-elim (∋∙-∋:=-false inΔ x)
⊢c-≫-⊢t regΓ (⊢c-var-∙ inΔ) (grd-var∙ x) = justts fv-var {!!}
⊢c-≫-⊢t regΓ (⊢c-var-= inΔ) grd = {!!}
⊢c-≫-⊢t regΓ (⊢c-arr cloA cloA₁) grd = {!!}
⊢c-≫-⊢t regΓ (⊢c-∀ cloA) (grd-∀ grd) = {!!}
-}

postulate
  𝕗𝕧-↑ty0 : A 𝕗𝕧 H
        → ↑ty0 A ⇘ A'
        → A' 𝕗𝕧 mis H


∋:=-⊢t : SRegularS Γ
       → Γ ∋ X := A
       → Γ ⊢t A
∋:=-⊢t (reg-S∙ regΓ) (S∙ inΓ up) with ∋:=-⊢t regΓ inΓ
... | justts x x₁ = justts (𝕗𝕧-↑ty0 x up) (wfs-mis∙ x₁)
∋:=-⊢t (reg-S^ regΓ) (S^ inΓ up) with ∋:=-⊢t regΓ inΓ
... | justts x x₁ = justts (𝕗𝕧-↑ty0 x up) (wfs-mis^ x₁)
∋:=-⊢t (reg-S= regΓ (justts x x₁)) (Z up) = justts (𝕗𝕧-↑ty0 x up) (wfs-mis= x₁)
∋:=-⊢t (reg-S= regΓ regA) (S= inΓ up) with ∋:=-⊢t regΓ inΓ
... | justts x x₁ = justts (𝕗𝕧-↑ty0 x up) (wfs-mis= x₁)


free-≫ : SRegularS Γ
       → Γ ≫ A ⇘ B
       → Free Γ Δ
       → Δ ≫ B ⇘ C
       → Δ ≫ A ⇘ C
free-≫ regΓ grd-int fr grd-int = grd-int
free-≫ regΓ (grd-var= x) fr grd2
  with regB ← (∋:=-⊢t regΓ x)
  with regB' ← ⊢t-⊢r (free-⊢t regB fr)
  with refl ← ⊢r-≫-eq' regB' grd2 = grd-var= (free-∋:=' x fr)
free-≫ regΓ (grd-var∙ x) fr (grd-var= x₁) = grd-var= x₁
free-≫ regΓ (grd-var∙ x) fr (grd-var∙ x₁) = grd-var∙ x₁
free-≫ regΓ (grd-arr grd1 grd3) fr (grd-arr grd2 grd4) = grd-arr (free-≫ regΓ grd1 fr grd2) (free-≫ regΓ grd3 fr grd4)
free-≫ regΓ (grd-∀ grd1) fr (grd-∀ grd2) = grd-∀ (free-≫ (reg-S∙ regΓ) grd1 (fr-S∙ fr) grd2)


sisoinf-isoinf : SIsoInf 𝕟
               → Bound Γ (⟨ 𝕟 , B ⟩) (⟨ j , C ⟩)
               → IsoInf j
sisoinf-isoinf i∞-z (bd-i bd-∞) = i∞-z
sisoinf-isoinf (i∞-i iso) (bd-i bd) = i∞-i (sisoinf-isoinf iso bd)


sfind-find : Sfind A k 𝕟
           → Bound Γ (⟨ 𝕟 , B ⟩) (⟨ j , C ⟩)
           → find A k j
sfind-find (f-∞ inA) bd-∞ = f-∞ inA
sfind-find (f-iso iso) (bd-i bd) = f-iso (sisoinf-isoinf iso (bd-i {A = Int} bd))
sfind-find (f-arr-𝕚-l inA) (bd-i bd) = f-arr-𝕚-l inA
sfind-find (f-arr-𝕚-r ¬inA fd) (bd-i bd) = f-arr-𝕚-r ¬inA (sfind-find fd bd)
sfind-find (f-arr-𝕔 ¬inA fd) (bd-c bd) = f-arr-𝕔 ¬inA (sfind-find fd bd)
sfind-find (f-∀-𝕚 fd) (bd-i {B = B} {j = j} {C = C} bd)
  with ⟨ j' , upj  ⟩ ← ↑tyʲ0-total j
  with ⟨ C' , upC ⟩ ← ↑ty0-total C
  with ⟨ B' , upB ⟩ ← ↑ty0-total B = f-∀-𝕚 (sfind-find fd (bd-i {A = Int} (bound-weaken=0 bd ⊢r-int upj upB upC))) upj
sfind-find (f-∀-𝕔 fd) (bd-c {B = B} {j = j} {C = C} bd)
  with ⟨ j' , upj  ⟩ ← ↑tyʲ0-total j
  with ⟨ C' , upC ⟩ ← ↑ty0-total C
  with ⟨ B' , upB ⟩ ← ↑ty0-total B = f-∀-𝕔 (sfind-find fd (bd-c {A = Int} (bound-weaken=0 bd ⊢r-int upj upB upC))) upj
sfind-find (f-𝕥 fd) bd = {!!}

bound-⊢r : Bound Γ (⟨ 𝕟 , A ⟩) (⟨ j , B ⟩)
         → Γ ⊢r A
         → Γ ⊢r B
bound-⊢r bd-z regA = regA
bound-⊢r bd-∞ regA = regA
bound-⊢r (bd-c bd) (⊢r-arr regA regA₁) = ⊢r-arr regA (bound-⊢r bd regA₁)
bound-⊢r (bd-i bd) (⊢r-arr regA regA₁) = ⊢r-arr regA (bound-⊢r bd regA₁)
bound-⊢r (bd-t bd x₂ regT) (⊢r-∀ regA) = {!!}
-- ⊢r-∀ (⊢r-weaken∙0 (st0-⊢r (⊢r-∀ (bound-⊢r bd regA)) (⊢t-⊢r x) x₁) x₂)
