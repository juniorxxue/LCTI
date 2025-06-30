module Implicit.SimCounter.Subtyping2 where

open import Implicit.Language.All
open import Implicit.AuxLemmas

data SCounter : Set where
  Z : SCounter
  ∞ : SCounter
  𝕚 : SCounter → SCounter
  𝕔 : SCounter → SCounter
  𝕥 : SCounter → SCounter

variable
  𝕟 : SCounter

data SNonZ : SCounter → Set where
  nz-∞ : SNonZ  ∞
  nz-I : SNonZ (𝕚 𝕟)
  nz-C : SNonZ (𝕔 𝕟)
  nz-T : SNonZ (𝕥 𝕟)

data S𝕚𝕔 : SCounter → Set where
  case-𝕚 : S𝕚𝕔 (𝕚 𝕟)
  case-𝕔 : S𝕚𝕔 (𝕔 𝕟)

data SIsoInf : SCounter → Set where
  i∞-z : SIsoInf (𝕚 ∞)
  i∞-i : SIsoInf 𝕟
       → SIsoInf (𝕚 𝕟)

data Sfind : Type m → Fin m → SCounter → Set where
  f-∞       : k ε A
            → Sfind A k ∞
  f-iso     : (iso : SIsoInf 𝕟)
            → Sfind (‶ k) k 𝕟
  f-arr-𝕚-l : (inA : k ε A)
            → Sfind (A `→ B) k (𝕚 𝕟)
  f-arr-𝕚-r : (¬inA : k ¬ε A)
            → Sfind B k 𝕟
            → Sfind (A `→ B) k (𝕚 𝕟)
  f-arr-𝕔   : (¬inA : k ¬ε A)
            → Sfind B k 𝕟
            → Sfind (A `→ B) k (𝕔 𝕟)
  f-∀-𝕚     : Sfind A (#S k) (𝕚 𝕟)
            → Sfind (`∀ A) k (𝕚 𝕟)
  f-∀-𝕔     : Sfind A (#S k) (𝕔 𝕟)
            → Sfind (`∀ A) k (𝕔 𝕟)
  f-𝕥       : Sfind A (#S k) 𝕟
            → Sfind (`∀ A) k (𝕥 𝕟)


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

data WFR : Env n m → HitMis m → Set where
  wfr-base : WFT Γ H
          → WFR (Γ ⋈) H
  wfr-hit  : WFR Γ H
           → WFR (Γ ,∙) (hit H)
  wfr-mis∙ : WFR Γ H
           → WFR (Γ ,∙) (mis H)
  wfr-mis= : WFR Γ H
           → WFR (Γ ,= A) (mis H)
  wfr-mis^ : WFR Γ H
           → WFR (Γ ,^) (mis H)

data WFC : Env n m → HitMis m → Set where
  wfc-base : WFT Γ H
           → WFC (Γ ⋈) H
  wfc-hit=  : WFC Γ H
           → WFC (Γ ,= A) (hit H)
  wfc-mis∙ : WFC Γ H
           → WFC (Γ ,∙) (mis H)
  wfc-mis= : WFC Γ H
           → WFC (Γ ,= A) (mis H)
  wfc-mis^ : WFC Γ H
           → WFC (Γ ,^) (mis H)


infix 3 _⊢t_
data _⊢t_ (Γ : Env n m) (A : Type m) : Set where
  justts : ∀ {H}
         → A 𝕗𝕧 H
         → WFS Γ H
         → Γ ⊢t A

infix 3 _⊢r'_
data _⊢r'_ (Γ : Env n m) (A : Type m) : Set where
  justrs : ∀ {H}
         → A 𝕗𝕧 H
         → WFR Γ H
         → Γ ⊢r' A

infix 3 _⊢c'_
data _⊢c'_ (Γ : Env n m) (A : Type m) : Set where
  justcs : ∀ {H}
         → A 𝕗𝕧 H
         → WFC Γ H
         → Γ ⊢c' A

data TRegularS : Env n m → Set where
  reg-Z : TRegularS ∅
  reg-S, : TRegularS Γ
         → (regA : Γ ⊢t A)
         → TRegularS (Γ , A)
  reg-S∙ : TRegularS Γ
         → TRegularS (Γ ,∙)
  reg-S^ : TRegularS Γ
         → TRegularS (Γ ,^)
  reg-S= : TRegularS Γ
         → (regA : Γ ⊢t A) -- we never access this entry, it's only created by initials
         → TRegularS (Γ ,= A)

data SRegularS : Env n m → Set where
  reg-Z : (regΓ : TRegularS Γ)
        → SRegularS (Γ ⋈)
  reg-S∙ : SRegularS Δ
         → SRegularS (Δ ,∙)
  reg-S^ : SRegularS Δ
         → SRegularS (Δ ,^)
  reg-S= : SRegularS Δ
         → (regA : Δ ⊢t A)
         → SRegularS (Δ ,= A)


infix 3 _⊨_#_⌞_⌝_
data _⊨_#_⌞_⌝_ : Env n m → SCounter → Type m → Polar → Type m → Set where
  s-refl :
      (regΔ : SRegularS Δ)
    → (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊨ Z # A ⌞ ≤⁺ ⌝ A%
  s-int :
      (regΔ : SRegularS Δ)
    → Δ ⊨ ∞ # Int ⌞ ≤ ⌝ Int
  s-var-∙ :
      (regΔ : SRegularS Δ)
    → (inΔ : Δ ∋∙ X)
    → Δ ⊨ ∞ # ‶ X ⌞ ≤ ⌝ ‶ X
  s-arr₁ :
      Δ ⊨ ∞ # C ⌞ ⋆ ≤ ⌝ A
    → Δ ⊨ ∞ # B ⌞ ≤ ⌝ D
    → Δ ⊨ ∞ # A `→ B ⌞ ≤ ⌝ C `→ D
  s-arr₂ :
      Δ ⊨ ∞ # C ⌞ ≤⁻ ⌝ A
    → Δ ⊨ 𝕟 # B ⌞ ≤⁺ ⌝ D
    → Δ ⊨ 𝕚 𝕟 # A `→ B ⌞ ≤⁺ ⌝ C `→ D
  s-arr₃ :
      (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊨ 𝕟 # B ⌞ ≤⁺ ⌝ D
    → Δ ⊨ 𝕔 𝕟 # A `→ B ⌞ ≤⁺ ⌝ A% `→ D
  s-∀ :
      Δ ,∙ ⊨ ∞ # A ⌞ ≤ ⌝ B
    → Δ ⊨ ∞ # `∀ A ⌞ ≤ ⌝ `∀ B
  s-∀l :
      Δ ,= B ⊨ 𝕟 # A ⌞ ≤⁺ ⌝ C' `→ D'
    → (ic : (S𝕚𝕔 𝕟))
    → (fd : Sfind A #0 𝕟)
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊨ 𝕟 # `∀ A ⌞ ≤⁺ ⌝ C `→ D
  s-tapp :
      Δ ,∙ ⊨ 𝕟 # A ⌞ ≤⁺ ⌝ C
    → Δ ⊨ 𝕥 𝕟 # `∀ A ⌞ ≤⁺ ⌝ `∀ C
  -- two atomic rules
  s-svar-l : ∀ {X A}
    → (SRegularS Δ)
    → (inΔ : Δ ∋ X := A)
    → Δ ⊨ ∞ # ‶ X ⌞ ≤⁺ ⌝ A
  s-svar-r : ∀ {X A}
    → (SRegularS Δ)
    → (inΔ : Δ ∋ X := A)
    → Δ ⊨ ∞ # A ⌞ ≤⁻ ⌝ ‶ X
  s-svar-𝕚 :
      Δ ∋ X := C
    → Δ ⊨ (𝕚 𝕟) # C ⌞ ≤⁺ ⌝ A `→ B
    → Δ ⊨ (𝕚 𝕟) # ‶ X ⌞ ≤⁺ ⌝ A `→ B
  s-svar-𝕔 :
      Δ ∋ X := C
    → Δ ⊨ (𝕔 𝕟) # C ⌞ ≤⁺ ⌝ A `→ B
    → Δ ⊨ (𝕔 𝕟) # ‶ X ⌞ ≤⁺ ⌝ A `→ B
  s-svar-𝕥 :
      Δ ∋ X := B
    → Δ ⊨ (𝕥 𝕟) # B ⌞ ≤⁺ ⌝ `∀ C
    → Δ ⊨ (𝕥 𝕟) # ‶ X ⌞ ≤⁺ ⌝ `∀ C




_ : ∅ ⋈ ⊨ 𝕥 Z # `∀ (‶ #0 `→ ‶ #0) ⌞ ≤⁺ ⌝ `∀ (‶ #0 `→ ‶ #0)
_ = s-tapp (s-refl (reg-S∙ (reg-Z reg-Z)) (⊢c-arr (⊢c-var-∙ Z) (⊢c-var-∙ Z)) (grd-arr (grd-var∙ Z) (grd-var∙ Z)))

postulate
  s-sregulars : Γ ⊨ 𝕟 # A ⌞ ≤ ⌝ B
            → SRegularS Γ

  ss-⊢r : Γ ⊨ 𝕟 # A ⌞ ≤⁺ ⌝ B
        → Γ ⊢r B
