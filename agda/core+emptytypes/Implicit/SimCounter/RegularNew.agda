module Implicit.SimCounter.RegularNew where

open import Implicit.Language.All
open import Implicit.AuxLemmas

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
