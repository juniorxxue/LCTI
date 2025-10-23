module Implicit.Decl2Interm.Corollaries where

open import Implicit.Language.All
import Implicit.Decl.All as D
open import Implicit.Decl.All
open import Implicit.Interm.All

open import Implicit.Decl2Interm.Main

complete+' : Γ ⊢d j # A% ≤ B
          → Γ ≫ A ⇘ A%
          → Γ ⊢ j # A ⌞ ≤⁺ ⌝ B
complete+' s grd = complete+ (⊢d→⊢d² s) grd

complete+0' : Γ ⋈ ⊢d j # A ≤ B
            → Γ ⋈ ⊢r A
            → Γ ⋈ ⊢r B
            → Γ ⋈ ⊢ j # A ⌞ ≤⁺ ⌝ B
complete+0' s regA regB = complete+' s (⊢r-≫-eq regA)


complete-' : Γ ⊢d `□ # A ≤ B%
          → Γ ≫ B ⇘ B%
          → Γ ⊢ `□ # A ⌞ ≤⁻ ⌝ B
complete-' s grd = complete- (⊢d→⊢d² s) grd

⊢complete : Γ ⊢d j # e ⦂ A
          → Γ ⊢ j # e ⦂ A
⊢complete (⊢lit regΓ) = ⊢lit regΓ
⊢complete (⊢var regΓ x∈Γ) = ⊢var regΓ x∈Γ
⊢complete (⊢ann ⊢e) = ⊢ann (⊢complete ⊢e)
⊢complete (⊢lam₁ ⊢e) = ⊢lam₁ (⊢complete ⊢e)
⊢complete (⊢lam₂ ⊢e) = ⊢lam₂ (⊢complete ⊢e)
⊢complete (⊢app ⊢e ⊢e₁) = ⊢app (⊢complete ⊢e) (⊢complete ⊢e₁)
⊢complete (⊢sub ⊢e B≤A gc j≢Z) = ⊢sub (⊢complete ⊢e) (complete+ (⊢d→⊢d² B≤A) (⊢r-≫-eq (⊢r-𝕣 (D.t-⊢r ⊢e)))) gc j≢Z
⊢complete (⊢tabs ⊢e) = ⊢tabs (⊢complete ⊢e)
⊢complete (⊢tapp ⊢e st regA s) = ⊢tapp (⊢complete ⊢e) st regA (complete+ (⊢d→⊢d² s) (⊢r-≫-eq (⊢r-𝕣 (st0-⊢r (D.t-⊢r ⊢e) st regA))))
