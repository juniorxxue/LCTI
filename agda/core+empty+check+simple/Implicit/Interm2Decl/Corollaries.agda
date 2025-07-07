module Implicit.Interm2Decl.Corollaries where

open import Implicit.Language.All
open import Implicit.Decl.All as D
open import Implicit.Interm.All as I
open import Implicit.Interm2Decl.Main renaming (sound to sound-this)

si→sd : Γ ⊢ j # A ⌞ ≤⁺ ⌝ B
      → Γ ⊢r A
      → Γ ⊢d j # A ≤ B
si→sd s regA = ⊢d²→⊢d (sound-this s (⊢r-≫-eq regA) (⊢r-≫-eq (s+-polarity s)))

⊢sound : Γ ⊢ j # e ⦂ A
       → Γ ⊢d j # e ⦂ A
⊢sound (⊢lit regΓ) = ⊢lit regΓ
⊢sound (⊢var regΓ x∈Γ) = ⊢var regΓ x∈Γ
⊢sound (⊢ann ⊢e) = ⊢ann (⊢sound ⊢e)
⊢sound (⊢lam₁ ⊢e) = ⊢lam₁ (⊢sound ⊢e)
⊢sound (⊢lam₂ ⊢e) = ⊢lam₂ (⊢sound ⊢e)
⊢sound (⊢app₁ ⊢e ⊢e₁) = ⊢app₁ (⊢sound ⊢e) (⊢sound ⊢e₁)
⊢sound (⊢app₂ ⊢e ⊢e₁) = ⊢app₂ (⊢sound ⊢e) (⊢sound ⊢e₁)
⊢sound (⊢sub ⊢e B≤A gc j≢Z) = ⊢sub (⊢sound ⊢e) (si→sd B≤A (⊢r-𝕣 (I.t-⊢r ⊢e))) gc j≢Z
⊢sound (⊢tabs ⊢e) = ⊢tabs (⊢sound ⊢e)
⊢sound (⊢tabs-∞ ⊢e) = ⊢tabs-∞ (⊢sound ⊢e)
⊢sound (⊢tapp ⊢e st) = ⊢tapp (⊢sound ⊢e) st
