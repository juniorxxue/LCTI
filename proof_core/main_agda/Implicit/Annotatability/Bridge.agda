module Implicit.Annotatability.Bridge where

open import Implicit.Language.All
open import Implicit.Decl.Typing
open import Implicit.Annotatability.DeclPartial renaming (_⊢_#_⦂_ to _⊢p_#_⦂_)
open import Implicit.Annotatability.IF
open import Implicit.Annotatability.Elaboration


par-complete : Γ ⊢p j # e ⦂ A
             → Γ ⊢ j # e ⦂ A
par-complete (⊢lit regΓ) = ⊢lit regΓ
par-complete (⊢var regΓ x∈Γ) = ⊢var regΓ x∈Γ
par-complete (⊢ann ⊢e) = ⊢ann (par-complete ⊢e)
par-complete (⊢lam₁ ⊢e) = ⊢lam₁ (par-complete ⊢e)
par-complete (⊢lam₂ ⊢e) = ⊢lam₂ (par-complete ⊢e)
par-complete (⊢app₁ ⊢e ⊢e₁) = ⊢app₁ (par-complete ⊢e) (par-complete ⊢e₁)
par-complete (⊢app₂ ⊢e ⊢e₁) = ⊢app₂ (par-complete ⊢e) (par-complete ⊢e₁)
par-complete (⊢sub ⊢e B≤A gc j≢Z) = ⊢sub (par-complete ⊢e) B≤A gc j≢Z
par-complete (⊢tabs ⊢e) = ⊢tabs (par-complete ⊢e)
par-complete (⊢tapp ⊢e st) = ⊢tapp (par-complete ⊢e) st


annotatability-real : Γ ⊢ e ⦂ A ⟶ e'
                    → Γ ⊢ ∞ # e' ⦂ A
annotatability-real ⊢e with annotatability ⊢e
... | bd = par-complete bd


annotatability-real' : Γ ⊢ e ⦂ A ⟶ e'
                     → Γ ⊢ Z # (e' ⦂ A) ⦂ A
annotatability-real' ⊢e = ⊢ann (annotatability-real ⊢e)
