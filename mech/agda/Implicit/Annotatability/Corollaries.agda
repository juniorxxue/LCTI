module Implicit.Annotatability.Corollaries where

open import Implicit.Language.All
open import Implicit.Decl.Typing
open import Implicit.Annotatability.DeclPartial renaming (_⊢_#_⦂_ to _⊢p_#_⦂_)
open import Implicit.Annotatability.IF
open import Implicit.Annotatability.Elaboration


par-complete : Γ ⊢p j # e ⦂ A
             → Γ ⊢d j # e ⦂ A
par-complete (⊢lit regΓ) = ⊢lit regΓ
par-complete (⊢var regΓ x∈Γ) = ⊢var regΓ x∈Γ
par-complete (⊢ann ⊢e) = ⊢ann (par-complete ⊢e)
par-complete (⊢lam₁ ⊢e) = ⊢lam₁ (par-complete ⊢e)
par-complete (⊢lam₂ ⊢e) = ⊢lam₂ (par-complete ⊢e)
par-complete (⊢app ⊢e ⊢e₁) = ⊢app (par-complete ⊢e) (par-complete ⊢e₁)
par-complete (⊢sub ⊢e B≤A gc j≢Z) = ⊢sub (par-complete ⊢e) B≤A gc j≢Z
par-complete (⊢tabs ⊢e) = ⊢tabs (par-complete ⊢e)

annotatability-real : Γ ⊢ e ⦂ A ⟶ e'
                    → Γ ⊢d `□ # e' ⦂ A
annotatability-real ⊢e with annotatability ⊢e
... | bd = par-complete bd


annotatability-real' : Γ ⊢ e ⦂ A ⟶ e'
                     → Γ ⊢d `■ # (e' ⦂ A) ⦂ A
annotatability-real' ⊢e = ⊢ann (annotatability-real ⊢e)
