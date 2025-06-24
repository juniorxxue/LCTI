module Implicit.Decl2Interm.Corollaries where

open import Implicit.Language.All
open import Implicit.Decl.All renaming (_⊢_#_≤_ to _⊢d²_#_≤_)
open import Implicit.Decl.Subtyping renaming (_⊢_#_≤_ to _⊢d¹_#_≤_)
open import Implicit.Decl.Typing renaming (_⊢_#_⦂_ to _⊢d_#_⦂_; t-⊢r to t-⊢r-this)
open import Implicit.Interm.All renaming (_⊢_#_⌞_⌝_ to _⊢i_#_⌞_⌝_; _⊢_#_⦂_ to _⊢i_#_⦂_)
open import Implicit.Decl.Equiv renaming (sound to v1→v2)

open import Implicit.Decl2Interm.Main

⊢complete : Γ ⊢d j # e ⦂ A
          → Γ ⊢i j # e ⦂ A
⊢complete (⊢lit regΓ) = ⊢lit regΓ
⊢complete (⊢var regΓ x∈Γ) = ⊢var regΓ x∈Γ
⊢complete (⊢ann ⊢e) = ⊢ann (⊢complete ⊢e)
⊢complete (⊢lam₁ ⊢e) = ⊢lam₁ (⊢complete ⊢e)
⊢complete (⊢lam₂ ⊢e) = ⊢lam₂ (⊢complete ⊢e)
⊢complete (⊢app₁ ⊢e ⊢e₁) = ⊢app₁ (⊢complete ⊢e) (⊢complete ⊢e₁)
⊢complete (⊢app₂ ⊢e ⊢e₁) = ⊢app₂ (⊢complete ⊢e) (⊢complete ⊢e₁)
⊢complete (⊢sub ⊢e B≤A gc j≢Z) = ⊢sub (⊢complete ⊢e) (complete+ (v1→v2 B≤A) (⊢r-≫-eq (⊢r-𝕣 (t-⊢r-this ⊢e)))) gc j≢Z
⊢complete (⊢tabs ⊢e) = ⊢tabs (⊢complete ⊢e)
⊢complete (⊢tapp ⊢e st) = ⊢tapp (⊢complete ⊢e) st
