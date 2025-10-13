module Implicit.Interm2Decl.Corollaries where

open import Implicit.Language.All
open import Implicit.Decl.All renaming (_⊢_#_≤_ to _⊢d²_#_≤_)
open import Implicit.Decl.Subtyping renaming (_⊢_#_≤_ to _⊢d¹_#_≤_)
open import Implicit.Decl.Typing renaming (_⊢_#_⦂_ to _⊢d_#_⦂_; t-⊢r to t-⊢r-this)
open import Implicit.Interm.All renaming (_⊢_#_⌞_⌝_ to _⊢i_#_⌞_⌝_; _⊢_#_⦂_ to _⊢i_#_⦂_; t-⊢r to t-⊢r-that)
open import Implicit.Decl.Equiv renaming (complete to v2→v1)

open import Implicit.Interm2Decl.Main renaming (sound to sound-this)

⊢sound : Γ ⊢i j # e ⦂ A
       → Γ ⊢d j # e ⦂ A
⊢sound (⊢lit regΓ) = ⊢lit regΓ
⊢sound (⊢var regΓ x∈Γ) = ⊢var regΓ x∈Γ
⊢sound (⊢ann ⊢e) = ⊢ann (⊢sound ⊢e)
⊢sound (⊢lam₁ ⊢e) = ⊢lam₁ (⊢sound ⊢e)
⊢sound (⊢lam₂ ⊢e) = ⊢lam₂ (⊢sound ⊢e)
⊢sound (⊢app₁ ⊢e ⊢e₁) = ⊢app₁ (⊢sound ⊢e) (⊢sound ⊢e₁)
⊢sound (⊢app₂ ⊢e ⊢e₁) = ⊢app₂ (⊢sound ⊢e) (⊢sound ⊢e₁)
⊢sound (⊢sub ⊢e B≤A gc j≢Z) = ⊢sub (⊢sound ⊢e) (v2→v1 (sound-this B≤A (⊢r-≫-eq (⊢r-𝕣 (t-⊢r-this (⊢sound ⊢e)))) (⊢r-≫-eq (⊢r-𝕣 (t-⊢r-that (⊢sub ⊢e B≤A gc j≢Z)))))) gc j≢Z
⊢sound (⊢tabs ⊢e) = ⊢tabs (⊢sound ⊢e)
⊢sound (⊢tapp ⊢e st) = ⊢tapp (⊢sound ⊢e) st
