module Implicit.Interm2Decl.AuxLemmas where

open import Implicit.Language.All
open import Implicit.Decl.All renaming (_⊢_#_≤_ to _⊢d_#_≤_)
open import Implicit.Interm.All renaming (_⊢_#_⌞_⌝_ to _⊢i_#_⌞_⌝_)


≫-same : Γ ≫ A ⇘ A₁
       → Γ ◈ k ⇘ Γ'
       → Γ' ≫ A ⇘ A₂
       → k ¬ε A
       → A₁ ≡ A₂
≫-same grd-int new grd-int ¬ε-int = refl
≫-same (grd-var= x) new (grd-var= x₁) (¬ε-var x₂) = ◈-∋:=-neq-unique new x₂ x x₁
≫-same (grd-var= x) new (grd-var∙ x₁) (¬ε-var x₂) = let in2 = ◈-neq-∋:= x new x₂
                                                    in ⊥-elim (∋∙-∋:=-false x₁ in2)
≫-same (grd-var∙ x) new (grd-var= x₂) (¬ε-var x₁) = let in2 = ◈-neq-∋∙ x new x₁ in ⊥-elim (∋∙-∋:=-false in2 x₂)
≫-same (grd-var∙ x) new (grd-var∙ x₂) (¬ε-var x₁) = refl
≫-same (grd-arr grd1 grd3) new (grd-arr grd2 grd4) (¬ε-arr ninA ninA₁)
  with refl ← ≫-same grd1 new grd2 ninA
  with refl ← ≫-same grd3 new grd4 ninA₁ = refl
≫-same (grd-∀ grd1) new (grd-∀ grd2) (¬ε-∀ ninA) = cong `∀_ (≫-same grd1 (◈S∙ new) grd2 ninA)
