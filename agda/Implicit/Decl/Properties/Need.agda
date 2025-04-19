module Implicit.Decl.Properties.Need where

open import Implicit.Language.All
open import Implicit.Decl.Typing



data Comj : Counter m → Counter m → Set where
  comj-Z : Comj Z j
  comj-∞ : Comj j ∞
  comj-𝕚 : Comj j₁ j₂
         → Comj (𝕚 j₁) (𝕚 j₂)

t-need : Γ ⊢ j # e ⦂ A
       → ∃[ j' ](Need e j'
         × Comj j' j)

t-need0 : Γ ⊢ Z # e ⦂ A
        → Need e Z
t-need0 ⊢e with t-need ⊢e
... | ⟨ fst , ⟨ fst₁ , comj-Z ⟩ ⟩ = fst₁

t-need (⊢lit regΓ) = ⟨ Z , ⟨ need-lit , comj-Z ⟩ ⟩
t-need (⊢var regΓ x∈Γ) = ⟨ Z , ⟨ need-var , comj-Z ⟩ ⟩
t-need (⊢ann ⊢e) = ⟨ Z , ⟨ need-ann , comj-Z ⟩ ⟩
t-need (⊢lam₁ ⊢e) = ⟨ 𝕚 (t-need ⊢e .proj₁) ,
                     ⟨ need-lam (t-need ⊢e .proj₂ .proj₁) , comj-∞ ⟩ ⟩
t-need (⊢lam₂ ⊢e) = ⟨ 𝕚 (t-need ⊢e .proj₁) ,
                     ⟨ need-lam (t-need ⊢e .proj₂ .proj₁) ,
                     comj-𝕚 (t-need ⊢e .proj₂ .proj₂) ⟩
                     ⟩
t-need (⊢app₁ ⊢e ⊢e₁) with t-need ⊢e
... | ⟨ Z , r ⟩ = ⟨ Z , ⟨ need-app1 (r .proj₁) , comj-Z ⟩ ⟩
t-need (⊢app₂ ⊢e ⊢e₁) with t-need ⊢e
... | ⟨ Z , r ⟩ = ⟨ Z , ⟨ need-app1 (r .proj₁) , comj-Z ⟩ ⟩
... | ⟨ 𝕚 fst , ⟨ fst₁ , comj-𝕚 snd ⟩ ⟩ = ⟨ fst , ⟨ need-app2 fst₁ , snd ⟩ ⟩
t-need (⊢sub ⊢e B≤A gc j≢Z) = ⟨ Z , ⟨ (t-need0 ⊢e) , comj-Z ⟩ ⟩
t-need (⊢tabs ⊢e) = ⟨ Z , ⟨ need-tabs , comj-Z ⟩ ⟩
t-need (⊢tapp ⊢e st) = ⟨ Z , ⟨ need-tapp , comj-Z ⟩ ⟩
