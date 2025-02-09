module Implicit.Language.Extension.Base where

open import Implicit.Language.Base
open import Implicit.Language.OpenClose.All

infix 3 _⊆_
data _⊆_ : Env n m → Env n m → Set where
  base : ∅ ⊆ ∅
  uvar :
      Γ ⊆ Γ'
    → Γ ,∙ ⊆ Γ' ,∙
  var :
      Γ ⊆ Γ'
    → Γ , A ⊆ Γ' , A
  evar :
      Γ ⊆ Γ'
    → Γ ,^ ⊆ Γ' ,^
  evar-sol :
      Γ ⊆ Γ'
    → (cloA : Γ' ⊢c A) -- instead of Γ, we use Γ' to prove trans, not sure it's a good choice or not
    → Γ ,^ ⊆ Γ' ,= A
  svar :
      Γ ⊆ Γ'
    → Γ ,= A ⊆ Γ' ,= A
