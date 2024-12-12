module Implicit.Algo.Extension where

open import Implicit.Language
open import Implicit.Algo.Syntax

private variable
  Γ Γ' : Env n m
  A : Type m

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
    → Γ ,^ ⊆ Γ' ,= A    
  svar :
      Γ ⊆ Γ'
    → Γ ,= A ⊆ Γ' ,= A
