module Implicit.Algo.Extension where

open import Implicit.Language
open import Implicit.Algo.Syntax

private variable
  Ψ Ψ' : SEnv n m
  A : Type m

infix 3 _⊆_
data _⊆_ : SEnv n m → SEnv n m → Set where
  base : ∅ ⊆ ∅
  uvar :
      Ψ ⊆ Ψ'
    → Ψ ,∙ ⊆ Ψ' ,∙
  var :
      Ψ ⊆ Ψ'
    → Ψ , A ⊆ Ψ' , A
  evar :
      Ψ ⊆ Ψ'
    → Ψ ,^ ⊆ Ψ' ,^
  evar-sol :
      Ψ ⊆ Ψ'
    → Ψ ,^ ⊆ Ψ' ,= A    
  svar :
      Ψ ⊆ Ψ'
    → Ψ ,= A ⊆ Ψ' ,= A
