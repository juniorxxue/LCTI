module Implicit.Algo.Lookup where

open import Implicit.Language
open import Implicit.Algo.Syntax

private variable
  Ψ : SEnv n m
  k : Fin m
  A A' B : Type m

-- k is existential variable in Ψ
infix 3 _^∈_
data _^∈_ : Fin m → SEnv n m → Set where

  Z :
      #0 ^∈ Ψ ,^
  S^ :
      k ^∈ Ψ
    → #S k ^∈ Ψ ,^
  S∙ :
      k ^∈ Ψ
    → #S k ^∈ Ψ ,∙
  S, :
      k ^∈ Ψ
    → k ^∈ Ψ , A
  S= :
      k ^∈ Ψ
    → #S k ^∈ Ψ ,= A

-- k is universal variable in Ψ
infix 3 _∙∈_
data _∙∈_ : Fin m → SEnv n m → Set where
  
  Z : #0 ∙∈ Ψ ,∙
  S^ :
      k ∙∈ Ψ
    → #S k ∙∈ Ψ ,^
  S∙ :
      k ∙∈ Ψ
    → #S k ∙∈ Ψ ,∙
  S, :
      k ∙∈ Ψ
    → k ∙∈ Ψ , A
  S= :
      k ∙∈ Ψ
    → #S k ∙∈ Ψ ,= A


infix 3 _:=_∈_
data _:=_∈_ : Fin m → Type m → SEnv n m → Set where

  Z :
      (up : ↑ty0 A ⇘ A')
    → #0 := A' ∈ Ψ ,= A
  S, :
      k := A ∈ Ψ
    → k := A ∈ Ψ , B
  S^ :
      k := A ∈ Ψ
    → (up : ↑ty0 A ⇘ A')
    → #S k := A' ∈ Ψ ,^
  S∙ :
      k := A ∈ Ψ
    → (up : ↑ty0 A ⇘ A')
    → #S k := A' ∈ Ψ ,∙
  S= :
      k := ⟦ B ⟧ A ∈ Ψ
    → #S k := A ∈ Ψ ,= B

-- a simple version of _:=_∈_ to check
infix 3 _=∈_
data _=∈_ : Fin m → SEnv n m → Set where

  Z :
      #0 =∈ Ψ ,= A
  S, :
      k =∈ Ψ
    → k =∈ Ψ , B
  S^ :
      k =∈ Ψ
    → #S k =∈ Ψ ,^
  S∙ :
      k =∈ Ψ
    → #S k =∈ Ψ ,∙
  S= :
      k =∈ Ψ
    → #S k =∈ Ψ ,= B

