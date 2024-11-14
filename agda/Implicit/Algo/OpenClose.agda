module Implicit.Algo.OpenClose where

open import Implicit.Language
open import Implicit.Algo.Syntax

-- an algorithmic version to define closedness and openness
-- however, it could work for defining a specification around k ε A and and Ψ ⊢^ k

private
  variable
    Ψ : SEnv n m
    X : Fin m
    A B : Type m

infix 3 _⊢c_
infix 3 _⊢o_

-- open: have free existential variables
data _⊢o_ : SEnv n m → Type m → Set where
  ⊢o-var^0 :
      Ψ ,^ ⊢o ‶ #0
  ⊢o-var∙S :
      Ψ ⊢o ‶ X
    → Ψ ,∙ ⊢o ‶ #S X
  ⊢o-var,S :
      Ψ ⊢o ‶ X
    → Ψ , A ⊢o ‶ X
  ⊢o-var^S :
      Ψ ⊢o ‶ X
    → Ψ ,^ ⊢o ‶ #S X
  ⊢o-var=S :
      Ψ ⊢o ‶ X
    → Ψ ,= A ⊢o ‶ #S X
  ⊢o-arr-l :
      Ψ ⊢o A
    → Ψ ⊢o (A `→ B)
  ⊢o-arr-r :
      Ψ ⊢o B
    → Ψ ⊢o (A `→ B)    
  ⊢o-∀ :
      Ψ ,∙ ⊢o A
    → Ψ ⊢o `∀ A

-- closed: no free existential variables
data _⊢c_ : SEnv n m → Type m → Set where
  ⊢c-int :
      Ψ ⊢c Int
  ⊢c-var∙0 :
      Ψ ,∙ ⊢c ‶ #0
  ⊢c-var=0 :
      Ψ ,= A ⊢c ‶ #0
  ⊢c-var,S :
      Ψ ⊢c ‶ X
    → Ψ , A ⊢c ‶ X
  ⊢c-var∙S :
      Ψ ⊢c ‶ X
    → Ψ ,∙ ⊢c ‶ #S X
  ⊢c-var^S :
      Ψ ⊢c ‶ X
    → Ψ ,^ ⊢c ‶ #S X
  ⊢c-var=S :
      Ψ ⊢c ‶ X
    → Ψ ,= A ⊢c ‶ #S X
  ⊢c-arr :
       Ψ ⊢c A
    → Ψ ⊢c B
    → Ψ ⊢c (A `→ B)
  ⊢c-∀ :
      Ψ ,∙ ⊢c A
    → Ψ ⊢c `∀ A

