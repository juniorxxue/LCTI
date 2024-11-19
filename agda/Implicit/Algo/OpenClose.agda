module Implicit.Algo.OpenClose where

open import Implicit.Language
open import Implicit.Algo.Syntax
open import Implicit.Algo.Lookup

-- an algorithmic version to define closedness and openness
-- however, it could work for defining a specification around k ε A and and Ψ ⊢^ k

private
  variable
    Ψ : SEnv n m
    X : Fin m
    A B : Type m
    Σ : Context n m
    e : Term n m

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


infix 3 _⊢cᶜ_
data _⊢cᶜ_ : SEnv n m → Context n m → Set where
  ⊢c-empty : Ψ ⊢cᶜ □
  ⊢c-τ : Ψ ⊢c A → Ψ ⊢cᶜ (τ A)
  ⊢c-term : Ψ ⊢cᶜ Σ → Ψ ⊢cᶜ [ e ]↝ Σ -- we may add conditions onto `e` later

infix 3 _⊢oᶜ_
data _⊢oᶜ_ : SEnv n m → Context n m → Set where
  ⊢o-τ : Ψ ⊢o A → Ψ ⊢oᶜ (τ A)
  ⊢o-term : Ψ ⊢oᶜ Σ → Ψ ⊢oᶜ [ e ]↝ Σ -- we may add conditions onto `e` later
