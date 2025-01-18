module Implicit.Language.Lookup.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift
open import Implicit.Language.Subst

-- lookup an entry: term variable
infix 3 _∋_⦂_
data _∋_⦂_ : Env n m → Fin n → Type m → Set where
  Z  : Γ , A ∋ #0 ⦂ A
  S, : Γ ∋ x ⦂ A
     → Γ , B ∋ #S x ⦂ A
  S∙ : Γ ∋ x ⦂ A
     → (up : ↑ty0 A ⇘ A')
     → Γ ,∙ ∋ x ⦂ A'
  S^ : Γ ∋ x ⦂ A
     → (up : ↑ty0 A ⇘ A')
     → Γ ,^ ∋ x ⦂ A'
  S= : Γ ∋ x ⦂ A
     → (up : ↑ty0 A ⇘ A')
     → Γ ,= B ∋ x ⦂ A'

-- lookup an entry: solution
infix 3 _∋_:=_
data _∋_:=_ : Env n m → Fin m → Type m → Set where
  Z  : (up : ↑ty0 A ⇘ A')
     → Γ ,= A ∋ #0 := A'
  S, : Γ ∋ k := A
     → Γ , B ∋ k := A
  S∙ : Γ ∋ k := A
     → (up : ↑ty0 A ⇘ A')
     → Γ ,∙ ∋ #S k := A'
  S^ : Γ ∋ k := A
     → (up : ↑ty0 A ⇘ A')
     → Γ ,^ ∋ #S k := A'
  S= : Γ ∋ k := A
     → (up : ↑ty0 A ⇘ A')
     → Γ ,= B ∋ #S k := A'

-- lookup an entry: solution (simpler ver.)
infix 3 _∋=_
data _∋=_ : Env n m → Fin m → Set where
  Z  : Γ ,= A ∋= #0
  S, : Γ ∋= k
     → Γ , B ∋= k
  S∙ : Γ ∋= k
     → Γ ,∙ ∋= #S k
  S^ : Γ ∋= k
     → Γ ,^ ∋= #S k
  S= : Γ ∋= k
     → Γ ,= B ∋= #S k

-- lookup an entry: (unsolved) existential variable
infix 3 _∋^_
data _∋^_ : Env n m → Fin m → Set where
  Z  : Γ ,^ ∋^ #0
  S, : Γ ∋^ k
     → Γ , A ∋^ k
  S∙ : Γ ∋^ k
     → Γ ,∙ ∋^ #S k
  S= : Γ ∋^ k
     → Γ ,= B ∋^ #S k
  S^ : Γ ∋^ k
     → Γ ,^ ∋^ #S k

-- lookup an entry: universal variable
infix 3 _∋∙_
data _∋∙_ : Env n m → Fin m → Set where
  Z  : Γ ,∙ ∋∙ #0
  S, : Γ ∋∙ k
     → Γ , A ∋∙ k
  S∙ : Γ ∋∙ k
     → Γ ,∙ ∋∙ #S k
  S= : Γ ∋∙ k
     → Γ ,= B ∋∙ #S k
  S^ : Γ ∋∙ k
     → Γ ,^ ∋∙ #S k

-- lookup a variable (can represent three kinds of entries), in a type
infix 3 _ε_
data _ε_ : Fin m → Type m → Set where
  ε-var :
      k ε (‶ k)
  ε-arr-l :
      k ε A
    → k ε A `→ B
  ε-arr-r :
      k ε B
    → k ε A `→ B
  ε-∀ :
      #S k ε A
    → k ε `∀ A
{-
-- a neg definition of ε
infix 3 _¬ε_
data _¬ε_ : Fin m → Type m → Set where
  ¬ε-int :
      k ¬ε Int
  ¬ε-var :
      k ≢ k'
    → k ¬ε (‶ k')
  ¬ε-arr :
      k ¬ε A
    → k ¬ε B
    → k ¬ε A `→ B
  ¬ε-∀ :
      #S k ¬ε A
    → k ¬ε `∀ A
-}
