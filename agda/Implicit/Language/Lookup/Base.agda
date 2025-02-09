module Implicit.Language.Lookup.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Subst.All

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
