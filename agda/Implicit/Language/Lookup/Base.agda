module Implicit.Language.Lookup.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Subst.All

-- lookup an entry: term variable, won't bypass the ⋈, since assume in TypEnv
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

-- lookup an entry in subtyping env : solution
infix 3 _∋_:=_
data _∋_:=_ : Env n m → Fin m → Type m → Set where
  Z  : (up : ↑ty0 A ⇘ A')
     → Δ ,= A ∋ #0 := A'
  S∙ : Δ ∋ k := A
     → (up : ↑ty0 A ⇘ A')
     → Δ ,∙ ∋ #S k := A'
  S^ : Δ ∋ k := A
     → (up : ↑ty0 A ⇘ A')
     → Δ ,^ ∋ #S k := A'
  S= : Δ ∋ k := A
     → (up : ↑ty0 A ⇘ A')
     → Δ ,= B ∋ #S k := A'
  S, : Δ ∋ k := A
     → Δ , B ∋ k := A

-- lookup an entry in subtyping env: solution (simpler ver.)
infix 3 _∋=_
data _∋=_ : Env n m → Fin m → Set where
  Z  : Δ ,= A ∋= #0
  S∙ : Δ ∋= k
     → Δ ,∙ ∋= #S k
  S^ : Δ ∋= k
     → Δ ,^ ∋= #S k
  S= : Δ ∋= k
     → Δ ,= B ∋= #S k
  S, : Δ ∋= k
     → Δ , A ∋= k

-- lookup an entry in subtyping env: (unsolved) existential variable
infix 3 _∋^_
data _∋^_ : Env n m → Fin m → Set where
  Z  : Δ ,^ ∋^ #0
  S∙ : Δ ∋^ k
     → Δ ,∙ ∋^ #S k
  S= : Δ ∋^ k
     → Δ ,= B ∋^ #S k
  S^ : Δ ∋^ k
     → Δ ,^ ∋^ #S k

-- lookup an entry: universal variable
-- works on either typing or subtyping env
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
  S⋈ : Γ ∋∙ k
     → Γ ⋈ ∋∙ k
