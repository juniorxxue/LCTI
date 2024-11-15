module Implicit.Language.Lookup.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift
open import Implicit.Language.Subst

private variable
  Γ : Env n m
  A A' B C D : Type m
  i : Fin n
  k : Fin m

-- lookup an entry: term variable
infix 3 _∋_⦂_
data _∋_⦂_ : Env n m → Fin n → Type m → Set where
  Z  : Γ , A ∋ #0 ⦂ A
  S, : Γ ∋ i ⦂ A
     → Γ , B ∋ #S i ⦂ A
  S∙ : Γ ∋ i ⦂ A
     → ↑ty0 A ⇘ A'
     → Γ ,∙ ∋ i ⦂ A'
  S= : Γ ∋ i ⦂ A
     → ↑ty0 A ⇘ A'
     → Γ ,= B ∋ i ⦂ A'

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
  S= : Γ ∋ k := A'
     → (st : ⟦ B ⟧ A ⇘ A')
     → Γ ,= B ∋ #S k := A

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

-- remove k-th entry (term binding) from environment
_/,/_ : Env (1 + n) m → Fin (1 + n) → Env n m
(Γ , A) /,/ #0 = Γ
_/,/_ {suc n} (Γ , A) (#S k) = (Γ /,/ k) , A
(Γ ,∙) /,/ k = (Γ /,/ k) ,∙
(Γ ,= A) /,/ k = (Γ /,/ k) ,= A


