module Poly.Common where
-- shared constructs between Decl. and Algo.

open import Poly.Prelude public

----------------------------------------------------------------------
--+                             Syntax                             +--
----------------------------------------------------------------------

infixr 5  ƛ_
infixl 7  _·_
infix  9  `_
infixr 5  Λ_
infixl 5  _[_]
infix  5  _⦂_

infix  9  ‶_
infixr 8  _`→_
infixr 8  `∀_

variable
  m n m' n' : ℕ

data Type : ℕ → Set where
  Int    : Type m
  ‶_     : (X : Fin m) → Type m
  _`→_   : (A : Type m) → (B : Type m) → Type m
  `∀_    : (A : Type (1 + m)) → Type m

data Term : ℕ → ℕ → Set where
  lit      : (i : ℕ) → Term n m
  `_       : (x : Fin n) → Term n m
  ƛ_       : (e : Term (1 + n) m) → Term n m
  _·_      : (e₁ : Term n m) → (e₂ : Term n m) → Term n m
  _⦂_      : (e : Term n m) → (A : Type m) → Term n m
  Λ_       : (e : Term n (1 + m)) → Term n m
  _[_]     : (e : Term n m) → (A : Type m) → Term n m

----------------------------------------------------------------------
--+                             Shift                              +--
----------------------------------------------------------------------

infix 3 ty_↑_⇨_

data ty_↑_⇨_ : Type m → Fin (1 + m) → Type (1 + m) → Set where
  ↑int : ∀ {k : Fin (1 + m)} → ty Int ↑ k ⇨ Int
  ↑var : ∀ {k : Fin (1 + m)} {X} → ty (‶ X) ↑ k ⇨ ‶ punchIn k X
  ↑arr : ∀ {A B : Type m} {A' B' : Type (1 + m)} {k}
    → ty A ↑ k ⇨ A'
    → ty B ↑ k ⇨ B'
    → ty A `→ B ↑ k ⇨ A' `→ B'
  ↑∀ : ∀ {A : Type (1 + m)} {A' k}
    → ty A ↑ #S k ⇨ A'
    → ty (`∀ A) ↑ k ⇨ `∀ A'

↑ty : Fin (1 + m) → Type m → Type (1 + m)
↑ty k Int      = Int
↑ty k (‶ X)    = ‶ punchIn k X
↑ty k (A `→ B) = ↑ty k A `→ ↑ty k B
↑ty k (`∀ A)   = `∀ (↑ty (#S k) A)

↑ty0 : Type m → Type (1 + m)
↑ty0 {m} = ↑ty {m} #0

----------------------------------------------------------------------
--+                          Environments                          +--
----------------------------------------------------------------------

infixl 4 _,_
infixl 4 _,∙
infixl 4 _,=_

data Env : ℕ → ℕ → Set where
  ∅     : Env 0 0
  _,_   : Env n m → (A : Type m) → Env (1 + n) m
  _,∙   : Env n m → Env n (1 + m)
  _,=_  : Env n m → (A : Type m) → Env n (1 + m)


private variable
  Γ : Env n m

-- the n ensures we can find the type
lookup : Env n m → Fin n → Type m
lookup (Γ , A) #0     = A
lookup (Γ , A) (#S k) = lookup Γ k
lookup (Γ ,∙) k       = ↑ty0 (lookup Γ k)
lookup (Γ ,= A) k     = ↑ty0 (lookup Γ k)

infix 3 _∋_⦂_
data _∋_⦂_ : Env n m → Fin n → Type m → Set where
  Z : ∀ {A}
    → Γ ∋ #0 ⦂ A
  S, : ∀ {A k}
    → Γ ∋ k ⦂ A
    → Γ , A ∋ #S k ⦂ A
  S∙ : ∀ {A A' k}
    → Γ ∋ k ⦂ A
    → ty A ↑ #0 ⇨ A'
    → Γ ,∙ ∋ k ⦂ A'
  S,= : ∀ {A A' B k}
    → Γ ∋ k ⦂ A
    → ty A ↑ #0 ⇨ A'
    → Γ ,= B ∋ k ⦂ A'

----------------------------------------------------------------------
--+                           Type Subst                           +--
----------------------------------------------------------------------

-- shift for term
↑tm : Fin (1 + n) → Term n m → Term (1 + n) m
↑tm k (lit i)    = lit i
↑tm k (` x)      = ` (punchIn k x)
↑tm k (ƛ e)      = ƛ (↑tm (#S k) e)
↑tm k (e₁ · e₂)  = ↑tm k e₁ · ↑tm k e₂
↑tm k (e ⦂ A)    = (↑tm k e) ⦂ A
↑tm k (Λ e)      = Λ (↑tm k e)
↑tm k (e [ A ])  = ↑tm k e [ A ]

↑tm0 : Term n m → Term (1 + n) m
↑tm0 = ↑tm #0

-- shift type in term
↑ty-in-tm : Fin (1 + m) → Term n m → Term n (1 + m)
↑ty-in-tm k (lit i)    = lit i
↑ty-in-tm k (` x)      = ` x
↑ty-in-tm k (ƛ e)      = ƛ (↑ty-in-tm k e)
↑ty-in-tm k (e₁ · e₂)  = ↑ty-in-tm k e₁ · ↑ty-in-tm k e₂
↑ty-in-tm k (e ⦂ A)    = (↑ty-in-tm k e) ⦂ (↑ty k A)
↑ty-in-tm k (Λ e)      = Λ (↑ty-in-tm (#S k) e)
↑ty-in-tm k (e [ A ])  = ↑ty-in-tm k e [ ↑ty k A ]

infix 3 ty-in-tm_↑_⇨_
data ty-in-tm_↑_⇨_ : Term n m → Fin (1 + m) → Term n (1 + m) → Set where
  ↑lit : ∀ {i} {k : Fin (1 + m)}
    → ty-in-tm (Term n m ∋⦂ lit i) ↑ k ⇨ lit i
  ↑var : ∀ {x : Fin n} {k : Fin (1 + m)}
    → ty-in-tm ` x ↑ k ⇨ ` x
  ↑lam : ∀ {e : Term (1 + n) m} {e' k}
    → ty-in-tm e ↑ k ⇨ e'
    → ty-in-tm (ƛ e) ↑ k ⇨ ƛ e'
  ↑app : ∀ {e₁ e₂ : Term n m} {e₁' e₂' k}
    → ty-in-tm e₁ ↑ k ⇨ e₁'
    → ty-in-tm e₂ ↑ k ⇨ e₂'
    → ty-in-tm (e₁ · e₂) ↑ k ⇨ e₁' · e₂'
  ↑ann : ∀ {e : Term n m} {A : Type m} {e' A' k}
    → ty-in-tm e ↑ k ⇨ e'
    → ty A ↑ k ⇨ A'
    → ty-in-tm (e ⦂ A) ↑ k ⇨ e' ⦂ A'
  ↑Λ : ∀ {e : Term n (1 + m)} {e' k}
    → ty-in-tm e ↑ #S k ⇨ e'
    → ty-in-tm (Λ e) ↑ k ⇨ Λ e'
  ↑tapp : ∀ {e : Term n m} {A : Type m} {e' A' k}
    → ty-in-tm e ↑ k ⇨ e'
    → ty A ↑ k ⇨ A'
    → ty-in-tm (e [ A ]) ↑ k ⇨ e' [ A' ]

-- subst type
infix 6 [_/_]ˢ_
[_/_]ˢ_ : Fin (1 + m) → Type m → Type (1 + m) → Type m
[ k / A ]ˢ Int      = Int
[ k / A ]ˢ (‶ X) with k #≟ X
... | yes p = A
... | no ¬p = ‶ punchOut {i = k} {j = X} ¬p
[ k / A ]ˢ (B `→ C) = ([ k / A ]ˢ B) `→ ([ k / A ]ˢ C)
[ k / A ]ˢ (`∀ B)   = `∀ ([ #S k / ↑ty0 A ]ˢ B)

infix 3 [_/_]ˢ_⇨_
data [_/_]ˢ_⇨_ : Fin (1 + m) → Type m → Type (1 + m) → Type m → Set where
  st-int : ∀ {k} {A : Type m}
    → [ k / A ]ˢ Int ⇨ Int
  st-var-eq : ∀ {k} {A : Type m}
    → [ k / A ]ˢ (‶ k) ⇨ A
  st-var-neq : ∀ {k X} {A : Type m}
    → (¬p : k ≢ X)
    → [ k / A ]ˢ (‶ X) ⇨ ‶ punchOut {i = k} {j = X} ¬p
  st-arr : ∀ {A : Type m} {B C B' C' k}
    → [ k / A ]ˢ B ⇨ B'
    → [ k / A ]ˢ C ⇨ C'
    → [ k / A ]ˢ (B `→ C) ⇨ B' `→ C'
  st-∀ : ∀ {A : Type m} {A' B B' k}
    → ty A ↑ #0 ⇨ A'
    → [ #S k / A' ]ˢ B ⇨ B'
    → [ k / A ]ˢ (`∀ B) ⇨ `∀ B'

[_]ˢ_⇨_ : Type m → Type (1 + m) → Type m → Set
[_]ˢ_⇨_ = [_/_]ˢ_⇨_ #0

infix 6 [_]ˢ_
[_]ˢ_ : Type m → Type (1 + m) → Type m
[_]ˢ_ = [_/_]ˢ_ #0

-- subst type in term
infix 6 [_/_]ᵗ_
[_/_]ᵗ_ : Fin (1 + m) → Type m → Term n (1 + m) → Term n m
[ k / A ]ᵗ lit i = lit i
[ k / A ]ᵗ ` x = ` x
[ k / A ]ᵗ (ƛ e) = ƛ ([ k / A ]ᵗ e)
[ k / A ]ᵗ e₁ · e₂ = ([ k / A ]ᵗ e₁) · ([ k / A ]ᵗ e₂)
[ k / A ]ᵗ (e ⦂ B) = ([ k / A ]ᵗ e) ⦂ ([ k / A ]ˢ B)
[ k / A ]ᵗ (Λ e) = Λ [ #S k / ↑ty0 A ]ᵗ e
[ k / A ]ᵗ (e [ B ]) = ([ k / A ]ᵗ e) [ ([ k / A ]ˢ B) ]

infix 6 [_]ᵗ_
[_]ᵗ_ : Type m → Term n (1 + m) → Term n m
[_]ᵗ_ = [_/_]ᵗ_ #0

-- unshift is just substing with a random type
↓ty0 : Type (1 + m) → Type m
↓ty0 A = [ Int ]ˢ A

-- solved existentials (k = A) is in Γ
infix 3 _:=_∈_
data _:=_∈_ : Fin m → Type m → Env n m → Set where

  Z : ∀ {A} → #0 := A ∈ Γ ,= ↓ty0 A
  S, : ∀ {k A B}
    → k := A ∈ Γ
    → k := A ∈ Γ , B
  S∙ : ∀ {k A}
    → k := ↓ty0 A ∈ Γ
    → #S k := A ∈ Γ ,∙
  S= : ∀ {k A B}
    → k := ↓ty0 A ∈ Γ
    → #S k := A ∈ Γ ,= B

----------------------------------------------------------------------
--+                            Structs                             +--
----------------------------------------------------------------------

data Apps : ℕ → ℕ → Set where
  nil : Apps n m
  _∷a_ : Term n m → Apps n m → Apps n m
  _∷t_ : Type m → Apps n m → Apps n m

data AppsType : ℕ → Set where
  nil : AppsType m
  _∷a_ : Type m → AppsType m → AppsType m
  _∷t_ : Type m → AppsType m → AppsType m
