module Implicit.Common where
-- shared constructs between Decl. and Algo.

open import Implicit.Prelude public

----------------------------------------------------------------------
--+                             Syntax                             +--
----------------------------------------------------------------------

infixr 5  ƛ_
infixl 7  _·_
infix  9  `_
infixr 5  Λ_
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

----------------------------------------------------------------------
--+                             Shift                              +--
----------------------------------------------------------------------

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
  k : Fin m
  x : Fin n
  A B C D : Type m
  e e₁ e₂ : Term n m

-- the n ensures we can find the type
lookup : Env n m → Fin n → Type m
lookup (Γ , A) #0     = A
lookup (Γ , A) (#S k) = lookup Γ k
lookup (Γ ,∙) k       = ↑ty0 (lookup Γ k)
lookup (Γ ,= A) k     = ↑ty0 (lookup Γ k)


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

↑ty0-tm : Term n m → Term n (1 + m)
↑ty0-tm = ↑ty-in-tm #0

-- subst
infix 6 [_/_]ˢ_

[_/_]ˢ_ : Fin (1 + m) → Type m → Type (1 + m) → Type m
[ k / A ]ˢ Int      = Int
[ k / A ]ˢ (‶ X) with k #≟ X
... | yes p = A
... | no ¬p = ‶ punchOut {i = k} {j = X} ¬p
[ k / A ]ˢ (B `→ C) = ([ k / A ]ˢ B) `→ ([ k / A ]ˢ C)
[ k / A ]ˢ (`∀ B)   = `∀ ([ #S k / ↑ty0 A ]ˢ B)

infix 7 [_]ˢ_
[_]ˢ_ : Type m → Type (1 + m) → Type m
[_]ˢ_ = [_/_]ˢ_ #0

infix 6 [_/_]ᵗ_
[_/_]ᵗ_ : Fin (1 + m) → Type m → Term n (1 + m) → Term n m
[ k / A ]ᵗ lit i = lit i
[ k / A ]ᵗ ` x = ` x
[ k / A ]ᵗ (ƛ e) = ƛ ([ k / A ]ᵗ e)
[ k / A ]ᵗ e₁ · e₂ = ([ k / A ]ᵗ e₁) · ([ k / A ]ᵗ e₂)
[ k / A ]ᵗ (e ⦂ B) = ([ k / A ]ᵗ e) ⦂ ([ k / A ]ˢ B)
[ k / A ]ᵗ (Λ e) = Λ [ #S k / ↑ty0 A ]ᵗ e

infix 7 [_]ᵗ_
[_]ᵗ_ : Type m → Term n (1 + m) → Term n m
[_]ᵗ_ = [_/_]ᵗ_ #0


-- unshift is just substing with a random type
↓ty0 : Type (1 + m) → Type m
↓ty0 A = [ Int ]ˢ A

-- solved existentials (k = A) is in Γ
infix 3 _:=_∈_
data _:=_∈_ : Fin m → Type m → Env n m → Set where
  Z  : #0 := A ∈ Γ ,= ↓ty0 A
  S∙ :
      k := ↓ty0 A ∈ Γ
    → #S k := A ∈ Γ ,∙
  S= :
      k := ↓ty0 A ∈ Γ
    → #S k := A ∈ Γ ,= B
  k, : 
      k := A ∈ Γ
    → k := A ∈ Γ , B 


----------------------------------------------------------------------
--+                            Structs                             +--
----------------------------------------------------------------------

infix 3 ty_↑_⇘_

data ty_↑_⇘_ : Type m → Fin (1 + m) → Type (1 + m) → Set where
  ↑int : ∀ {k : Fin (1 + m)} → ty Int ↑ k ⇘ Int
  ↑var : ∀ {k : Fin (1 + m)} {X} → ty (‶ X) ↑ k ⇘ ‶ punchIn k X
  ↑arr : ∀ {A B : Type m} {A' B' : Type (1 + m)} {k}
    → ty A ↑ k ⇘ A'
    → ty B ↑ k ⇘ B'
    → ty A `→ B ↑ k ⇘ A' `→ B'
  ↑∀ : ∀ {A : Type (1 + m)} {A' k}
    → ty A ↑ #S k ⇘ A'
    → ty (`∀ A) ↑ k ⇘ `∀ A'

↑ty0_⇘_ : Type m → Type (1 + m) → Set
↑ty0_⇘_ A A' = ty_↑_⇘_ A #0 A'

-- shift is unique
shift-unique : ∀ {A : Type m} {k A₁ A₂}
  → ty A ↑ k ⇘ A₁
  → ty A ↑ k ⇘ A₂
  → A₁ ≡ A₂
shift-unique ↑int ↑int = refl
shift-unique ↑var ↑var = refl
shift-unique (↑arr sf1 sf3) (↑arr sf2 sf4) rewrite shift-unique sf1 sf2 | shift-unique sf3 sf4 = refl
shift-unique (↑∀ sf1) (↑∀ sf2) rewrite shift-unique sf1 sf2 = refl

shift-total : forall (A : Type m) (k)
  → ∃ λ A' → ty A ↑ k ⇘ A'
shift-total Int k = ⟨ Int , ↑int ⟩
shift-total (‶ X) k = ⟨ (‶ punchIn k X) , ↑var ⟩
shift-total (A `→ A₁) k with shift-total A k
... | ⟨ fst , snd ⟩ with shift-total A₁ k
... | ⟨ fst₁ , snd₁ ⟩ = ⟨ (fst `→ fst₁) , ↑arr snd snd₁ ⟩
shift-total (`∀ A) k with shift-total A (#S k) 
... | ⟨ fst , snd ⟩ = ⟨ (`∀ fst) , (↑∀ snd) ⟩

infix 3 [_/_]v_⇘_
data [_/_]v_⇘_ : Fin (1 + m) → Type m → Fin (1 + m) → Type m → Set where
  st-var-eq : ∀ {k} {A : Type m}
    → [ k / A ]v k ⇘ A
  st-var-neq : ∀ {k X} {A : Type m}
    → (¬p : k ≢ X)
    → [ k / A ]v X ⇘ ‶ punchOut {i = k} {j = X} ¬p

infix 3 [_/_]ˢ_⇘_
data [_/_]ˢ_⇘_ : Fin (1 + m) → Type m → Type (1 + m) → Type m → Set where
  st-int : ∀ {k} {A : Type m}
    → [ k / A ]ˢ Int ⇘ Int
  st-var-eq : ∀ {k} {A : Type m}
    → [ k / A ]ˢ (‶ k) ⇘ A
  st-var-neq : ∀ {k X} {A : Type m}
    → (¬p : k ≢ X)
    → [ k / A ]ˢ (‶ X) ⇘ ‶ punchOut {i = k} {j = X} ¬p
  st-arr : ∀ {A : Type m} {B C B' C' k}
    → [ k / A ]ˢ B ⇘ B'
    → [ k / A ]ˢ C ⇘ C'
    → [ k / A ]ˢ (B `→ C) ⇘ B' `→ C'
  st-∀ : ∀ {A : Type m} {A' B B' k}
    → (up : ty A ↑ #0 ⇘ A')
    → [ #S k / A' ]ˢ B ⇘ B'
    → [ k / A ]ˢ (`∀ B) ⇘ `∀ B'

[_]ˢ_⇘_ : Type m → Type (1 + m) → Type m → Set
[_]ˢ_⇘_ = [_/_]ˢ_⇘_ #0

-- type subst is unique
subst-unique' : ∀ {A : Type m} {k B B₁ B₂}
  → [ k / A ]ˢ B ⇘ B₁
  → [ k / A ]ˢ B ⇘ B₂
  → B₁ ≡ B₂
subst-unique' st-int st-int = refl
subst-unique' st-var-eq st-var-eq = refl
subst-unique' st-var-eq (st-var-neq ¬p) = ⊥-elim (¬p refl)
subst-unique' (st-var-neq ¬p) st-var-eq = ⊥-elim (¬p refl)
subst-unique' (st-var-neq ¬p) (st-var-neq ¬p₁) = refl
subst-unique' (st-arr st1 st3) (st-arr st2 st4) rewrite subst-unique' st1 st2 | subst-unique' st3 st4 = refl
subst-unique' (st-∀ up st1) (st-∀ up₁ st2) rewrite shift-unique up up₁ | subst-unique' st1 st2 = refl

subst-unique : ∀ {A : Type m} {B B₁ B₂}
  → [ A ]ˢ B ⇘ B₁
  → [ A ]ˢ B ⇘ B₂
  → B₁ ≡ B₂
subst-unique st1 st2 = subst-unique' {k = #0} st1 st2

data Apps : ℕ → ℕ → Set where
  nil : Apps n m
  _∷a_ : Term n m → Apps n m → Apps n m

data AppsType : ℕ → Set where
  nil : AppsType m
  _∷a_ : Type m → AppsType m → AppsType m
  `∀_ : AppsType (1 + m) → AppsType m

infix 3 [_/_]ˢˢ_⇘_
data [_/_]ˢˢ_⇘_ : Fin (1 + m) → Type m → AppsType (1 + m) → AppsType m → Set where

  st-nil : ∀ {k : Fin (1 + m)} {A}
    → [ k / A ]ˢˢ nil ⇘ nil
  st-cons : ∀ {k : Fin (1 + m)} {A B B' Bs Bs'}
    → [ k / A ]ˢ B ⇘ B'
    → [ k / A ]ˢˢ Bs ⇘ Bs'
    → [ k / A ]ˢˢ B ∷a Bs ⇘ B' ∷a Bs'
  st-∀ : ∀ {k : Fin (1 + m)} {A A' B B'}
    → (up : ty A ↑ #0 ⇘ A')
    → [ #S k / A' ]ˢˢ B ⇘ B'
    → [ k / A ]ˢˢ (`∀ B) ⇘ `∀ B'

[_]ˢˢ_⇘_ : Type m → AppsType (1 + m) → AppsType m → Set
[_]ˢˢ_⇘_ = [_/_]ˢˢ_⇘_ #0

postulate
  substs-unique : ∀ {A : Type m} {B B₁ B₂}
    → [ A ]ˢˢ B ⇘ B₁
    → [ A ]ˢˢ B ⇘ B₂
    → B₁ ≡ B₂

up : Fin (1 + n) → Apps n m → Apps (1 + n) m
up n nil = nil
up n (e ∷a as) = (↑tm n e) ∷a (up n as)

up0 : Apps n m → Apps (1 + n) m
up0 = up #0

upty : Fin (1 + m) → Apps n m → Apps n (1 + m)
upty k nil = nil
upty k (e ∷a as) = ↑ty-in-tm k e ∷a upty k as

upty0 : Apps n m → Apps n (1 + m)
upty0 = upty #0

uptyT : Fin (1 + m) → AppsType m → AppsType (1 + m)
uptyT k nil = nil
uptyT k (A ∷a As) = ↑ty k A ∷a uptyT k As
uptyT k (`∀ As) = `∀ uptyT (#S k) As

uptyT0 : AppsType m → AppsType (1 + m)
uptyT0 = uptyT #0

infix 5 [_/_]ᵗ_⇘_
data [_/_]ᵗ_⇘_ : Fin (1 + m) → Type m → Term n (1 + m) → Term n m → Set where
  st-lit : ∀ {k A i}
    → [ k / A ]ᵗ lit i ⇘ (Term n m ∋⦂ lit i)
  st-var : ∀ {k A x}
    → [ k / A ]ᵗ ` x ⇘ (Term n m ∋⦂ ` x)
  st-ƛ : ∀ {k A e e'}
    → [ k / A ]ᵗ e ⇘ e'
    → [ k / A ]ᵗ (ƛ e) ⇘ (Term n m ∋⦂ ƛ e')
  st-· : ∀ {k A e₁ e₂ e₁' e₂'}
    → [ k / A ]ᵗ e₁ ⇘ e₁'
    → [ k / A ]ᵗ e₂ ⇘ e₂'
    → [ k / A ]ᵗ (e₁ · e₂) ⇘ (Term n m ∋⦂ e₁' · e₂')
  st-⦂ : ∀ {k A e B e' B'}
    → [ k / A ]ᵗ e ⇘ e'
    → [ k / A ]ˢ B ⇘ B'
    → [ k / A ]ᵗ (e ⦂ B) ⇘ (Term n m ∋⦂ e' ⦂ B')
  st-Λ : ∀ {k A e e'}
    → [ #S k / ↑ty0 A ]ᵗ e ⇘ e'
    → [ k / A ]ᵗ (Λ e) ⇘ (Term n m ∋⦂ Λ e')
