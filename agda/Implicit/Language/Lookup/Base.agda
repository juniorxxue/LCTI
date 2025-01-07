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

----------------------------------------------------------------------
--+                         Entry Removal                          +--
----------------------------------------------------------------------

-- remove k-th entry (term binding) from environment
infix 5 _∤,∤_
_∤,∤_ : Env (1 + n) m → Fin (1 + n) → Env n m
(Γ , A) ∤,∤ #0 = Γ
_∤,∤_ {suc n} (Γ , A) (#S k) = (Γ ∤,∤ k) , A
(Γ ,∙) ∤,∤ k = (Γ ∤,∤ k) ,∙
(Γ ,^) ∤,∤ k = (Γ ∤,∤ k) ,^
(Γ ,= A) ∤,∤ k = (Γ ∤,∤ k) ,= A

-- remove (x : A) from k-th position
infix 3 _◀_,⇘_
data _◀_,⇘_ : Env (1 + n) m → Fin (1 + n) → Env n m → Set where
  ◀Z : Γ , A ◀ #0 ,⇘ Γ
  ◀S, : Γ ◀ k ,⇘ Γ'
      → Γ , B ◀ #S k ,⇘ Γ' , B
  ◀S^ : Γ ◀ k ,⇘ Γ'
      → (Γ ,^) ◀ k ,⇘ Γ' ,^
  ◀S∙ : Γ ◀ k ,⇘ Γ'
      → (Γ ,∙) ◀ k ,⇘ Γ' ,∙
  ◀S= : Γ ◀ k ,⇘ Γ'
      → (Γ ,= A) ◀ k ,⇘ Γ' ,= A

-- remove exsitential variable â from k-th posititon
infix 3 _◀_^⇘_
data _◀_^⇘_ : Env n (1 + m) → Fin (1 + m) → Env n m → Set where
  ◀Z  : Γ ,^ ◀ #0 ^⇘ Γ
  ◀S, : Γ ◀ k ^⇘ Γ'
      → B ↑ty k ⇘ B'
      → Γ , B' ◀ k ^⇘ Γ' , B
  ◀S^ : Γ ◀ k ^⇘ Γ'
      → Γ ,^ ◀ #S k ^⇘ Γ' ,^
  ◀S∙ : Γ ◀ k ^⇘ Γ'
      → Γ ,∙ ◀ #S k ^⇘ Γ' ,∙
  ◀S= : Γ ◀ k ^⇘ Γ'
      → A ↑ty k ⇘ A'
      → Γ ,= A' ◀ #S k ^⇘ Γ' ,= A

-- remove type variable a from k-th posititon
infix 3 _◀_∙⇘_
data _◀_∙⇘_ : Env n (1 + m) → Fin (1 + m) → Env n m → Set where
  ◀Z  : Γ ,∙ ◀ #0 ∙⇘ Γ
  ◀S, : Γ ◀ k ∙⇘ Γ'
      → B ↑ty k ⇘ B'
      → Γ , B' ◀ k ∙⇘ Γ' , B
  ◀S^ : Γ ◀ k ∙⇘ Γ'
      → Γ ,^ ◀ #S k ∙⇘ Γ' ,^
  ◀S∙ : Γ ◀ k ∙⇘ Γ'
      → Γ ,∙ ◀ #S k ∙⇘ Γ' ,∙
  ◀S= : Γ ◀ k ∙⇘ Γ'
      → A ↑ty k ⇘ A'
      → Γ ,= A' ◀ #S k ∙⇘ Γ' ,= A

-- remove solution entry, without doing subst
infix 3 _◀_=⇘_
data _◀_=⇘_ : Env n (1 + m) → Fin (1 + m) → Env n m → Set where
  ◀Z  : Γ ,= T ◀ #0 =⇘ Γ
  ◀S, : Γ ◀ k =⇘ Γ'
      → B ↑ty k ⇘ B'
      → Γ , B' ◀ k =⇘ Γ' , B
  ◀S^ : Γ ◀ k =⇘ Γ'
      → Γ ,^ ◀ #S k =⇘ Γ' ,^
  ◀S∙ : Γ ◀ k =⇘ Γ'
      → Γ ,∙ ◀ #S k =⇘ Γ' ,∙
  ◀S= : Γ ◀ k =⇘ Γ'
      → A ↑ty k ⇘ A'
      → Γ ,= A' ◀ #S k =⇘ Γ' ,= A


-- remove an entry a=A, we should be careful about this
-- removing an entry a=A requires us to do substittuiion on the remaining env

-- in algo, we need to first lookup the type A
-- then use type A to manipuate remaining envs to produce a new env
-- in this relation, we could assume we know A
infix 3 _◀_:=_⇘_
data _◀_:=_⇘_ : Env n (1 + m) → Fin (1 + m) → Type m → Env n m → Set where
  ◀Z : Γ ,= A ◀ #0 := A ⇘ Γ
  ◀S, : Γ ◀ k := A ⇘ Γ'
      → ⟦ k / A ⟧ B ⇘ B*
      → Γ , B ◀ k := A ⇘ Γ' , B*
  ◀S^ : Γ ◀ k := A ⇘ Γ'
      → (up : ↑ty0 A ⇘ A')
      → Γ ,^ ◀ #S k := A' ⇘ Γ' ,^
  ◀S∙ : Γ ◀ k := A ⇘ Γ'
      → (up : ↑ty0 A ⇘ A')
      → Γ ,∙ ◀ #S k := A' ⇘ Γ' ,∙
  ◀S= : Γ ◀ k := A ⇘ Γ'
      → (up : ↑ty0 A ⇘ A')
      → ⟦ k / A ⟧ B ⇘ B*
      → Γ ,= B ◀ #S k := A' ⇘ Γ' ,= B*


----------------------------------------------------------------------
--+                         Entry Insertion                        +--
----------------------------------------------------------------------

infix 3 _▶_,_⇘_
data _▶_,_⇘_ : Env n m → Fin (1 + n) → Type m → Env (1 + n) m → Set where
  ▶Z : Γ ▶ #0 , A ⇘ Γ , A
  ▶S, : Γ ▶ k , A ⇘ Γ'
      → (Γ , B) ▶ #S k , A ⇘ Γ' , B
  ▶S^ : Γ ▶ k , A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → (Γ ,^) ▶ k , A' ⇘ Γ' ,^
  ▶S∙ : Γ ▶ k , A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → (Γ ,∙) ▶ k , A' ⇘ Γ' ,∙
  ▶S= : Γ ▶ k , A  ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → (Γ ,= B) ▶ k , A' ⇘ Γ' ,= B

infix 3 _▶_,^⇘_
data _▶_,^⇘_ : Env n m → Fin (1 + m) → Env n (1 + m) → Set where
  ▶Z : Γ ▶ #0 ,^⇘ Γ ,^
  ▶S, : Γ ▶ #S k ,^⇘ Γ'
      → (upA : A ↑ty #S k ⇘ A')
      → Γ , A ▶ #S k ,^⇘ Γ' , A'
  ▶S^ : Γ ▶ k ,^⇘ Γ'
      → Γ ,^ ▶ #S k ,^⇘ Γ' ,^
  ▶S∙ : Γ ▶ k ,^⇘ Γ'
      → Γ ,∙ ▶ #S k ,^⇘ Γ' ,∙
  ▶S= : Γ ▶ k ,^⇘ Γ'
      → (upB : B ↑ty k ⇘ B')
      → Γ ,= B ▶ #S k ,^⇘ Γ' ,= B'

infix 3 _▶_,∙⇘_
data _▶_,∙⇘_ : Env n m → Fin (1 + m) → Env n (1 + m) → Set where
  ▶Z : Γ ▶ #0 ,∙⇘ Γ ,∙
  ▶S, : Γ ▶ #S k ,∙⇘ Γ'
      → A ↑ty #S k ⇘ A'
      → Γ , A ▶ #S k ,∙⇘ Γ' , A'
  ▶S^ : Γ ▶ k ,∙⇘ Γ'
      → Γ ,^ ▶ #S k ,∙⇘ Γ' ,^
  ▶S∙ : Γ ▶ k ,∙⇘ Γ'
      → Γ ,∙ ▶ #S k ,∙⇘ Γ' ,∙
  ▶S= : Γ ▶ k ,∙⇘ Γ'
      → B ↑ty k ⇘ B'
      → Γ ,= B ▶ #S k ,∙⇘ Γ' ,= B'

infix 3 _▶_,=_⇘_
data _▶_,=_⇘_ : Env n m → Fin (1 + m) → Type m → Env n (1 + m) → Set where
  ▶Z : Γ ▶ #0 ,= A ⇘ Γ ,= A
  ▶S, : Γ ▶ #S k ,= A ⇘ Γ'
      → B ↑ty #S k ⇘ B'
      → Γ , B ▶ #S k ,= A ⇘ Γ' , B'
  ▶S^ : Γ ▶ k ,= A ⇘ Γ'
      → ↑ty0 A ⇘ A' -- an alternative is defining an unshift
      → Γ ,^ ▶ #S k ,= A' ⇘ Γ' ,^
  ▶S∙ : Γ ▶ k ,= A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → Γ ,∙ ▶ #S k ,= A' ⇘ Γ' ,∙
  ▶S= : Γ ▶ k ,= A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → B ↑ty k ⇘ B'
      → Γ ,= B ▶ #S k ,= A' ⇘ Γ' ,= B'

----------------------------------------------------------------------
--+                       Entry Replacement                        +--
----------------------------------------------------------------------

-- replace entry ^a with a solution ^a=A in an environment
infix 3 [_/_]_⟹_↪_
data [_/_]_⟹_↪_ : Type m → Fin m → Env n m → Env n m → Type m → Set where
  ⟹^0 : (up : ↑ty0 A ⇘ A')
      → [ A' / #0 ] (Γ ,^) ⟹ (Γ ,= A) ↪ A'

  ⟹^S : [ A / k ] Γ ⟹ Γ' ↪ B
      → (up1 : ↑ty0 A ⇘ A')
      → (up2 : ↑ty0 B ⇘ B')
      → [ A' / #S k ] (Γ ,^) ⟹ Γ' ,^ ↪ B'

  ⟹∙S : [ A / k ] Γ ⟹ Γ' ↪ B
      → (up1 : ↑ty0 A ⇘ A')
      → (up2 : ↑ty0 B ⇘ B')
      → [ A' / #S k ] (Γ ,∙) ⟹ (Γ' ,∙) ↪ B'

  ⟹,S : [ A / k ] Γ ⟹ Γ' ↪ C
       → [ A / k ] (Γ , B) ⟹ (Γ' , B) ↪ C

  ⟹=S : [ A / k ] Γ ⟹ Γ' ↪ C
       → (up1 : ↑ty0 A ⇘ A')
       → (up2 : ↑ty0 C ⇘ C')
       → [ A' / #S k ] (Γ ,= B) ⟹ (Γ' ,= B) ↪ C'
