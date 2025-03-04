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
  S⋈ : Γ ∋ k := A
     → Γ ⋈ ∋ k := A


infix 3 _∋_:=¹_
data _∋_:=¹_ : Env n m → Fin m → Type m → Set where
  S, : Γ ∋ k :=¹ A
     → Γ , B ∋ k :=¹ A
  S∙ : Γ ∋ k :=¹ A
     → (up : ↑ty0 A ⇘ A')
     → Γ ,∙ ∋ #S k :=¹ A'
  S^ : Γ ∋ k :=¹ A
     → (up : ↑ty0 A ⇘ A')
     → Γ ,^ ∋ #S k :=¹ A'
  S= : Γ ∋ k :=¹ A
     → (up : ↑ty0 A ⇘ A')
     → Γ ,= B ∋ #S k :=¹ A'
  S⋈ : Γ ∋ X := A
     → Γ ⋈ ∋ X :=¹ A

infix 3 _∋_:=²_
data _∋_:=²_ : Env n m → Fin m → Type m → Set where
  Z= : ↑ty0 A ⇘ A'
     → Γ ,= A ∋ #0 :=² A'
  S∙ : Γ ∋ k :=² A
     → (up : ↑ty0 A ⇘ A')
     → Γ ,∙ ∋ #S k :=² A'
  S^ : Γ ∋ k :=² A
     → (up : ↑ty0 A ⇘ A')
     → Γ ,^ ∋ #S k :=² A'
  S= : Γ ∋ k :=² A
     → (up : ↑ty0 A ⇘ A')
     → Γ ,= B ∋ #S k :=² A'

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
  S⋈ : Γ ∋= k
     → Γ ⋈ ∋= k

-- this lookup works on the subtyping environment;
-- but lookup an entry: solution in the (inner) typing environment.
infix 3 _∋=¹_
data _∋=¹_ : Env n m → Fin m → Set where
{-
  Z  : TypEnv Γ
     → Γ ,= A ∋=¹ #0
-}
  S, : Γ ∋=¹ k
     → Γ , B ∋=¹ k
  S∙ : Γ ∋=¹ k
     → Γ ,∙ ∋=¹ #S k
  S^ : Γ ∋=¹ k
     → Γ ,^ ∋=¹ #S k
  S= : Γ ∋=¹ k
     → Γ ,= B ∋=¹ #S k
  S⋈ : Γ ∋= k
    →  Γ ⋈ ∋=¹ k

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
  S⋈ : Γ ∋^ k
     → Γ ⋈ ∋^ k

-- ex variable in SubEnv
infix 3 _∋^²_
data _∋^²_ : Env n m → Fin m → Set where
  Z^ : Γ ,^ ∋^² #0
  S, : Γ ∋^² k
     → Γ , B ∋^² k
  S∙ : Γ ∋^² k
     → Γ ,∙ ∋^² #S k
  S^ : Γ ∋^² k
     → Γ ,^ ∋^² #S k
  S= : Γ ∋^² k
     → Γ ,= B ∋^² #S k

-- sol variable in SubEnv
infix 3 _∋=²_
data _∋=²_ : Env n m → Fin m → Set where
  Z^ : Γ ,= A ∋=² #0
  S, : Γ ∋=² k
     → Γ , B ∋=² k
  S∙ : Γ ∋=² k
     → Γ ,∙ ∋=² #S k
  S^ : Γ ∋=² k
     → Γ ,^ ∋=² #S k
  S= : Γ ∋=² k
     → Γ ,= B ∋=² #S k

{-
-- ex variable in SubEnv, not sure where is it used
infix 3 _∋^=²_
data _∋^=²_ : Env n m → Fin m → Set where
  Z^ : SubEnv Γ
     → Γ ,^ ∋^=² #0
  Z= : SubEnv Γ
     → Γ ,= A ∋^=² #0
  S, : Γ ∋^=² k
     → Γ , B ∋^=² k
  S∙ : Γ ∋^=² k
     → Γ ,∙ ∋^=² #S k
  S^ : Γ ∋^=² k
     → Γ ,^ ∋^=² #S k
  S= : Γ ∋^=² k
     → Γ ,= B ∋^=² #S k
-}

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
  S⋈ : Γ ∋∙ k
     → Γ ⋈ ∋∙ k
