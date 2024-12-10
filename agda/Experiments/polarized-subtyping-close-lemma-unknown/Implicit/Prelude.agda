module Implicit.Prelude where

open import Data.Nat hiding (_/_) public
open import Data.Nat.Properties public
open import Data.Bool using (Bool; _∨_; _∧_; true; false) public
open import Data.String using (String) public
open import Relation.Nullary using (yes; no; Dec; ¬_) public
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness) public
open import Function.Base using (case_of_; case_return_of_) public
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; cong; sym; ≢-sym) public
open import Data.Empty public
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩) public
open import Data.List using (List; []; _∷_; _++_; reverse; map; foldr; downFrom) renaming (length to len) public
open import Data.List.Properties using (map-++) public
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mmap) public
open import Data.Fin using (Fin; punchIn; punchOut; toℕ) renaming (zero to #0; suc to #S; pred to #pred; _≤_ to _#≤_) public
open import Data.Fin.Properties using (punchInᵢ≢i; punchOut-punchIn) renaming (<-cmp to #<-cmp; _≟_ to _#≟_) public
open import Function renaming (_∋_ to _∋⦂_) public

m+1≤n→m≤n : ∀ {m n}
  → suc m ≤ n
  → m ≤ n
m+1≤n→m≤n (s≤s m+1≤n) = m≤n⇒m≤1+n m+1≤n

n-1+1≡n+1-1 : ∀ {n}
  → 0 < n
  → suc (pred n) ≡ pred (suc n)
n-1+1≡n+1-1 (s≤s 0<n) = refl

m+1≰n+1⇒m≰n : ∀ {m n}
  → suc m ≰ suc n
  → m ≰ n
m+1≰n+1⇒m≰n m+1≰n+1 = λ m≤n → m+1≰n+1 (s≤s m≤n)  
  
m≰n⇒n<m : ∀ {m n}
  → m ≰ n
  → n < m
m≰n⇒n<m {zero} {zero} m≰n = ⊥-elim (m≰n z≤n)
m≰n⇒n<m {zero} {suc n} m≰n = ⊥-elim (m≰n z≤n)
m≰n⇒n<m {suc m} {zero} m≰n = s≤s z≤n
m≰n⇒n<m {suc m} {suc n} m≰n = s≤s (m≰n⇒n<m {m} {n} (m+1≰n+1⇒m≰n m≰n))

n<m⇒m≰n : ∀ {m n}
  → n < m
  → m ≰ n
n<m⇒m≰n {suc m} {zero} n<m = λ ()
n<m⇒m≰n {suc m} {suc n} (s≤s n<m) (s≤s m≤n) = n<m⇒m≰n {m} {n} n<m m≤n

m+0≡m : ∀ m
  → m + 0 ≡ m
m+0≡m m rewrite +-comm m 0 = refl

m≤m : ∀ {m}
  → m ≤ m
m≤m {zero} = z≤n
m≤m {suc m} = s≤s m≤m

-- pattern ⟦_⟧ z = z ∷ []

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

m+n<o⇒m<o : ∀ {m n o}
  → m + n < o
  → m < o
m+n<o⇒m<o {m} {n} {o} m+n<o = ≤-trans (s≤s (m≤m+n m n)) m+n<o

m+n<o⇒n<o : ∀ {m n o}
  → m + n < o
  → n < o
m+n<o⇒n<o {m} {n} {o} m+n<o = ≤-trans (s≤s (m≤n+m n m)) m+n<o



----------------------------------------------------------------------
--+                              Fin                               +--
----------------------------------------------------------------------

≢-pred : ∀ {n} {x y : Fin n}
  → #S x ≢ #S y
  → x ≢ y
≢-pred neq eq = neq (cong #S eq)

≢-suc : ∀ {n} {x y : Fin n}
  → x ≢ y
  → #S x ≢ #S y
≢-suc eq refl = ⊥-elim (eq refl)

punchIn-≤ : ∀ {m} {k₁ : Fin m} {k₂}
  → k₂ #≤ k₁
  → punchIn k₂ k₁ ≡ #S k₁
punchIn-≤ {k₁ = k₁} {k₂ = #0} sm = refl
punchIn-≤ {k₁ = #S k₁} {k₂ = #S k₂} (s≤s sm) = cong #S (punchIn-≤ sm)

#1 : ∀ {m} → Fin (2 + m)
#1 = #S #0

#2 : ∀ {m} → Fin (3 + m)
#2 = #S #1
