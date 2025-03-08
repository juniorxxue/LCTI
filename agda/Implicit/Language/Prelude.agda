module Implicit.Language.Prelude where

open import Data.Nat hiding (_/_) public
open import Data.Nat.Properties public
open import Data.Bool using (Bool; _∨_; _∧_; true; false) public
open import Data.String using (String) public
open import Relation.Nullary using (yes; no; Dec; ¬_) public
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness) public
open import Function.Base using (case_of_; case_return_of_) public
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; cong; cong₂; sym; ≢-sym) public
open import Data.Empty public
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩) public
open import Data.List using (List; []; _∷_; _++_; reverse; map; foldr; downFrom) renaming (length to len) public
open import Data.List.Properties using (map-++) public
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mmap) public
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎) public
open import Data.Fin using (Fin; punchIn; punchOut; toℕ; inject₁) renaming (zero to #0; suc to #S; pred to #pred; _<_ to _#<_; _≤_ to _#≤_) public
open import Data.Fin.Properties using (punchIn-injective; punchInᵢ≢i; punchIn-punchOut; punchOut-punchIn) renaming (<-cmp to #<-cmp; _≟_ to _#≟_) public
open import Function renaming (_∋_ to _∋⦂_) public

variable
  m m' n n' o : ℕ

m+1≤n→m≤n : suc m ≤ n
          → m ≤ n
m+1≤n→m≤n (s≤s m+1≤n) = m≤n⇒m≤1+n m+1≤n

n-1+1≡n+1-1 : 0 < n
            → suc (pred n) ≡ pred (suc n)
n-1+1≡n+1-1 (s≤s 0<n) = refl

m+1≰n+1⇒m≰n : suc m ≰ suc n
            → m ≰ n
m+1≰n+1⇒m≰n m+1≰n+1 = λ m≤n → m+1≰n+1 (s≤s m≤n)

m≰n⇒n<m : m ≰ n
        → n < m
m≰n⇒n<m {zero} {zero} m≰n = ⊥-elim (m≰n z≤n)
m≰n⇒n<m {zero} {suc n} m≰n = ⊥-elim (m≰n z≤n)
m≰n⇒n<m {suc m} {zero} m≰n = s≤s z≤n
m≰n⇒n<m {suc m} {suc n} m≰n = s≤s (m≰n⇒n<m {m} {n} (m+1≰n+1⇒m≰n m≰n))

m+0≡m : ∀ m → m + 0 ≡ m
m+0≡m m rewrite +-comm m 0 = refl

m≤m : m ≤ m
m≤m {zero} = z≤n
m≤m {suc m} = s≤s m≤m

-- pattern ⟦_⟧ z = z ∷ []

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

m+n<o⇒m<o : m + n < o
          → m < o
m+n<o⇒m<o {m} {n} {o} m+n<o = ≤-trans (s≤s (m≤m+n m n)) m+n<o

m+n<o⇒n<o : m + n < o
          → n < o
m+n<o⇒n<o {m} {n} {o} m+n<o = ≤-trans (s≤s (m≤n+m n m)) m+n<o



----------------------------------------------------------------------
--+                              Fin                               +--
----------------------------------------------------------------------

variable
  x y : Fin n
  k k' k₁ k₂ k₃ X Y : Fin m

inject₂ : Fin n → Fin (suc (suc n))
inject₂ #0 = #0
inject₂ (#S k) = #S (inject₂ k)

≢-pred : #S x ≢ #S y
       → x ≢ y
≢-pred neq eq = neq (cong #S eq)

≢-suc : x ≢ y
      → #S x ≢ #S y
≢-suc eq refl = ⊥-elim (eq refl)

punchIn-≤ : ∀ {k₁ : Fin m} {k₂}
          → k₂ #≤ k₁
          → punchIn k₂ k₁ ≡ #S k₁
punchIn-≤ {k₁ = k₁} {k₂ = #0} sm = refl
punchIn-≤ {k₁ = #S k₁} {k₂ = #S k₂} (s≤s sm) = cong #S (punchIn-≤ sm)

#1 : ∀ {m} → Fin (2 + m)
#1 = #S #0

#2 : ∀ {m} → Fin (3 + m)
#2 = #S #1

punchIn-inject : X #< k
               → inject₁ X ≡ punchIn k X
punchIn-inject {X = #0} {k = #S k} lt = refl
punchIn-inject {X = #S X} {k = #S k} (s≤s lt) = cong #S (punchIn-inject lt)

punchIn-inject-neq : X #< k
                   → X ≢ k'
                   → inject₁ X ≢ punchIn k k'
punchIn-inject-neq {X = #0} {k = #S k} {#0} lt neq = λ z → neq refl
punchIn-inject-neq {X = #S X} {k = #S k} {#0} lt neq = λ ()
punchIn-inject-neq {X = #0} {k = #S k} {#S k'} lt neq = λ ()
punchIn-inject-neq {X = #S X} {k = #S k} {#S k'} (s≤s lt) neq = ≢-suc (punchIn-inject-neq lt (≢-pred neq))

punchIn-comm : ∀ {x : Fin n} {j k}
   → j #≤ k
   → punchIn (inject₁ j) (punchIn k x) ≡
      punchIn (#S k) (punchIn j x)
punchIn-comm {x = #0} {#0} j≤k = refl
punchIn-comm {x = #0} {#S j} {#S k} j≤k = refl
punchIn-comm {x = #S x} {#0} j≤k = refl
punchIn-comm {x = #S x} {#S j} {#S k} (s≤s j≤k) = cong #S (punchIn-comm j≤k)

m#<m+1 : k #< #S k
m#<m+1 {k = #0} = s≤s z≤n
m#<m+1 {k = #S k} = s≤s m#<m+1


#S-injective : #S X ≡ #S Y
             → X ≡ Y
#S-injective refl = refl

punchIn-≢ : k₁ ≢ k₂
          → punchIn k k₁ ≢ punchIn k k₂
punchIn-≢ {k₁ = k₁} {k₂} {#0} neq refl = neq refl
punchIn-≢ {k₁ = #0} {#0} {#S k} neq peq = neq refl
punchIn-≢ {k₁ = #S k₁} {#S k₂} {#S k} neq peq = punchIn-≢ (≢-pred neq) (#S-injective peq)

#≤-#<-≢ : k₁ #≤ k₂
        → k₂ #< k₃
        → k₁ ≢ k₃
#≤-#<-≢ {k₁ = #0} {k₂ = #0} {k₃ = #S k₃} z≤n lt2 = λ ()
#≤-#<-≢ {k₁ = #0} {k₂ = #S k₂} {k₃ = #S k₃} z≤n lt2 = λ ()
#≤-#<-≢ {k₁ = #S k₁} {k₂ = #S k₂} {k₃ = #S k₃} (s≤s lt1) (s≤s lt2) = ≢-suc (#≤-#<-≢ lt1 lt2)
