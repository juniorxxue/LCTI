module Poly.Algo where

open import Poly.Common

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

infixr 7 [_]↝_
infixr 7 ⟦_⟧↝_

data Context : ℕ → ℕ → Set where
  □     : Context n m
  τ_    : (A : Type m) → Context n m
  [_]↝_ : (e : Term n m) → Context n m → Context n m
  ⟦_⟧↝_ : (A : Type m) → Context n m → Context n m

data NonEmpty : Context n m → Set where
  ne-τ    : ∀ {A : Type m} → NonEmpty (Context n m ∋⦂ τ A)
  ne-app  : ∀ {e} {Σ : Context n m} → NonEmpty ([ e ]↝ Σ)
  ne-tapp : ∀ {A} {Σ : Context n m} → NonEmpty (⟦ A ⟧↝ Σ)  

↑Σ : Fin (1 + n) → Context n m → Context (1 + n) m
↑Σ k □ = □
↑Σ k (τ A) = τ A
↑Σ k ([ e ]↝ Σ) = [ ↑tm k e ]↝ (↑Σ k Σ)
↑Σ k (⟦ A ⟧↝ Σ) = ⟦ A ⟧↝ (↑Σ k Σ)

↑Σ0 : Context n m → Context (1 + n) m
↑Σ0 = ↑Σ #0

↑tyΣ : Fin (1 + m) → Context n m → Context n (1 + m)
↑tyΣ k □ = □
↑tyΣ k (τ A) = τ (↑ty k A)
↑tyΣ k ([ e ]↝ Σ) = [ ↑ty-in-tm k e ]↝ (↑tyΣ k Σ)
↑tyΣ k (⟦ A ⟧↝ Σ) = ⟦ ↑ty k A ⟧↝ (↑tyΣ k Σ)

↑tyΣ0 : Context n m → Context n (1 + m)
↑tyΣ0 = ↑tyΣ #0

infix 3 ty-in-con_↑_⇨_
data ty-in-con_↑_⇨_ : Context n m → Fin (1 + m) → Context n (1 + m) → Set where
  ↑empty : ∀ {k}
    → ty-in-con (Context n m ∋⦂ □) ↑ k ⇨ □
  ↑type  : ∀ {k A A'}
    → ty A ↑ k ⇨ A'
    → ty-in-con (Context n m ∋⦂ τ A) ↑ k ⇨ τ A'
  ↑term  : ∀ {Σ : Context n m} {k e e' Σ'}
    → ty-in-tm e ↑ k ⇨ e'
    → ty-in-con Σ ↑ k ⇨ Σ'
    → ty-in-con [ e ]↝ Σ ↑ k ⇨ [ e' ]↝ Σ'
  ↑tapp : ∀ {Σ : Context n m} {k A A' Σ'}
    → ty A ↑ k ⇨ A'
    → ty-in-con Σ ↑ k ⇨ Σ'
    → ty-in-con ⟦ A ⟧↝ Σ ↑ k ⇨ ⟦ A' ⟧↝ Σ'
  
private
  variable
    Γ Γ' Γ₁ Γ₂ Γ₃ : Env n m
    Σ Σ' : Context n m

data GenericConsumer : Term n m → Set where
  gc-i : ∀ {i} → GenericConsumer (Term n m ∋⦂ lit i)
  gc-var : ∀ {x} → GenericConsumer (Term n m ∋⦂ ` x)
  gc-ann : ∀ {e : Term n m} {A} → GenericConsumer (e ⦂ A)
  gc-tlam : ∀ {e : Term n (1 + m)} → GenericConsumer (Λ e)

infix 3 _⊢_⇒_⇒_
infix 3 _⊢_≤_

data _⊢_⇒_⇒_ : Env n m → Context n m → Term n m → Type m → Set
-- we cannot syntactically distinguish the result type here, which should contain unsolved variables
data _⊢_≤_ : Env n m → Type m → Context n m → Set

data _⊢_⇒_⇒_ where

  ⊢lit : ∀ {i}
    → Γ ⊢ □ ⇒ lit i ⇒ Int

  ⊢var : ∀ {x A}
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊢ □ ⇒ ` x ⇒ A

  ⊢ann : ∀ {e A B}
    → Γ ⊢ τ A ⇒ e ⇒ B
    → Γ ⊢ □ ⇒ e ⦂ A ⇒ A

  ⊢app : ∀ {e₁ e₂ A B}
    → Γ ⊢ [ e₂ ]↝ Σ ⇒ e₁ ⇒ A `→ B
    → Γ ⊢ Σ ⇒ e₁ · e₂ ⇒ B

  ⊢lam₁ : ∀ {A B C e}
    → Γ , A ⊢ τ B ⇒ e ⇒ C
    → Γ ⊢ τ (A `→ B) ⇒ ƛ e ⇒ A `→ C

  ⊢lam₂ : ∀ {A B e e₂}
    → Γ ⊢ □ ⇒ e₂ ⇒ A
    → Γ , A ⊢ ↑Σ0 Σ ⇒ e ⇒ B
    → Γ ⊢ [ e₂ ]↝ Σ ⇒ ƛ e ⇒ A `→ B
    
  ⊢sub : ∀ {g A}
    → Γ ⊢ □ ⇒ g ⇒ A          --- Γ ⊢ Z # e : A
    → (¬□ : NonEmpty Σ)
    → (gc : GenericConsumer g)
    → (s : Γ ⊢ A ≤ Σ)    --- Γ ⊢ j # A ≤ B
    → Γ ⊢ Σ ⇒ g ⇒ A         --- Γ ⊢ j # e ∶ B

  ⊢tabs₁ : ∀ {e A}
    → Γ ,∙ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ □ ⇒ Λ e ⇒ `∀ A  

  ⊢tapp : ∀ {e A B B'}
    → Γ ⊢ ⟦ A ⟧↝ Σ ⇒ e ⇒ `∀ B
    → (st : [ A ]ˢ B ⇨ B')
    → Γ ⊢ Σ ⇒ e [ A ] ⇒ B'
  
data _⊢_≤_ where

  s-empty : ∀ {A}
    → Γ ⊢ A ≤ □
  s-refl : ∀ {A}
    → Γ ⊢ A ≤ τ A
  s-arr : ∀ {e A B C}
    → Γ ⊢ B ≤ Σ
    → (⊢e : Γ ⊢ τ A ⇒ e ⇒ C)
    → Γ ⊢ A `→ B ≤ [ e ]↝ Σ 
  s-∀-t : ∀ {A B A'}
    → (st : [ B ]ˢ A ⇨ A')
    → Γ ⊢ A' ≤ Σ
    → Γ ⊢ `∀ A ≤ ⟦ B ⟧↝ Σ

----------------------------------------------------------------------
--+                           Splitting                            +--
----------------------------------------------------------------------

-- Bs' / A by B ⇨ Bs
infix 4 _/_by_⇨_
data _/_by_⇨_ : AppsType m → Type m → Type (1 + m) → AppsType (1 + m) → Set where
  /by-nil : ∀ {A : Type m} {B}
    → nil / A by B ⇨ nil
  /by-cons : ∀ {A : Type m} {B' Bs Bs' B₁ B₂}
    → [ A ]ˢ B₁ ⇨ B'
    → Bs' / A by B₂ ⇨ Bs
    → B' ∷a Bs' / A by (B₁ `→ B₂) ⇨ B₁ ∷a Bs
  /by-∀ : ∀ {A : Type m} {B Bs Bs' A'}
--    → [ A ]ˢ B₁ ⇨ B'
    → ty A ↑ #0 ⇨ A'
    → Bs' / A' by B ⇨ Bs
    → `∀ Bs' / A by `∀ B ⇨ `∀ Bs

infix 4 _/_at_by_⇨_
data _/_at_by_⇨_ : AppsType m → Type m → Fin (1 + m) →  Type (1 + m) → AppsType (1 + m) → Set where
  /by-nil : ∀ {A : Type m} {B k}
    → nil / A at k by B ⇨ nil
  /by-cons : ∀ {A : Type m} {B' Bs Bs' B₁ B₂ k}
    → [ k / A ]ˢ B₁ ⇨ B'
    → Bs' / A at k by B₂ ⇨ Bs
    → B' ∷a Bs' / A at k by (B₁ `→ B₂) ⇨ B₁ ∷a Bs
  /by-∀ : ∀ {A : Type m} {B Bs Bs' A' k}
    → ty A ↑ #0 ⇨ A'
    → Bs' / A' at (#S k) by B ⇨ Bs
    → `∀ Bs' / A at k by `∀ B ⇨ `∀ Bs

infix 4 ⟦_,_⟧→⟦_,_,_,_⟧

data ⟦_,_⟧→⟦_,_,_,_⟧ : Context n m → Type m → Apps n m → Context n m → AppsType m → Type m → Set where

  none-□ : ∀ {A}
    → ⟦ (Context n m ∋⦂ □) , A ⟧→⟦ nil , □ , nil , A ⟧

  none-τ : ∀ {A B}
    → ⟦ (Context n m ∋⦂ τ A) , B ⟧→⟦ nil , τ A , nil , B ⟧

  have-e : ∀ {Σ : Context n m} {e A B es A' B' Bs}
    → ⟦ Σ , B ⟧→⟦ es , A' , Bs , B' ⟧
    → ⟦ ([ e ]↝ Σ) , A `→ B ⟧→⟦ e ∷a es , A' , A ∷a Bs , B' ⟧

  have-t : ∀ {Σ Σ' : Context n m} {B A es B' Bs' C Bs}
    → (st : [ A ]ˢ B ⇨ B')
    → (sts : [ A ]ˢˢ Bs ⇨ Bs') -- new
    -- may be
    → ⟦ Σ , B' ⟧→⟦ es , Σ' , Bs' , C ⟧
    --  → (sts' : with Bs' / A by `∀ B ⇨ `∀ Bs
    -- sts' should derive sts
    → ⟦ ⟦ A ⟧↝ Σ , `∀ B ⟧→⟦ A ∷t es , Σ' , `∀ Bs , C ⟧

data ⟦_,_⟧⇒⟦_⟧ : Context n m → Type m → AppsType m → Set where

  none-□ : ∀ {A}
    → ⟦ (Context n m ∋⦂ □) , A ⟧⇒⟦ nil ⟧

  none-τ : ∀ {A B}
    → ⟦ (Context n m ∋⦂ τ A) , B ⟧⇒⟦ nil ⟧

  have-e : ∀ {Σ : Context n m} {e A B Bs}
    → ⟦ Σ , B ⟧⇒⟦  Bs ⟧
    → ⟦ ([ e ]↝ Σ) , A `→ B ⟧⇒⟦ A ∷a Bs ⟧

  have-t : ∀ {Σ : Context n m} {B A Bs}
    → ty-in-con Σ ↑ #0 ⇨ Σ'
    → ⟦ Σ' , B ⟧⇒⟦ Bs ⟧
    → ⟦ ⟦ A ⟧↝ Σ , `∀ B ⟧⇒⟦ `∀ Bs ⟧

infix 4 ⟦_,_⟧⇢⟦_,_,_⟧

data ⟦_,_⟧⇢⟦_,_,_⟧ : Context n m → Type m → Apps n m → Context n m → Type m → Set where

  none-□ : ∀ {A}
    → ⟦ (Context n m ∋⦂ □) , A ⟧⇢⟦ nil , □  , A ⟧

  none-τ : ∀ {A B}
    → ⟦ (Context n m ∋⦂ τ A) , B ⟧⇢⟦ nil , τ A , B ⟧

  have-e : ∀ {Σ : Context n m} {e A B es A' B'}
    → ⟦ Σ , B ⟧⇢⟦ es , A' , B' ⟧
    → ⟦ ([ e ]↝ Σ) , A `→ B ⟧⇢⟦ e ∷a es , A' , B' ⟧

  have-t : ∀ {Σ : Context n m} {B A es B' C}
    → [ A ]ˢ B ⇨ B'
    → ⟦ Σ , B' ⟧⇢⟦ es , Σ' , C ⟧
    → ⟦ ⟦ A ⟧↝ Σ , `∀ B ⟧⇢⟦ A ∷t es , Σ' , C ⟧

infix 4 ⟦_⟧⇒⟦_,_⟧

data ⟦_⟧⇒⟦_,_⟧ : Context n m → Apps n m → Context n m → Set where

  none-□ :
      ⟦ (Context n m ∋⦂ □) ⟧⇒⟦ nil , □ ⟧

  none-τ : ∀ {A}
    → ⟦ (Context n m ∋⦂ τ A) ⟧⇒⟦ nil , τ A ⟧

  have-e : ∀ {e es}
    → ⟦ Σ ⟧⇒⟦ es , Σ' ⟧
    → ⟦ [ e ]↝ Σ ⟧⇒⟦ e ∷a es , Σ' ⟧

  have-t : ∀ {es A}
    → ⟦ Σ ⟧⇒⟦ es , Σ' ⟧
    → ⟦ ⟦ A ⟧↝ Σ ⟧⇒⟦ A ∷t es , Σ' ⟧




