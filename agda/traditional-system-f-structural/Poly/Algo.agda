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
infix 3 _⊢_≤_⊣_↪_

data _⊢_⇒_⇒_ : Env n m → Context n m → Term n m → Type m → Set
-- we cannot syntactically distinguish the result type here, which should contain unsolved variables
data _⊢_≤_⊣_↪_ : Env n m → Type m → Context n m → Env n m → Type m → Set

data _⊢_⇒_⇒_ where

  ⊢lit : ∀ {i}
    → Γ ⊢ □ ⇒ lit i ⇒ Int

  ⊢var : ∀ {x A}
    → (x∈Γ : lookup Γ x ≡ A)
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

  ⊢sub : ∀ {g A B}
    → Γ ⊢ □ ⇒ g ⇒ A          --- Γ ⊢ Z # e : A
    → (¬□ : NonEmpty Σ)
    → (gc : GenericConsumer g)
    → (s : Γ ⊢ A ≤ Σ ⊣ Γ' ↪ B)    --- Γ ⊢ j # A ≤ B
    → Γ ⊢ Σ ⇒ g ⇒ B          --- Γ ⊢ j # e ∶ B

  -- design choices here,
  -- (1) we maybe need a checking for tabs
  -- (2) we need a context (must have, if we intend to be consistent)
  ⊢tabs₁ : ∀ {e A}
    → Γ ,∙ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ □ ⇒ Λ e ⇒ `∀ A

  ⊢tapp : ∀ {e A B}
    → Γ ⊢ ⟦ A ⟧↝ Σ ⇒ e ⇒ B
    → Γ ⊢ Σ ⇒ e [ A ] ⇒ B
  
data _⊢_≤_⊣_↪_ where
  s-int :
      Γ ⊢ Int ≤ τ Int ⊣ Γ ↪ Int

  s-empty : ∀ {A}
    → Γ ⊢ A ≤ □ ⊣ Γ ↪ A

  s-var : ∀ {X}
    → Γ ⊢ ‶ X ≤ τ (‶ X) ⊣ Γ ↪ ‶ X

  s-ex-l= : ∀ {A A' B X}
    → X := B ∈ Γ
    → Γ ⊢ B ≤ τ A ⊣ Γ' ↪ A'
    → Γ ⊢ ‶ X ≤ τ A ⊣ Γ' ↪ A'

  s-ex-r= : ∀ {A A' B X}
    → X := B ∈ Γ
    → Γ ⊢ A ≤ τ B ⊣ Γ' ↪ A'
    → Γ ⊢ A ≤ τ (‶ X) ⊣ Γ' ↪ (‶ X)

  s-arr : ∀ {A B C D A' D'}
    → Γ₁ ⊢ C ≤ τ A ⊣ Γ₂ ↪ A'
    → Γ₂ ⊢ B ≤ τ D ⊣ Γ₃ ↪ D'
    → Γ₁ ⊢ A `→ B ≤ τ (C `→ D) ⊣ Γ₃ ↪ (C `→ D)

  s-term-c : ∀ {A B A' D e}
    → (⊢e : Γ ⊢ τ A ⇒ e ⇒ A')
    → Γ ⊢ B ≤ Σ ⊣ Γ' ↪ D
    → Γ ⊢ (A `→ B) ≤ ([ e ]↝ Σ) ⊣ Γ' ↪ A `→ D

  s-∀ : ∀ {A B C}
    → Γ ,∙ ⊢ A ≤ τ B ⊣ Γ' ,∙ ↪ C
    → Γ ⊢ `∀ A ≤ τ (`∀ B) ⊣ Γ' ↪ `∀ C
    
  s-∀-t : ∀ {A B C C'}
    → (↑Σ : ty-in-con Σ ↑ #0 ⇨ Σ') -- a type shift of the context
    → Γ ,= B ⊢ A ≤ Σ' ⊣ Γ' ,= B ↪ C
    → (st : [ B ]ˢ C ⇨ C')
    → Γ ⊢ `∀ A ≤ (⟦ B ⟧↝ Σ) ⊣ Γ' ↪ C'

----------------------------------------------------------------------
--+                           Splitting                            +--
----------------------------------------------------------------------

infix 4 ⟦_,_⟧→⟦_,_,_,_⟧

data ⟦_,_⟧→⟦_,_,_,_⟧ : Context n m → Type m → Apps n m → Context n m → AppsType m → Type m → Set where

  none-□ : ∀ {A}
    → ⟦ (Context n m ∋⦂ □) , A ⟧→⟦ nil , □ , nil , A ⟧

  none-τ : ∀ {A B}
    → ⟦ (Context n m ∋⦂ τ A) , B ⟧→⟦ nil , τ A , nil , B ⟧

  have-e : ∀ {Σ : Context n m} {e A B es A' B' Bs}
    → ⟦ Σ , B ⟧→⟦ es , A' , Bs , B' ⟧
    → ⟦ ([ e ]↝ Σ) , A `→ B ⟧→⟦ e ∷a es , A' , A ∷a Bs , B' ⟧

  have-t : ∀ {Σ : Context n m} {B A es A' B' Bs}
    → ⟦ Σ , B ⟧→⟦ es , A' , Bs , B' ⟧
    → ⟦ ⟦ A ⟧↝ Σ , B ⟧→⟦ A ∷t es , A' , Bs , B' ⟧




