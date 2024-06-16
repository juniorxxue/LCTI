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

  
private
  variable
    Γ Γ' Γ₁ Γ₂ Γ₃ : Env n m
    Σ : Context n m

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
    → Γ ⊢ τ A ⇒ e ⇒ A'
    → Γ ⊢ B ≤ Σ ⊣ Γ' ↪ D
    → Γ ⊢ (A `→ B) ≤ ([ e ]↝ Σ) ⊣ Γ' ↪ A `→ D

  s-∀ : ∀ {A B C}
    → Γ ,∙ ⊢ A ≤ τ B ⊣ Γ' ,∙ ↪ C
    → Γ ⊢ `∀ A ≤ τ (`∀ B) ⊣ Γ' ↪ `∀ C
    
  s-∀-t : ∀ {A B C}
    → Γ ,= B ⊢ A ≤ ↑tyΣ0 Σ ⊣ Γ' ,= B ↪ C
    → Γ ⊢ `∀ A ≤ (⟦ B ⟧↝ Σ) ⊣ Γ' ↪ [ B ]ˢ C

----------------------------------------------------------------------
--+                            Examples                            +--
----------------------------------------------------------------------
idEnv : Env 1 0
idEnv = ∅ , `∀ (‶ #0 `→ ‶ #0)

sub-id[Int]1 : ∀ {Γ : Env n m} → Γ ⊢ `∀ ‶ #0 `→ ‶ #0 ≤ ⟦ Int ⟧↝ [ lit 1 ]↝ □ ⊣ Γ ↪ Int `→ Int
sub-id[Int]1 {Γ = Γ} = s-∀-t (s-term-c (⊢sub ⊢lit ne-τ gc-i (s-ex-r= Z s-int)) s-empty)


sub-id[Int] : ∀ {Γ : Env n m} → Γ ⊢ `∀ ‶ #0 `→ ‶ #0 ≤ ⟦ Int ⟧↝ □ ⊣ Γ ↪ Int `→ Int
sub-id[Int] = s-∀-t s-empty

id[Int]1 : idEnv ⊢ □ ⇒ ((` #0) [ Int ]) · (lit 1) ⇒ Int
id[Int]1 = ⊢app (⊢tapp (⊢sub (⊢var refl)
                             ne-tapp
                             gc-var
                             sub-id[Int]1))
idExp : Term 0 0
idExp = Λ (((ƛ ` #0) ⦂ ‶ #0 `→ ‶ #0))

idExp[Int]1 : ∅ ⊢ □ ⇒ (idExp [ Int ]) · (lit 1) ⇒ Int
idExp[Int]1 = ⊢app (⊢tapp (⊢sub
                            (⊢tabs₁ (⊢ann (⊢lam₁ (⊢sub (⊢var refl) ne-τ gc-var s-var)))) ne-tapp gc-tlam (sub-id[Int]1 {Γ = ∅})))

idExp[Int] : ∅ ⊢ □ ⇒ idExp [ Int ] ⇒ Int `→ Int
idExp[Int] = ⊢tapp (⊢sub (⊢tabs₁ (⊢ann (⊢lam₁ (⊢sub (⊢var refl) ne-τ gc-var s-var)))) ne-tapp gc-tlam sub-id[Int])


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




