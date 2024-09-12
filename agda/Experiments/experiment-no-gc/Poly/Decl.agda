module Poly.Decl where

open import Poly.Common

data Counter : Set where
  Z  : Counter
  ∞  : Counter
  S  : Counter → Counter
  Sτ : Counter → Counter

data NonZ : Counter → Set where
  nz-∞ : NonZ ∞
  nz-S : ∀ {j} → NonZ (S j)
  nz-Sτ : ∀ {j} → NonZ (Sτ j)

private
  variable
    Γ : Env n m

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

-- apply solutions in Env to a type

{-
infix 4 _⟦_⟧⟹'_
data _⟦_⟧⟹'_ : Env n m → Fin m → Type m → Set where
  slv'-, : ∀ {A B X}
    → Γ ⟦ X ⟧⟹' B
    → (Γ , A) ⟦ X ⟧⟹' B
  slv'-∙-Z : 
      (Γ ,∙) ⟦ #0 ⟧⟹' ‶ #0
  slv'-∙-S : ∀ {X A A'}
    → Γ ⟦ X ⟧⟹' A
    → A' ≡ ↑ty0 A
    → (Γ ,∙) ⟦ #S X ⟧⟹' A'
--    → (Γ ,∙) ⟦ #S X ⟧⟹' ↑ty0 A
  slv'-=-Z : ∀ {A A'}
    → A' ≡ ↑ty0 A
    → (Γ ,= A) ⟦ #0 ⟧⟹' A'
  slv'-=-S : ∀ {A X B B'}
    → Γ ⟦ X ⟧⟹' B
    → B' ≡ ↑ty0 B
    → (Γ ,= A) ⟦ #S X ⟧⟹' B'
-}    

infix 4 _⟦_⟧⟹_
data _⟦_⟧⟹_ : Env n m → Type m → Type m → Set where
  slv-int : Γ ⟦ Int ⟧⟹ Int
  slv-var : ∀ {X A A'}
--    → Γ ⟦ X ⟧⟹' A ⚠️
    → X := A ∈' Γ
    → Γ ⟦ A ⟧⟹ A'
    → Γ ⟦ ‶ X ⟧⟹ A'
  slv-arr : ∀ {A B A' B'}
    → Γ ⟦ A ⟧⟹ A'
    → Γ ⟦ B ⟧⟹ B'
    → Γ ⟦ A `→ B ⟧⟹ A' `→ B'
  slv-∀ : ∀ {A A'}
    → (Γ ,∙) ⟦ A ⟧⟹ A'
    → Γ ⟦ `∀ A ⟧⟹ `∀ A'

data bound : Type (1 + m) → Fin (1 + m) → Set where
  b-var : bound (Type (1 + m) ∋⦂ ‶ #0) #0
  b-arr₁ : ∀ {A : Type (1 + m)} {B k} → bound A k → bound (A `→ B) k
  b-arr₂ : ∀ {A : Type (1 + m)} {B k} → bound B k → bound (A `→ B) k
  b-∀ : ∀ {A : Type (2 + m)} {k} → bound A (#S k) → bound (`∀ A) k

-- find A k j
-- at j-th position of A type, should have a bound variable, example: |-1 forall a. a -> a <: Int -> Int
data find : Type (1 + m) → Fin (1 + m) → Counter → Set where
  f-∞ : ∀ {A : Type (1 + m)} {k} → find A k ∞ -- not sure
  f-Z : ∀ {A : Type (1 + m)} {k} → bound A k → find A k Z
  f-S₁ : ∀ {A : Type (1 + m)} {B k j}
    → bound A k
    → find (A `→ B) k (S j)
  f-S₂ : ∀ {A : Type (1 + m)} {B k j}
    → find B k j
    → find (A `→ B) k (S j)
  f-S₃ :  ∀ {A : Type (2 + m)} {k j}
    → find A (#S k) (S j)
    → find (`∀ A) k (S j)
  f-Sτ : ∀ {A : Type (2 + m)} {k j}
    → find A (#S k) j
    → find (`∀ A) k (Sτ j)
  
infix 3 _⊢_#_≤_
data _⊢_#_≤_ : Env n m → Counter → Type m → Type m → Set where
  s-refl : ∀ {A A'}
    → (ap : Γ ⟦ A ⟧⟹ A') -- I want to simplify this judgment, but worried about type variables case
    → Γ ⊢ Z # A ≤ A'
  s-int :
      Γ ⊢ ∞ # Int ≤ Int
  s-var : ∀ {X} 
    → Γ ⊢ ∞ # ‶ X ≤ ‶ X
  s-arr₁ : ∀ {A B C D}
    → Γ ⊢ ∞ # C ≤ A
    → Γ ⊢ ∞ # B ≤ D
    → Γ ⊢ ∞ # A `→ B ≤ C `→ D
  s-arr₂ : ∀ {j A B C D}
    → Γ ⊢ ∞ # C ≤ A
    → Γ ⊢ j # B ≤ D
    → Γ ⊢ S j # A `→ B ≤ C `→ D
  s-∀ : ∀ {A B}
    → Γ ,∙ ⊢ ∞ # A ≤ B
    → Γ ⊢ ∞ # `∀ A ≤ `∀ B
  s-∀l : ∀ {j A B C}
    → Γ ,= B ⊢ S j # A ≤ ↑ty0 C
-- we guess a solution of B here, we must make sure this B is provided from the counter
-- what we does is to make sure the all inputs matching the counter should at least have the quantifer contained
    → find A #0 (S j)
    → Γ ⊢ S j # `∀ A ≤ C
  s-∀lτ : ∀ {j A B C}
    → Γ ,= B ⊢ j # A ≤ ↑ty0 C 
    → Γ ⊢ Sτ j # `∀ A ≤ C
  -- two atomic rules, not sure where to use them
  s-var-l : ∀ {X A B}
    → X := B ∈ Γ
    → Γ ⊢ ∞ # B ≤ A
    → Γ ⊢ ∞ # ‶ X ≤ A
  s-var-r : ∀ {X A B}
    → X := B ∈ Γ
    → Γ ⊢ ∞ # A ≤ B
    → Γ ⊢ ∞ # A ≤ ‶ X

infix 3 _⊢_#_⦂_
data _⊢_#_⦂_ : Env n m → Counter → Term n m → Type m → Set where
  ⊢lit : ∀ {i} → Γ ⊢ Z # (lit i) ⦂ Int
  ⊢var : ∀ {x A}
    → lookup Γ x ≡ A
    → Γ ⊢ Z # ` x ⦂ A
  ⊢ann : ∀ {e A}
    → Γ ⊢ ∞ # e ⦂ A
    → Γ ⊢ Z # (e ⦂ A) ⦂ A
  ⊢lam₁ : ∀ {e A B}
    → Γ , A ⊢ ∞ # e ⦂ B
    → Γ ⊢ ∞ # ƛ e ⦂ A `→ B
  ⊢lam₂ : ∀ {e j A B}
    → Γ , A ⊢ j # e ⦂ B
    → Γ ⊢ S j # ƛ e ⦂ A `→ B
  ⊢app₁ : ∀ {e₁ e₂ j A B}
    → Γ ⊢ Z # e₁ ⦂ A `→ B
    → Γ ⊢ ∞ # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B
  ⊢app₂ : ∀ {e₁ e₂ j A B}
    → Γ ⊢ S j # e₁ ⦂ A `→ B
    → Γ ⊢ Z # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B
  ⊢sub : ∀ {e j A B}
    → Γ ⊢ Z # e ⦂ B
    → (B≤A : Γ ⊢ j # B ≤ A)
    → (j≢Z : NonZ j)
    → Γ ⊢ j # e ⦂ A
  ⊢tabs₁ : ∀ {e A}
    → Γ ,∙ ⊢ Z # e ⦂ A
    → Γ ⊢ Z # Λ e ⦂ `∀ A    
  ⊢tapp : ∀ {e j A B}
    → Γ ⊢ Sτ j # e ⦂ B
    → Γ ⊢ j # e [ A ] ⦂ B

idEnv : Env 1 0
idEnv = ∅ , `∀ (‶ #0 `→ ‶ #0)

id[Int]1 : idEnv ⊢ Z # ((` #0) [ Int ]) · (lit 1) ⦂ Int
id[Int]1 = ⊢app₁ (⊢tapp (⊢sub (⊢var refl) (s-∀lτ (s-refl (slv-arr (slv-var Z slv-int) (slv-var Z slv-int)))) nz-Sτ))
                 (⊢sub ⊢lit s-int nz-∞)

idExp : Term 0 0
idExp = Λ (((ƛ ` #0) ⦂ ‶ #0 `→ ‶ #0))

idExp[Int]1 : ∅ ⊢ Z # (idExp [ Int ]) · (lit 1) ⦂ Int
idExp[Int]1 = ⊢app₁ (⊢tapp (⊢sub (⊢tabs₁ (⊢ann (⊢lam₁ (⊢sub (⊢var refl) s-var nz-∞))))
                                 (s-∀lτ (s-refl (slv-arr (slv-var Z slv-int) (slv-var Z slv-int)))) nz-Sτ))
                    (⊢sub ⊢lit s-int nz-∞)

idExp[Int] : ∅ ⊢ Z # idExp [ Int ] ⦂ Int `→ Int
idExp[Int] = ⊢tapp (⊢sub (⊢tabs₁ (⊢ann (⊢lam₁ (⊢sub (⊢var refl) s-var nz-∞))))
                         (s-∀lτ (s-refl (slv-arr (slv-var Z slv-int) (slv-var Z slv-int)))) nz-Sτ)

-- implicit inst
id1 : idEnv ⊢ Z # (` #0) · (lit 1) ⦂ Int
id1 = ⊢app₂ (⊢sub (⊢var refl)
                  (s-∀l (s-arr₂ (s-var-r Z s-int) (s-refl (slv-var Z slv-int))) (f-S₁ b-var)) nz-S)
            ⊢lit

#1 : Fin (2 + m)
#1 = #S #0

_ : Env 3 3
_ = ∅ ,∙ , ‶ #0  ,∙ , ‶ #1 ,∙ , ‶ #0
