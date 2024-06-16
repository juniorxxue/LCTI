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
    
infix 3 _⊢_#_≤_
data _⊢_#_≤_ : Env n m → Counter → Type m → Type m → Set where
  s-refl : ∀ {A}
    → Γ ⊢ Z # A ≤ A
  s-int :
      Γ ⊢ ∞ # Int ≤ Int
  s-var : ∀ {X} 
    → Γ ⊢ ∞ # ‶ X ≤ ‶ X
  s-arr₁ : ∀ {A B C D}
    → Γ ⊢ ∞ # C ≤ A
    → Γ ⊢ ∞ # B ≤ D
    → Γ ⊢ ∞ # A `→ B ≤ C `→ D
{-    
  s-arr₂ : ∀ {j A B C D}
    → Γ ⊢ ∞ # C ≤ A
    → Γ ⊢ j # B ≤ D
    → Γ ⊢ S j # A `→ B ≤ C `→ D
-}    
  s-∀ : ∀ {A B}
    → Γ ,∙ ⊢ ∞ # A ≤ B
    → Γ ⊢ ∞ # `∀ A ≤ `∀ B
  s-∀lτ : ∀ {j A B C}
    → Γ ,= B ⊢ j # A ≤ C
    → Γ ⊢ Sτ j # `∀ A ≤ [ B ]ˢ C
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
  ⊢app₁ : ∀ {e₁ e₂ A B}
    → Γ ⊢ Z # e₁ ⦂ A `→ B
    → Γ ⊢ ∞ # e₂ ⦂ A
    → Γ ⊢ Z # e₁ · e₂ ⦂ B
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
id[Int]1 = ⊢app₁ (⊢tapp (⊢sub (⊢var refl) (s-∀lτ {B = Int} s-refl) nz-Sτ))
                 (⊢sub ⊢lit s-int nz-∞)

idExp : Term 0 0
idExp = Λ (((ƛ ` #0) ⦂ ‶ #0 `→ ‶ #0))

idExp[Int]1 : ∅ ⊢ Z # (idExp [ Int ]) · (lit 1) ⦂ Int
idExp[Int]1 = ⊢app₁ (⊢tapp (⊢sub (⊢tabs₁ (⊢ann (⊢lam₁ (⊢sub (⊢var refl) s-var nz-∞))))
                                 (s-∀lτ {B = Int} s-refl) nz-Sτ))
                    (⊢sub ⊢lit s-int nz-∞)

idExp[Int] : ∅ ⊢ Z # idExp [ Int ] ⦂ Int `→ Int
idExp[Int] = ⊢tapp (⊢sub (⊢tabs₁ (⊢ann (⊢lam₁ (⊢sub (⊢var refl) s-var nz-∞))))
                         (s-∀lτ {B = Int} s-refl) nz-Sτ)

#1 : Fin (2 + m)
#1 = #S #0

_ : Env 3 3
_ = ∅ ,∙ , ‶ #0  ,∙ , ‶ #1 ,∙ , ‶ #0
