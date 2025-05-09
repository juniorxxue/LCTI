module Implicit.Annotatability.SystemF where

open import Implicit.Language.All hiding (Counter)
open import Implicit.Decl.Typing

private variable
  e₁′ : Term n m

data Counter : Set where
  Z : Counter
  ∞ : Counter
  𝕚 : Counter → Counter
  𝕔 : Counter → Counter

private variable
  p p' p₁ p₂ : Counter
  mp mp' mp₁ mp₂ : Maybe Counter

infix 3 _⊢_needFunT_
data _⊢_needFunT_ : Env n m → Type m → Counter → Set where
  ndft-var1 : Γ ∋= X
            → Γ ⊢ ‶ X needFunT Z
  ndft-var2 : Γ ∋^ X
            → Γ ⊢ ‶ X needFunT ∞
  ndft-arr1 : Γ ⊢c A
            → Γ ⊢ B needFunT p
            → Γ ⊢ A `→ B needFunT 𝕔 p
  ndft-arr2 : Γ ⊢o A
            → Γ ⊆ Δ w/t A
            → Δ ⊢ B needFunT p
            → Γ ⊢ A `→ B needFunT 𝕚 p
  ndft-∀ : Γ ,^ ⊢ A needFunT p
         → Γ ⊢ `∀ A needFunT p

data NEnv : ℕ → Set where
  ∅ : NEnv 0
  S : Counter → NEnv n → NEnv (1 + n)

private variable
  δ : NEnv n

data Conv : Env n m → NEnv n → Set where
  conv-Z : Conv ∅ ∅
  conv-S : Conv Γ δ
         → Γ ⊢ A needFunT p
         → Conv (Γ , A) (S p δ)

infix 3 _𝕄_
data _𝕄_ : Type m → Type m → Set where

  𝕄-arr : A `→ B 𝕄 A `→ B
  M-∀ : ⟦ T ⟧ A ⇘ A*
       → A* 𝕄 B `→ C
       → `∀ A 𝕄 B `→ C

infix 3 _⊢_needFun_
data _⊢_needFun_ : Env n m → Term n m → Counter → Set where
  ndf-var : Γ ∋ x ⦂ A
          → Γ ⋈ ⊢ A needFunT p
          → Γ ⊢ ` x needFun p
  ndf-lam : Γ , A ⊢ e needFun p
          → Γ ⊢ ƛ e needFun 𝕚 p
  ndf-app1 : Γ ⊢ e₁ needFun 𝕚 p
           → Γ ⊢ e₁ · e₂ needFun p
  ndf-app2 : Γ ⊢ e₁ needFun 𝕔 p
           → Γ ⊢ e₁ · e₂ needFun p

infix 3 _⊢_need_
data _⊢_need_ : Env n m → Term n m → Counter → Set where
  nd-lit : Γ ⊢ lit n need Z
  nd-var : Γ ⊢ ` x need Z
  nd-lam : Γ , A ⊢ e need p
         → Γ ⊢ ƛ e need 𝕚 p
  nd-app1 : Γ ⊢ e₁ needFun 𝕚 p
          → Γ ⊢ e₁ · e₂ need p
  nd-app2 : Γ ⊢ e₁ needFun 𝕔 p
          → Γ ⊢ e₁ · e₂ need p

infix 3 _⊢_⦂_⟶_
data _⊢_⦂_⟶_ : Env n m → Term n m → Type m → Term n m → Set where

  ela-lit : Γ ⊢ (lit n) ⦂ Int ⟶ (lit n)
  ela-var : Γ ∋ x ⦂ A
          → Γ ⊢ ` x ⦂ A ⟶ ` x
  ela-lam : Γ , A ⊢ e ⦂ B ⟶ e'
          → Γ ⊢ ƛ e ⦂ A `→ B ⟶ ƛ e'
  ela-app1 : (ndf : Γ ⊢ e₁ needFun 𝕔 p)
           → Γ ⊢ e₁ ⦂ A ⟶ e₁'
           → A 𝕄 B `→ C
           → Γ ⊢ e₂ ⦂ B ⟶ e₂'
           → Γ ⊢ e₁ · e₂ ⦂ C ⟶ e₁' · e₂'
  ela-app2 : (nd : Γ ⊢ e₂ need Z)
           → Γ ⊢ e₁ ⦂ A ⟶ e₁'
           → A 𝕄 B `→ C
           → Γ ⊢ e₂ ⦂ B ⟶ e₂'
           → Γ ⊢ e₁ · e₂ ⦂ C ⟶ e₁' · e₂'
  ela-app3 : (ndf : Γ ⊢ e₁ needFun 𝕚 p)
           → (nd : Γ ⊢ e₂ need 𝕚 p')
           → Γ ⊢ e₁ ⦂ A ⟶ e₁'
           → A 𝕄 B `→ C
           → Γ ⊢ e₂ ⦂ B ⟶ e₂'
           → (up : ↑tm0 e₁' ⇘ e₁′)
           → Γ ⊢ e₁ · e₂ ⦂ C ⟶ ((ƛ (e₁′ · ` #0)) ⦂ B `→ C) · e₂'


_ : ∅ , `∀ (‶ #0 `→ ‶ #0) ⊢ (` #0) · (lit 1) ⦂ Int ⟶ (` #0) · (lit 1)
_ = ela-app2 nd-lit (ela-var Z)
     (M-∀ (st-arr (st-var stx-eq) (st-var stx-eq)) 𝕄-arr) ela-lit

_ : ∅ , `∀ (‶ #0 `→ ‶ #0) ⊢ (` #0) · (ƛ ` #0) ⦂ Int `→ Int ⟶ (` #0) · ((ƛ ` #0) ⦂ Int `→ Int)
_ = {!!}


annotatability : Γ ⊢ e ⦂ A ⟶ e'
               → Γ ⊢ e need p
               → Γ ⊢ j # e' ⦂ A

annotatability-fun : Γ ⊢ e ⦂ A ⟶ e'
                   → Γ ⊢ e needFun p
                   → A 𝕄 B
                   → Γ ⊢ j # e' ⦂ B
