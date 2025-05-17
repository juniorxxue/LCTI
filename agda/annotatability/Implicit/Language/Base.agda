module Implicit.Language.Base where

open import Implicit.Language.Prelude public

infixr 5  ƛ_
infixl 7  _·_
infix  9  `_
infixr 5  Λ_
infixl 5  _⓪_
infix  5  _⦂_

infix  9  ‶_
infixr 8  _`→_
infixr 8  `∀_

data Type : ℕ → Set where
  Int    : Type m
  ‶_     : (X : Fin m) → Type m
  _`→_   : (A : Type m) → (B : Type m) → Type m
  `∀_    : (A : Type (1 + m)) → Type m


variable
  A  B  C  D  E  T  : Type m
  A% B% C% D% E% T% : Type m
  A%' B%' C%' D%'   : Type m
  A* B* C* D* E* T* : Type m
  A*' B*' C*' D*' E*' T*' : Type m
  A' B' C' D' E' T' : Type m
  A₁ B₁ C₁ D₁ E₁ T₁ : Type m
  A₂ B₂ C₂ D₂ E₂ T₂ : Type m
  A₃ B₃ C₃ D₃ E₃ T₃ : Type m

data Term : ℕ → ℕ → Set where
  lit      : (i : ℕ) → Term n m
  `_       : (x : Fin n) → Term n m
  ƛ_       : (e : Term (1 + n) m) → Term n m
  _·_      : (e₁ : Term n m) → (e₂ : Term n m) → Term n m
  _⦂_      : (e : Term n m) → (A : Type m) → Term n m
  Λ_       : (e : Term n (1 + m)) → Term n m
  _⓪_      : (e : Term n m) → (A : Type m) → Term n m

variable
  e  e' e* : Term n m
  e% e%' e₁% e₂% : Term n m
  e₁  e₂  e₃ e₄ : Term n m
  e₁' e₂' : Term n m
  g : Term n m -- reserved for generic consumers

----------------------------------------------------------------------
--+                          Environments                          +--
----------------------------------------------------------------------

infixl 4 _,_
infixl 4 _,∙
infixl 4 _,^
infixl 4 _,=_
infixl 4 _⋈

data Env : ℕ → ℕ → Set where
  ∅     : Env 0 0
  _,_   : Env n m → (A : Type m) → Env (1 + n) m
  _,^   : Env n m → Env n (1 + m)
  _,∙   : Env n m → Env n (1 + m)
  _,=_  : Env n m → (A : Type m) → Env n (1 + m)
  _⋈    : Env n m → Env n m

variable
  Γ Γ' Γ'' Γ₁ Γ₂ Γ₃ Γ* Γ% : Env n m -- typing env
  Δ Δ' Δ₁ Δ₂ Ψ Ω Ψ' Ω' : Env n m -- subtyping env

data TEnv : Env n m → Set where
  Z⋈ : TEnv ∅
  S, : TEnv Γ
     → TEnv (Γ , A)
  S= : TEnv Γ
     → TEnv (Γ ,= B)
  S∙ : TEnv Γ
     → TEnv (Γ ,∙)
  S^ : TEnv Γ
     → TEnv (Γ ,^)

data SEnv : Env n m → Set where
  Z⋈ : TEnv Γ
     → SEnv (Γ ⋈)
  S, : SEnv Δ
     → SEnv (Δ , A)
  S= : SEnv Δ
     → SEnv (Δ ,= B)
  S∙ : SEnv Δ
     → SEnv (Δ ,∙)
  S^ : SEnv Δ
     → SEnv (Δ ,^)

𝕣 : Env n m → Env n m
𝕣 ∅ = ∅
𝕣 (Γ , A) = 𝕣 Γ , A
𝕣 (Γ ,^) = 𝕣 Γ ,^
𝕣 (Γ ,∙) = 𝕣 Γ ,∙
𝕣 (Γ ,= A) = 𝕣 Γ ,= A
𝕣 (Γ ⋈) = Γ

‶-injective : ‶ X ≡ ‶ Y
            → X ≡ Y
‶-injective refl = refl

infixr 9 𝕥₍_₎_
data Counter : ℕ → Set where
  Z : Counter m
  ∞ : Counter m
  𝕚 : Counter m → Counter m
  𝕔 : Counter m → Counter m
  𝕥₍_₎_ : Type m → Counter m → Counter m

variable
  j j′ j″  : Counter m
  j' j'' : Counter m
  j₁ j₂ j₃ : Counter m

data NonZ : Counter m → Set where
  nz-∞ : NonZ (Counter m ∋⦂ ∞)
  nz-I : NonZ (𝕚 j)
  nz-C : NonZ (𝕔 j)
  nz-T : NonZ (𝕥₍ A ₎ j)

data 𝕚𝕔 : Counter m → Set where
  case-𝕚 : 𝕚𝕔 (𝕚 j)
  case-𝕔 : 𝕚𝕔 (𝕔 j)

data Polar : Set where
  ≤⁺ ≤⁻ : Polar

⋆ : Polar → Polar
⋆ ≤⁺ = ≤⁻
⋆ ≤⁻ = ≤⁺

variable
  ≤ : Polar

data GenericConsumer : Term n m → Set where
  gc-i : ∀ {i} → GenericConsumer (Term n m ∋⦂ lit i)
  gc-var : ∀ {x} → GenericConsumer (Term n m ∋⦂ ` x)
  gc-ann : ∀ {e : Term n m} {A} → GenericConsumer (e ⦂ A)
  gc-tlam : ∀ {e : Term n (1 + m)} → GenericConsumer (Λ e)
