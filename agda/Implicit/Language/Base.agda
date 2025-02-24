module Implicit.Language.Base where

open import Implicit.Language.Prelude public

infixr 5  ƛ_
infixl 7  _·_
infix  9  `_
infixr 5  Λ_
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

variable
  e  e' e* : Term n m
  e% e%' e₁% e₂% : Term n m
  e₁  e₂  : Term n m
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
  Γ Γ' Γ'' Γ₁ Γ₂ Γ₃ Γ* : Env n m
  Γ% : Env n m
  Δ Δ' Δ₁ Δ₂ : Env n m
  Ψ Ω : Env n m

data TypEnv : Env n m → Set where
  Z⋈ : TypEnv ∅
  S, : TypEnv Γ
     → TypEnv (Γ , A)
  S= : TypEnv Γ
     → TypEnv (Γ ,= B)
  S∙ : TypEnv Γ
     → TypEnv (Γ ,∙)
  S^ : TypEnv Γ
     → TypEnv (Γ ,^)

data SubEnv : Env n m → Set where
  Z⋈ : TypEnv Γ
     → SubEnv (Γ ⋈)
  S, : SubEnv Γ
     → SubEnv (Γ , A)
  S= : SubEnv Γ
     → SubEnv (Γ ,= B)
  S∙ : SubEnv Γ
     → SubEnv (Γ ,∙)
  S^ : SubEnv Γ
     → SubEnv (Γ ,^)


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

data Counter : Set where
  Z : Counter
  ∞ : Counter
  𝕚 : Counter → Counter
  𝕔 : Counter → Counter

variable
  j j′ j″ : Counter

data NonZ : Counter → Set where
  nz-∞ : NonZ ∞
  nz-I : NonZ (𝕚 j)
  nz-C : NonZ (𝕔 j)

data 𝕚𝕔 : Counter → Set where
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
