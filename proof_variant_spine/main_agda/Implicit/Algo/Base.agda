module Implicit.Algo.Base where

open import Implicit.Language.All

open import Implicit.Algo.Constructs.Syntax public
open import Implicit.Algo.Constructs.Shift public
open import Implicit.Algo.Constructs.Subst public
open import Implicit.Algo.Constructs.Lookup public

infix 3 _⊢_⌞_⌝_⊣_
data _⊢_⌞_⌝_⊣_ : Env n m → Type m → Polar → Type m → Env n m → Set where
  s-int :
      (regΓ : SRegular Δ)
    → Δ ⊢ Int ⌞ ≤ ⌝ Int ⊣ Δ

  s-var-∙ :
      (regΓ : SRegular Δ)
    → (inΔ : Δ ∋∙ X)
    → Δ ⊢ (‶ X) ⌞ ≤ ⌝ (‶ X) ⊣ Δ

  s-ex-l^ :
--      (x-in : Δ ∋^ X)
--    → (regA : Δ ⊢r A)
      (inst : [ A / X ] Δ ⟹ Ψ)
    → Δ ⊢ ‶ X ⌞ ≤⁺ ⌝ A ⊣ Ψ

  s-ex-r^ :
--      (x-in : Δ ∋^ X) -- implied by inst
--    → (regA : Γ ⊢r A) -- implied by the inst
      (inst : [ A / X ] Δ ⟹ Ψ)
    → Δ ⊢ A ⌞ ≤⁻ ⌝ (‶ X) ⊣ Ψ

  s-ex-l= :
      (regΓ : SRegular Δ)
    → (x-in : Δ ∋ X := A)
    → Δ ⊢ ‶ X ⌞ ≤⁺ ⌝ A ⊣ Δ

  s-ex-r= :
      (regΓ : SRegular Δ)
    → (x-in : Δ ∋ X := A)
    → Δ ⊢ A ⌞ ≤⁻ ⌝ (‶ X) ⊣ Δ

  s-arr :
      Δ ⊢ C ⌞ ⋆ ≤ ⌝ A ⊣ Ω
    → Ω ⊢ B ⌞ ≤ ⌝ D ⊣ Ψ
    → Δ ⊢ A `→ B ⌞ ≤ ⌝ (C `→ D) ⊣ Ψ

  s-∀ :
      Δ ,∙ ⊢ A ⌞ ≤ ⌝ B ⊣ Ψ ,∙
    → Δ ⊢ `∀ A ⌞ ≤ ⌝ (`∀ B) ⊣ Ψ

-- degenerate version for negation

infix 3 _~pk~_w/_

data _~pk~_w/_ : Type m → Context n m → Fin m → Set where
  pk-type : (inA : k ε A)
          → A ~pk~ (Context n m ∋⦂ τ B) w/ k
  pk-term : B ~pk~ Σ w/ k
          → A `→ B ~pk~ [ e ]↝ Σ w/ k
  pk-∀l   : A ~pk~ [ e' ]↝ Σ' w/ (#S k)
          → (upΣ : ↑tyᶜ0 Σ ⇘ Σ')
          → (upe : ↑tyᵉ0 e ⇘ e')
          → `∀ A ~pk~ [ e ]↝ Σ w/ k
  pk-tapp : A ~pk~ Σ' w/ (#S k)
          → (upΣ : ↑tyᶜ0 Σ ⇘ Σ')
          → `∀ A ~pk~ (B ⓪↝ Σ) w/ k



infix 3 _~~pk~~_w/_↪_
infix 3 _~pk~_w/_↪_

data _~~pk~~_w/_↪_ : Type m → Type m → Fin m → Type m → Set where
  pk-var-l : ‶ k ~~pk~~ A w/ k ↪ A
  pk-arr-l : A ~~pk~~ C w/ k ↪ E -- note, no contra-variant here for simplicity
           → A `→ B ~~pk~~ C `→ D w/ k ↪ E
  pk-arr-r : B ~~pk~~ D w/ k ↪ E
           → A `→ B ~~pk~~ C `→ D w/ k ↪ E
  pk-∀     : A ~~pk~~ B w/ (#S k) ↪ C'
           → (upC : ↑ty0 C ⇘ C')
           → `∀ A ~~pk~~ `∀ B w/ k ↪ C

data _~pk~_w/_↪_ : Type m → Context n m → Fin m → Type m → Set where
  pk-type : A ~~pk~~ B w/ k ↪ C
          → A ~pk~ (Context n m ∋⦂ τ B) w/ k ↪ C
  pk-term : B ~pk~ Σ w/ k ↪ C
          → A `→ B ~pk~ [ e ]↝ Σ w/ k ↪ C
  pk-∀l   : A ~pk~ [ e' ]↝ Σ' w/ (#S k) ↪ C'
          → (upΣ : ↑tyᶜ0 Σ ⇘ Σ')
          → (upe : ↑tyᵉ0 e ⇘ e')
          → (upC : ↑ty0 C ⇘ C')
          → `∀ A ~pk~ [ e ]↝ Σ w/ k ↪ C
  pk-tapp : A ~pk~ Σ' w/ (#S k) ↪ C'
          → (upC : ↑ty0 C ⇘ C')
          → (upΣ : ↑tyᶜ0 Σ ⇘ Σ')
          → `∀ A ~pk~ (B ⓪↝ Σ) w/ k ↪ C


infix 3 _⊢_⇒_⇒_
infix 3 _⊢_≤⁺_⊣_↪_
infix 3 _⊨_⟹_

data _⊢_⇒_⇒_ : Env n m → Context n m → Term n m → Type m → Set
data _⊢_≤⁺_⊣_↪_ : Env n m → Type m → Context n m → Env n m → Type m → Set
data _⊨_⟹_ : Env n m → Context n m → Type m → Set

data _⊢_⇒_⇒_ where

  ⊢lit : ∀ {num : ℕ}
    → (regΓ : TRegular Γ)
    → Γ ⊢ □ ⇒ lit num ⇒ Int

  ⊢var :
      (regΓ : TRegular Γ)
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊢ □ ⇒ ` x ⇒ A

  ⊢ann :
      Γ ⊢ τ A ⇒ e ⇒ B
    → Γ ⊢ □ ⇒ e ⦂ A ⇒ A

  ⊢app :
      Γ ⊢ [ e₂ ]↝ Σ ⇒ e₁ ⇒ A `→ B
    → Γ ⊢ Σ ⇒ e₁ · e₂ ⇒ B

  ⊢lam₁ :
      Γ , A ⊢ τ B ⇒ e ⇒ C
    → Γ ⊢ τ (A `→ B) ⇒ ƛ e ⇒ A `→ C

  ⊢lam₂ :
      Γ ⊢ □ ⇒ e₂ ⇒ A
    → (up-c : ↑tmᶜ0 Σ ⇘ Σ')
    → Γ , A ⊢ Σ' ⇒ e ⇒ B
    → Γ ⊢ [ e₂ ]↝ Σ ⇒ ƛ e ⇒ A `→ B

  ⊢sub :
      Γ ⊢ □ ⇒ g ⇒ A
    → (ne : NonEmpty Σ)
    → (gc : GenericConsumer g)
    → (s : Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ B)
    → Γ ⊢ Σ ⇒ g ⇒ B

  ⊢tabs :
      Γ ,∙ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ □ ⇒ Λ e ⇒ `∀ A

  ⊢tabs-τ :
      Γ ,∙ ⊢ τ B ⇒ e ⇒ A
    → Γ ⊢ τ (`∀ B) ⇒ Λ e ⇒ `∀ A

  ⊢tapp : ∀ {pB}
    → Γ ⊢ A ⓪↝ Σ ⇒ e ⇒ `∀ B
    → (upB : ↑ty0 pB ⇘ B)
    → Γ ⊢ Σ ⇒ e ⓪ A ⇒ pB

data _⊢_≤⁺_⊣_↪_ where

  s-empty :
      (regΓ : SRegular Δ)
    → (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊢ A ≤⁺ □ ⊣ Δ ↪ A%

  s-type :
      (ss : Δ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Ψ)
    → Δ ⊢ A ≤⁺ (τ B) ⊣ Ψ ↪ B

  s-term-c :
      (cloA : Δ ⊢c A)
    → (ap : Δ ≫ A ⇘ A%)
    → (⊢e : 𝕣 Δ ⊢ τ A% ⇒ e ⇒ A')
    → Δ ⊢ B ≤⁺ Σ ⊣ Ψ ↪ D
    → Δ ⊢ (A `→ B) ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ A% `→ D

  s-term-o :
      (opnA : Δ ⊢o A)
    → (⊢e : 𝕣 Δ ⊢ □ ⇒ e ⇒ C)
    → (ss : Δ ⊢ C ⌞ ≤⁻ ⌝ A ⊣ Ω)
    → Ω ⊢ B ≤⁺ Σ ⊣ Ψ ↪ D
    → Δ ⊢ A `→ B ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D

  s-∀l-y :
      (pk : A ~pk~ ([ e' ]↝ Σ') w/ #0 ↪ B')
    → (upB : ↑ty0 B ⇘ B')
    → Δ ,= B ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,= B ↪ C' `→ D'
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D

  s-∀l-n-y :
      (¬pk : ¬ (A ~pk~ ([ e' ]↝ Σ') w/ #0))
    → Δ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,= B ↪ C' `→ D'
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D

  s-∀l-n-n :
      (¬pk : ¬ (A ~pk~ ([ e' ]↝ Σ') w/ #0))
    → Δ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,^ ↪ C' `→ D'
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D

  s-tapp :
      Δ ,= B ⊢ A ≤⁺ Σ' ⊣ Ψ ,= B ↪ C
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → Δ ⊢ `∀ A ≤⁺ (B ⓪↝ Σ) ⊣ Ψ ↪ `∀ C

  s-svar-term :
      Δ ∋ X := A
    → Δ ⊢ A ≤⁺ ([ e ]↝ Σ) ⊣ Δ ↪ B `→ C
    → Δ ⊢ ‶ X ≤⁺ ([ e ]↝ Σ) ⊣ Δ ↪ B `→ C

  s-svar-tapp :
      Δ ∋ X := A
    → Δ ⊢ A ≤⁺ (B ⓪↝ Σ) ⊣ Δ ↪ `∀ C
    → Δ ⊢ ‶ X ≤⁺ (B ⓪↝ Σ) ⊣ Δ ↪ `∀ C

  s-evar-infers :
      (infs : 𝕣 Δ ⊨ [ e ]↝ Σ ⟹ A)
    → (inst : [ A / X ] Δ ⟹ Ψ) -- implies Γ ∋^k
    → Δ ⊢ ‶ X ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ A

data _⊨_⟹_ where
  infs-z : (regΓ : TRegular Γ)
         → (regA : Γ ⊢r A)
         → Γ ⊨ τ A ⟹ A
  infs-s : (⊢e : Γ ⊢ □ ⇒ e ⇒ A)
         → Γ ⊨ Σ ⟹ B
         → Γ ⊨ [ e ]↝ Σ ⟹ A `→ B
