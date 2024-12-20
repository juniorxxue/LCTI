module Implicit.Complete where

open import Implicit.Language
open import Implicit.Decl renaming (find to d-find)
open import Implicit.Algo

private variable
  Γ : Env n m
  X : Fin m

infix 3 _⊢_~_

data _⊢_~_ : Env n m → Counter × Type m → Context n m → Set

data _⊢_~_ where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~I : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ □ ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ~ ([ e ]↝ Σ)

  ~C : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ τ A ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕔 j , A `→ B ⟩ ~ ([ e ]↝ Σ)

infix 3 _⊢_≊_
data _⊢_≊_ : Env n m → Type m → Type m → Set where

  ≊-int : Γ ⊢ Int ≊ Int

  ≊-var : Γ ⊢ ‶ X ≊ ‶ X

  ≊-left : Γ ∋ X := A
         → Γ ⊢ ‶ X ≊ A
    
  ≊-right : X := A ∈ Γ
          → Γ ⊢ A ≊ ‶ X

  ≊-arr : Γ ⊢ A ≊ A'
        → Γ ⊢ B ≊ B'
        → Γ ⊢ A `→ B ≊ A' `→ B'

  ≊-∀ : Γ ,∙ ⊢ A ≊ B
      → Γ ⊢ `∀ A ≊ `∀ B

≊-refl : ∀ {Ψ : SEnv n m} {A}
  → Ψ ⊢ A ≊ A
≊-refl {A = Int} = ≊-int
≊-refl {A = ‶ X} = ≊-var
≊-refl {A = A `→ A₁} = ≊-arr ≊-refl ≊-refl
≊-refl {A = `∀ A} = ≊-∀ ≊-refl

data JustTyp (Γ : Env n m) (Σ : Context n m) (e : Term n m) (A : Type m) : Set where
  typs : ∀ {B}
    → (⊢e : Γ ⊢ Σ ⇒ e ⇒ B)
    → (sim : 𝕎 Γ ⊢ A ≊ B)
    → JustTyp Γ Σ e A

data JustSub (Ψ' : SEnv n m) (Σ : Context n m) (A : Type m) : Set where
  subs : ∀ {Ψ B}
    → (ext : Ψ ⊆ Ψ')
    → (sub : Ψ ⊢ A ≤⁺ Σ ⊣ Ψ' ↪ B)
    → (sim : Ψ ⊢ A ≊ B)
    → JustSub Ψ' Σ A

complete' : ∀ {Γ : Env n m} {Σ j e A}
  → Γ ⊢ j # e ⦂ A
  → Γ ⊢ ⟨ j , A ⟩ ~ Σ
  → JustTyp Γ Σ e A

complete : ∀ {Γ : Env n m} {Σ j e A}
  → Γ ⊢ j # e ⦂ A
  → Γ ⊢ ⟨ j , A ⟩ ~ Σ
  → Γ ⊢ Σ ⇒ e ⇒ A

complete-≤ : ∀ {Γ : Env n m} {Σ j A B}
  → Γ ⊢ j # B ≤ A
  → Γ ⊢ ⟨ j , A ⟩ ~ Σ -- should be gen to consider existential vars
  → 𝕎 Γ ⊢ B ≤⁺ Σ ⊣ 𝕎 Γ ↪ A -- too strict


complete-≤' : ∀ {Γ : Env n m} {Ψ Σ j A B}
  → Γ ⊢ j # B ≤ A
  → Γ ⊢ ⟨ j , A ⟩ ~ Σ ~> Ψ
--  → Ψ ⊆ (𝕎 Γ) x (exvar(Ψ) in B) × someCon(j) -- w
  → Ψ ⊢ B ≤⁺ Σ ⊣ 𝕎 Γ ↪ A -- this is too loose, abtrary Ψ cannot prove simple cases
  
complete-inf : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ Z # e ⦂ A
  → Γ ⊢ □ ⇒ e ⇒ A
complete-inf ⊢e = complete ⊢e ~Z  

complete-chk : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ ∞ # e ⦂ A
  → Γ ⊢ τ A ⇒ e ⇒ A
complete-chk ⊢e = complete ⊢e ~∞

complete-≤-chk : ∀ {Γ : Env n m} {A B}
  → Γ ⊢ ∞ # B ≤ A
  → 𝕎 Γ ⊢ B ≤⁺ τ A ⊣ 𝕎 Γ ↪ A
complete-≤-chk B≤A = complete-≤ B≤A ~∞  

complete ⊢lit ~Z = ⊢lit
complete (⊢var x) ~Z = ⊢var x
complete (⊢ann ⊢e) ~Z = ⊢ann (complete-chk ⊢e)
complete (⊢lam₁ ⊢e) ~∞ = ⊢lam₁ (complete-chk ⊢e)
complete (⊢lam₂ ⊢e) (~I ⊢e' j~Σ) = {!!}
complete {Γ = Γ} (⊢app₁ ⊢e ⊢e₁) j~Σ = ⊢app (complete ⊢e (~C (complete-chk ⊢e₁) j~Σ))
complete (⊢app₂ ⊢e ⊢e₁) j~Σ = ⊢app (complete ⊢e (~I (complete-inf ⊢e₁) j~Σ))
complete (⊢sub ⊢e B≤A j≢Z) j~Σ = {!!}
complete (⊢tabs ⊢e) ~Z = ⊢tabs (complete-inf ⊢e)

complete-≤ s-refl j~Σ = {!!}
complete-≤ s-int j~Σ = {!!}
complete-≤ s-var j~Σ = {!!}
complete-≤ (s-arr₁ s s₁) j~Σ = {!!}
complete-≤ (s-arr₂ s s₁) j~Σ = {!!}
complete-≤ (s-arr₃ s) j~Σ = {!!}
complete-≤ (s-∀ s) j~Σ = {!!}
complete-≤ (s-∀l s x fd st₁ st₂) j~Σ = {!complete-≤ s ?!}
complete-≤ (s-var-l x s) j~Σ = {!!}
complete-≤ (s-var-r x s) j~Σ = {!!}

complete-≤' s-refl ~Z tf = {!!}
complete-≤' s-int ~∞ tf = {!!}
complete-≤' s-var j~Σ tf = {!!}
complete-≤' (s-arr₁ s s₁) j~Σ tf = {!!}
complete-≤' (s-arr₂ s s₁) j~Σ tf = {!!}
complete-≤' (s-arr₃ s) j~Σ tf = {!!}
complete-≤' (s-∀ s) j~Σ tf = {!!}
complete-≤' (s-∀l s x fd st₁ st₂) (~I ⊢e j~Σ) tf = s⁺-∀l {!!} (complete-≤' s {!!} (evar-sol tf)) {!!} {!!} st₁ st₂
complete-≤' (s-∀l s x fd st₁ st₂) (~C ⊢e j~Σ) tf = {!!}
complete-≤' (s-var-l x s) j~Σ tf = {!!}
complete-≤' (s-var-r x s) j~Σ tf = {!!}


-
^a |- Int <+ Int -| ^a=Int ~> Int
