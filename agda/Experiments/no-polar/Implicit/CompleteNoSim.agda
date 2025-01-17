module Implicit.CompleteNoSim where

open import Implicit.Language
open import Implicit.Decl renaming (find to d-find)
open import Implicit.Algo
-- open import Implicit.Algo.Properties.Subsumption

postulate
  subsumption0 : Γ ⊢ □ ⇒ e ⇒ A
             → Γ ⊢ A ≤ Σ ⊣ Γ ↪ A'
             → Γ ⊢ Σ ⇒ e ⇒ A'

infix 3 _⊢_~_

data _⊢_~_ : Env n m → Counter × Type m → Context n m → Set where

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

postulate
  ~weaken,0 : Γ ⊢ ⟨ j , B ⟩ ~ Σ
            → ↑tmᶜ0 Σ ⇘ Σ'
            → Γ , A ⊢ ⟨ j , B ⟩ ~ Σ'

data Transfer : Env n m → Env n m → Type m → Counter → Set where

  base : Transfer ∅ ∅ A j
  uvar : Transfer Γ Δ (`∀ A) j
       → Transfer (Γ ,∙) (Δ ,∙) A j
  var : Transfer Γ Δ A j
      → Transfer (Γ , B) (Δ , B) A j
  evar : Transfer Γ Δ (`∀ A) j
       → Transfer (Γ ,^) (Δ ,^) A j
  evar-sol : Transfer Γ Δ (`∀ A) j
           → d-find A #0 j
           → Transfer (Γ ,^) (Δ ,= B) A j
  svar : Transfer Γ Δ (`∀ A) j
        → Transfer (Γ ,= B) (Δ ,= B) A j

_ : Transfer (∅ , Int ,^ ,∙) (∅ , Int ,= Int ,∙) (‶ #1 `→ ‶ #1) (𝕚 Z)
_ = uvar (evar-sol (var base) (f-∀ (f-arr-𝕚-l ε-var)))

transfer-z : Transfer Δ Δ A Z
transfer-z {Δ = ∅} = base
transfer-z {Δ = Δ , A} = var transfer-z
transfer-z {Δ = Δ ,^} = evar transfer-z
transfer-z {Δ = Δ ,∙} = uvar transfer-z
transfer-z {Δ = Δ ,= A} = svar transfer-z

transfer-int : Transfer Δ Δ Int ∞
transfer-int {Δ = ∅} = base
transfer-int {Δ = Δ , A} = var transfer-int
transfer-int {Δ = Δ ,^} = evar {!!}
transfer-int {Δ = Δ ,∙} = uvar {!!}
transfer-int {Δ = Δ ,= A} = svar {!!}


data JustSub (Δ : Env n m) (Σ : Context n m) (A : Type m) (B : Type m) (j : Counter) : Set where
  subs : ∀ {Γ C}
    → (ext : Transfer Γ Δ A j)
    → (sub : Γ ⊢ A ≤ Σ ⊣ Δ ↪ C)
    → JustSub Δ Σ A B j

complete : Γ ⊢ j # e ⦂ A
         → Γ ⊢ ⟨ j , A ⟩ ~ Σ
         → Γ ⊢ Σ ⇒ e ⇒ A

complete-∞ : Γ ⊢ ∞ # e ⦂ A
           → Γ ⊢ τ A ⇒ e ⇒ A
complete-∞ ⊢e with complete ⊢e ~∞
... | typs ⊢e₁ sim with ⊢id0 ⊢e₁
... | refl = ⊢e₁

complete-s : Δ ⊢ j # A ≤ B
           → Δ ⊢ ⟨ j , B ⟩ ~ Σ
           → Δ ⊢ A ≊ A'
           → JustSub Δ Σ A' B j

complete (⊢lit cloΣ) ~Z = typs (⊢lit cloΣ) ≊-int
complete (⊢var cloΣ x∈Γ) ~Z = typs (⊢var cloΣ x∈Γ) ≊-refl
complete (⊢ann ⊢e) ~Z with complete ⊢e ~∞
... | typs ⊢e₁ sim = typs (⊢ann ⊢e₁) ≊-refl
complete (⊢lam₁ ⊢e) ~∞ with complete ⊢e ~∞
... | typs ⊢e₁ sim = typs (⊢lam₁ ⊢e₁) (≊-arr ≊-refl (≊-weaken,0 sim))
complete (⊢lam₂ ⊢e) (~I ⊢e₁ j~Σ) with complete ⊢e (~weaken,0 j~Σ {!!})
... | typs ⊢e₂ sim = typs (⊢lam₂ ⊢e₁ {!!} ⊢e₂) (≊-arr ≊-refl (≊-weaken,0 sim))
complete (⊢app₁ ⊢e ⊢e₁) j~Σ with complete ⊢e (~C (complete-∞ ⊢e₁) j~Σ)
... | typs ⊢e₂ (≊-right x) = {!!}
... | typs ⊢e₂ (≊-arr sim sim₁) = typs (⊢app ⊢e₂) sim₁
complete (⊢app₂ ⊢e ⊢e₁) j~Σ = {!!}
complete (⊢sub ⊢e B≤A j≢Z) j~Σ with complete ⊢e ~Z
... | typs ⊢e₁ sim with complete-s B≤A j~Σ sim
... | subs ext sub sim₁ = typs (subsumption0 ⊢e₁ {!sub!}) sim₁
complete (⊢tabs ⊢e) ~Z with complete ⊢e ~Z
... | typs ⊢e₁ sim = typs (⊢tabs ⊢e₁) (≊-∀ sim)

complete-s (s-refl cloΓ cloA) ~Z sim = subs {!!} (s-empty cloΓ {!!}) sim
complete-s (s-int cloΓ) ~∞ ≊-int = subs {!!} (s-int cloΓ) ≊-int
complete-s (s-int cloΓ) ~∞ (≊-right x) = subs {!!} (s-ex-l= x (s-int cloΓ)) ≊-int
complete-s (s-var-∙ cloΓ inΓ) j~Σ sim = {!!}
complete-s (s-var-= cloΓ inΓ) j~Σ sim = {!!}
complete-s (s-arr₁ s s₁) j~Σ sim = {!!}
complete-s (s-arr₂ s s₁) j~Σ sim = {!!}
complete-s (s-arr₃ cloA s) j~Σ sim = {!!}
complete-s (s-∀ s) j~Σ sim = {!!}
complete-s (s-∀l s ic fd st₁ st₂) j~Σ sim = {!!}
complete-s (s-var-l inΓ s) j~Σ sim = {!!}
complete-s (s-var-r inΓ s) j~Σ sim = {!!}
