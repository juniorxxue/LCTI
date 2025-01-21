module Implicit.Sound where

open import Implicit.Language
open import Implicit.Decl renaming (find to d-find)
open import Implicit.Algo

postulate
  ⊢id0 : Γ ⊢ τ A ⇒ e ⇒ B ↡ ∞
       → A ≡ B

  s-id0 : Γ ⊢ A ≤ τ B ⊣ Γ ↪ C ↡ j
        → B ≡ C

infix 3 _⊢_~_
data _⊢_~_ : Env n m → Counter × Type m → Context n m → Set where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~I : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ □ ⇒ e ⇒ A ↡ Z)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ~ ([ e ]↝ Σ)

  ~C : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ (τ A) ⇒ e ⇒ A ↡ ∞)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕔 j , A `→ B ⟩ ~ ([ e ]↝ Σ)


algo-~ : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
       → Γ ⊢ ⟨ j , A ⟩ ~ Σ

s-~ : Γ ⊢ A₁ ≤ Σ ⊣ Γ ↪ A ↡ j
    → Γ ⊢ ⟨ j , A ⟩ ~ Σ

s-~ (s-int cloΓ) = ~∞
s-~ (s-empty cloΓ clo) = ~Z
s-~ (s-var-∙ cloΓ x-in) = ~∞
s-~ (s-var-= cloΓ x-in) = ~∞
s-~ (s-ex-l^ cloA cloΓ x-in inst) = ~∞
s-~ (s-ex-l= x-in s) = ~∞
s-~ (s-ex-r^ cloA cloΓ x-in inst) = ~∞
s-~ (s-ex-r= x-in s) = ~∞
s-~ (s-arr s s₁) = ~∞
s-~ (s-term-c ⊢e s) with ⊢id0 ⊢e
... | refl = ~C ⊢e (s-~ s)
s-~ (s-term-o opnA ⊢e s s₁) = ~I ⊢e {!!}
s-~ (s-∀ s) rewrite s-id0 s = ~∞
s-~ (s-∀l s upᶜ upᵉ st₁ st₂) = {!s-~!}

algo-~ (⊢lit cloΓ) = ~Z
algo-~ (⊢var cloΓ x∈Γ) = ~Z
algo-~ (⊢ann ⊢e) = ~Z
algo-~ (⊢app ⊢e) with algo-~ ⊢e
... | ~I ⊢e₁ r = r
... | ~C ⊢e₁ r = r
algo-~ (⊢lam₁ ⊢e) rewrite ⊢id0 ⊢e = ~∞
algo-~ (⊢lam₂ ⊢e up-c ⊢e₁) = ~I ⊢e {!algo-~ ⊢e₁!}
algo-~ (⊢sub ⊢e ne gc s) = s-~ s
algo-~ (⊢tabs ⊢e) = ~Z


----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

sound : ∀ {Γ : Env n m} {Σ e A}
  → Γ ⊢ Σ ⇒ e ⇒ A ↡ j
  → Γ ⊢ j # e ⦂ A

sound-s : ∀ {Γ Γ' : Env n m} {Σ A B}
  → Γ ⊢ A ≤ Σ ⊣ Δ ↪ B ↡ j
  → Δ ⊢ j # A ≤ B

sound-0 : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ □ ⇒ e ⇒ A ↡ Z
  → Γ ⊢ Z # e ⦂ A
sound-0 ⊢e = sound ⊢e

sound-∞ : ∀ {Γ : Env n m} {e A B}
  → Γ ⊢ τ B ⇒ e ⇒ A ↡ ∞
  → Γ ⊢ ∞ # e ⦂ B
sound-∞ ⊢e with ⊢id0 ⊢e
... | refl = sound ⊢e

sound (⊢lit cloΓ) = ⊢lit cloΓ
sound (⊢var cloΓ x∈Γ) = ⊢var cloΓ x∈Γ
sound (⊢ann ⊢e) = ⊢ann (sound-∞ ⊢e)
sound (⊢app ⊢e) with sound ⊢e
sound (⊢app {j = Z} ⊢e) | r = {!!}
sound (⊢app {j = ∞} ⊢e) | r = {!!}
sound (⊢app {j = 𝕚 j} ⊢e) | r with algo-~ ⊢e
... | ~I ⊢e₁ r' = ⊢app₂ r (sound-0 ⊢e₁)
sound (⊢app {j = 𝕔 j} ⊢e) | r with algo-~ ⊢e
... | ~C ⊢e₁ r' = ⊢app₁ r (sound-∞ ⊢e₁)
sound (⊢lam₁ ⊢e) = ⊢lam₁ (sound ⊢e)
sound (⊢lam₂ ⊢e up-c ⊢e₁) = ⊢lam₂ (sound ⊢e₁)
sound (⊢sub ⊢e ne gc s) = ⊢sub' (sound ⊢e) (sound-s s)
sound (⊢tabs ⊢e) = ⊢tabs (sound ⊢e)

sound-s (s-int cloΓ) = s-int cloΓ
sound-s (s-empty cloΓ clo) = s-refl cloΓ clo
sound-s (s-var-∙ cloΓ x-in) = s-var-∙ cloΓ x-in
sound-s (s-var-= cloΓ x-in) = s-var-= cloΓ x-in
sound-s (s-ex-l^ cloA cloΓ x-in inst) = {!!}
sound-s (s-ex-l= x-in s) = {!!}
sound-s (s-ex-r^ cloA cloΓ x-in inst) = {!!}
sound-s (s-ex-r= x-in s) = {!!}
sound-s (s-arr s s₁) = {!!}
sound-s (s-term-c ⊢e s) = {!!}
sound-s (s-term-o opnA ⊢e s s₁) = {!!}
sound-s (s-∀ s) = s-∀ (sound-s s)
sound-s (s-∀l s upᶜ upᵉ st₁ st₂) = s-∀l (sound-s s) {!𝕚𝕔!} {!!} st₁ st₂

sound-find-l : Γ ⊢ A ≤ Σ ⊣ Δ ↪ B ↡ j
           → Γ ∋^ k
           → Δ ∋= k
           → d-find A k j

sound-find-r : Γ ⊢ A ≤ τ B ⊣ Δ ↪ C ↡ j
           → Γ ∋^ k
           → Δ ∋= k
           → d-find B k j
