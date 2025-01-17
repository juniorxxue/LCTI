module Implicit.Sound where

open import Implicit.Language
open import Implicit.Decl renaming (find to d-find)
open import Implicit.Algo

infix 3 _⊢_~_
data _⊢_~_ : Env n m → Counter × Type m → Context n m → Set where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~I : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ Z # e ⦂ A) -- is A or not
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ~ ([ e ]↝ Σ)

  ~C : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ ∞ # e ⦂ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕔 j , A `→ B ⟩ ~ ([ e ]↝ Σ)

postulate

  ~-subst : ∀ {Γ : Env n m} {Σ A B j Σ' A'}
    → (Γ ,= B) ⊢ ⟨ j , A ⟩ ~ Σ
    → ⟦ B ⟧ᶜ Σ ⇘ Σ'
    → ⟦ B ⟧ A ⇘ A'
    → Γ ⊢ ⟨ j , A' ⟩ ~ Σ'

  ~-weaken0 : Γ , A ⊢ ⟨ j , B ⟩ ~ Σ'
            → ↑tmᶜ0 Σ ⇘ Σ'
            → Γ ⊢ ⟨ j , B ⟩ ~ Σ

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

e-ic : ∀ {Γ : Env n m} {j A Σ e}
  → Γ ⊢ ⟨ j , A ⟩ ~ [ e ]↝ Σ
  → 𝕚𝕔 j
e-ic (~I ⊢e ~j) = case-𝕚
e-ic (~C ⊢e ~j) = case-𝕔


data JustSub (Γ : Env n m) (Σ : Context n m) (A : Type m) (B : Type m) : Set where
  subs : ∀ {j}
    → (j~Σ : Γ ⊢ ⟨ j , B ⟩ ~ Σ)
    → (s : Γ ⊢ j # A ≤ B)
    → JustSub Γ Σ A B

data JustTyping (Γ : Env n m) (Σ : Context n m) (e : Term n m) (A : Type m) : Set where
  typs : ∀ {j}
    → (j~Σ : Γ ⊢ ⟨ j , A ⟩ ~ Σ)
    → (s : Γ ⊢ j # e ⦂ A)
    → JustTyping Γ Σ e A

sound : ∀ {Γ : Env n m} {Σ e A}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → JustTyping Γ Σ e A

sound-s : ∀ {Γ Γ' : Env n m} {Σ A B}
  → Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Γ' ↪ B
  → JustSub Γ' Σ A B

sound-s' : ∀ {Γ Γ' : Env n m} {Σ A B}
  → Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Γ' ↪ B
  → Polarity Γ A Σ ≤
  → JustSub Γ' Σ A B

sound-0 : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ □ ⇒ e ⇒ A
  → Γ ⊢ Z # e ⦂ A
sound-0 ⊢e with sound ⊢e
... | typs ~Z ⊢e = ⊢e

sound-∞ : ∀ {Γ : Env n m} {e A B}
  → Γ ⊢ τ B ⇒ e ⇒ A
  → Γ ⊢ ∞ # e ⦂ B
sound-∞ ⊢e rewrite ⊢id0 ⊢e with sound ⊢e
... | typs ~∞ ⊢e = ⊢e

sound (⊢lit cloΓ) = typs ~Z (⊢lit cloΓ)
sound (⊢var cloΓ x∈Γ) = typs ~Z (⊢var cloΓ x∈Γ)
sound (⊢ann ⊢e) = typs ~Z (⊢ann (sound-∞ ⊢e))
sound (⊢app ⊢e) with sound ⊢e
... | typs (~I ⊢e₁ j~Σ) ⊢e = typs j~Σ (⊢app₂ ⊢e ⊢e₁)
... | typs (~C ⊢e₁ j~Σ) ⊢e = typs j~Σ (⊢app₁ ⊢e ⊢e₁)
sound (⊢lam₁ ⊢e) with sound ⊢e
... | typs ~∞ s = typs ~∞ (⊢lam₁ s)
sound (⊢lam₂ ⊢e up-c ⊢e₁) with sound ⊢e₁
... | typs j ⊢e' = typs (~I (sound-0 ⊢e) (~-weaken0 j up-c)) (⊢lam₂ ⊢e')
sound (⊢sub ⊢e ne gc cloΣ s) with sound-s' s (polar-r (⊢closeΓ ⊢e) cloΣ)
... | subs j~Σ s₁ = typs j~Σ (⊢sub' (sound-0 ⊢e) s₁)
sound (⊢tabs ⊢e) with sound ⊢e
... | typs ~Z s = typs ~Z (⊢tabs s)

{-
sound-s s'@(s-term-o opnA ⊢e s s₁) with sound-s s | sound-s s₁
... | subs ~∞ s₂ | subs j~Σ s₃ = subs (~I (t-⊆-prv (sound-0 ⊢e) (s-⊆ s' {!!})) j~Σ) (s-arr₂ (s-⊆-prv s₂ (s-⊆ s₁ {!!})) s₃)
sound-s (s-∀l s upᶜ upᵉ st₁ st₂) with sound-s s
... | subs IH-j~Σ IH = subs ((~-subst IH-j~Σ {!!} (st-arr st₁ st₂))) (s-∀l IH {!!} {!!} st₁ st₂)
-}

sound-s' s-int pr = subs ~∞ (s-int (polar-closed pr))
sound-s' (s-empty clo) (polar-r cloΓ cloΣ) = subs ~Z (s-refl cloΓ clo)
sound-s' s-var (polar-l cloΓ (⊢c-var-∙ inΓ)) = subs ~∞ (s-var-∙ cloΓ inΓ)
sound-s' s-var (polar-l cloΓ (⊢c-var-= inΓ)) = subs ~∞ (s-var-= cloΓ inΓ)
sound-s' s-var (polar-r cloΓ (⊢c-τ (⊢c-var-∙ inΓ))) = subs ~∞ (s-var-∙ cloΓ inΓ)
sound-s' s-var (polar-r cloΓ (⊢c-τ (⊢c-var-= inΓ))) = subs ~∞ (s-var-= cloΓ inΓ)
sound-s' (s-ex-l^ x-in inst) (polar-r cloΓ (⊢c-τ cloA)) =
  subs ~∞ (s-var-l (inst-in inst) (s-refl-∞ (⊆-closed cloΓ (inst-⊆ inst cloA)) (⊆-cloA cloA (inst-⊆ inst cloA))))
sound-s' (s-ex-l= x-in s) pr with sound-s' s (polar-in-l pr x-in)
... | subs ~∞ s₁ = subs ~∞ (s-var-l (⊆-in:= x-in (s-⊆ s (polar-in-l pr x-in))) s₁)
sound-s' (s-ex-r^ x-in inst) (polar-l cloΓ cloA) =
  subs ~∞ (s-var-r (inst-in inst) (s-refl-∞ (⊆-closed cloΓ (inst-⊆ inst cloA)) (⊆-cloA cloA (inst-⊆ inst cloA))))
sound-s' (s-ex-r= x-in s) pr with sound-s' s (polar-in-r pr x-in)
... | subs ~∞ s₁ = subs ~∞ (s-var-r (⊆-in:= x-in (s-⊆ s (polar-in-r pr x-in))) s₁)
sound-s' s'@(s-arr s s₁) pr with sound-s' s (polar-arr-l pr) | sound-s' s₁ (polar-arr-r (polar-⊆ pr (s-⊆ s (polar-arr-l pr))))
... | subs ~∞ s₂ | subs ~∞ s₃ = subs ~∞ (s-arr₁ (s-⊆-prv s₂ (s-⊆ s₁ ((polar-arr-r (polar-⊆ pr (s-⊆ s (polar-arr-l pr))))))) s₃)
sound-s' (s-term-c ⊢e s) pr'@(polar-r cloΓ (⊢c-term cloe cloΣ)) with sound-s' s (polar-tm-r pr')
... | subs j~Σ s₁ with ⊢id0 ⊢e
... | refl = subs (~C (t-⊆-prv (sound-∞ ⊢e) (s-⊆ s (polar-r cloΓ cloΣ))) j~Σ) (s-arr₃ (⊆-cloA (⊢closeA ⊢e) (s-⊆ s (polar-r cloΓ cloΣ))) s₁)
sound-s' (s-term-o opnA ⊢e s s₁) pr = {!!}
sound-s' (s-∀ s) pr with sound-s' s (polar-∀ pr)
... | subs ~∞ s₁ = subs ~∞ (s-∀ s₁)
sound-s' (s-∀l s upᶜ upᵉ st₁ st₂) pr = {!!}

sound-find : Γ ⊢ A  ⌞ ≤⁺ ⌝ Σ ⊣ Γ' ↪ B
           → Γ  ∋^ k
           → Γ' ∋= k
           → Γ' ⊢ ⟨ j , B ⟩ ~ Σ
           → d-find A k j
sound-find s-int k^ k= j~Σ = {!!}
sound-find (s-empty clo) k^ k= j~Σ = {!!}
sound-find s-var k^ k= j~Σ = {!!}
sound-find (s-ex-l^ x-in inst) k^ k= ~∞ = f-∞ {!!}
sound-find (s-ex-l= x-in s) k^ k= ~∞ = f-∞ {!!}
sound-find (s-ex-r= x-in s) k^ k= ~∞ = f-∞ {!!}
sound-find (s-arr s s₁) k^ k= j~Σ = {!!}
sound-find (s-term-c ⊢e s) k^ k= (~I ⊢e₁ j~Σ) = f-arr-𝕚-r (sound-find s k^ k= j~Σ)
-- f-arr-𝕚-r (sound-find s k^ k= j~Σ)
sound-find (s-term-c ⊢e s) k^ k= (~C ⊢e₁ j~Σ) = f-arr-𝕔 {!!} (sound-find s k^ k= j~Σ)
sound-find (s-term-o opnA ⊢e s s₁) k^ k= (~I ⊢e₁ j~Σ) = {!!}
sound-find (s-term-o opnA ⊢e s s₁) k^ k= (~C ⊢e₁ j~Σ) = f-arr-𝕔 {!!} {!!}
sound-find (s-∀ s) k^ k= j~Σ = {!!}
sound-find (s-∀l s upᶜ upᵉ st₁ st₂) k^ k= j~Σ = {!!}
