module Implicit.SoundCounter where

open import Implicit.Language hiding (_≤_)
open import Implicit.Decl renaming (find to d-find)
open import Implicit.Algo
open import Implicit.Algo.BaseCounter



----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

sound : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
      → Γ ⊢ j # e ⦂ A

sound-find-l : Γ ⊢ A  ⌞ ≤⁺ ⌝ Σ ⊣ Δ ↪ B ↡ j
             → Γ ⊢cᶜ Σ
             → Γ  ∋^ k
             → Γ' ∋= k
             → d-find A k j

sound-find-r : Γ ⊢ A  ⌞ ≤⁻ ⌝ τ B ⊣ Δ ↪ C ↡ j
             → Γ ⊢c A
             → Γ  ∋^ k
             → Δ ∋= k
             → d-find B k j

sound-find-l0 : Γ ,^ ⊢ A ⌞ ≤⁺ ⌝ [ e' ]↝ Σ' ⊣ Δ ,= B ↪ C `→ D ↡ j
              → Γ ⊢cᶜ [ e ]↝ Σ
              → ↑tyᵉ0 e ⇘ e'
              → ↑tyᶜ0 Σ ⇘ Σ'
              → d-find A #0 j
sound-find-l0 s clo up1 up2 = sound-find-l s (⊢cᶜ-weaken^0 clo (↑tyᶜ-e up1 up2)) Z Z

sound-s : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B ↡ j
        → Polarity Γ A Σ ≤
        → Δ ⊢ j # A ≤ B
sound-s s-int pr = {!!}
sound-s (s-empty clo) pr = {!!}
sound-s s-var pr = {!!}
sound-s (s-ex-l^ x-in inst) pr = {!!}
sound-s (s-ex-l= x-in s) pr = {!!}
sound-s (s-ex-r^ x-in inst) pr = {!!}
sound-s (s-ex-r= x-in s) pr = {!!}
sound-s (s-arr s s₁) pr = {!!}
sound-s (s-term-c ⊢e s) pr = {!!}
sound-s (s-term-o opnA ⊢e s s₁) pr = {!!}
sound-s (s-∀ s) pr = {!!}
sound-s (s-∀l s upᶜ upᵉ st₁ st₂) (polar-r cloΓ cloΣ) =
  s-∀l (sound-s s (polar-r (clo-S^ cloΓ) (⊢cᶜ-weaken^0 cloΣ (↑tyᶜ-e upᵉ upᶜ)))) {!!} (sound-find-l0 s cloΣ upᵉ upᶜ) st₁ st₂

sound-find-l s clo inΓ inΔ = {!!}
sound-find-r s clo inΓ inΔ = {!!}



----------------------------------------------------------------------
--+                             Bridge                             +--
----------------------------------------------------------------------

infix 3 _⊢_~_
data _⊢_~_ : Env n m → Counter × Type m → Context n m → Set where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~I : ∀ {Γ : Env n m} {j A B Σ e}
--    → (⊢e : Γ ⊢ □ ⇒ e ⇒ A)
    → (⊢e : Γ ⊢ Z # e ⦂ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ~ ([ e ]↝ Σ)

  ~C : ∀ {Γ : Env n m} {j A B Σ e}
    (⊢e : Γ ⊢ ∞ # e ⦂ A)
--    → (⊢e : Γ ⊢ τ A ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕔 j , A `→ B ⟩ ~ ([ e ]↝ Σ)

postulate

  ~subst : ∀ {Γ : Env n m} {Σ A B j Σ' A'}
    → (Γ ,= B) ⊢ ⟨ j , A ⟩ ~ Σ
    → ⟦ B ⟧ᶜ Σ ⇘ Σ'
    → ⟦ B ⟧ A ⇘ A'
    → Γ ⊢ ⟨ j , A' ⟩ ~ Σ'

  ~weaken0 : Γ , A ⊢ ⟨ j , B ⟩ ~ Σ'
            → ↑tmᶜ0 Σ ⇘ Σ'
            → Γ ⊢ ⟨ j , B ⟩ ~ Σ

data JustType (Γ : Env n m) (Σ : Context n m) (e : Term n m) (A : Type m) : Set where
  typs : ∀ {j}
    → (j~Σ : Γ ⊢ ⟨ j , A ⟩ ~ Σ)
    → (⊢e : Γ ⊢ Σ ⇒ e ⇒ A ↡ j)
    → JustType Γ Σ e A

data JustSub (Γ : Env n m) (A : Type m) (≤ : Polar) (Σ : Context n m) (Δ : Env n m) (B : Type m) : Set where
  subs : ∀ {j}
    → (j~Σ : Δ ⊢ ⟨ j , B ⟩ ~ Σ)
    → (s : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B ↡ j)
    → JustSub Γ A ≤ Σ Δ B

t-imply : Γ ⊢ Σ ⇒ e ⇒ A
        → JustType Γ Σ e A

s-imply : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
        → Polarity Γ A Σ ≤
        → JustSub Γ A ≤ Σ Δ B

sound-0 : Γ ⊢ □ ⇒ e ⇒ A
        → Γ ⊢ Z # e ⦂ A
sound-0 ⊢e with t-imply ⊢e
... | typs ~Z ⊢e₁ = sound ⊢e₁

sound-∞ : Γ ⊢ τ B ⇒ e ⇒ A
        → Γ ⊢ ∞ # e ⦂ B
sound-∞ ⊢e with t-imply ⊢e
... | typs ~∞ ⊢e₁ = sound ⊢e₁

t-imply (⊢lit cloΓ) = typs ~Z (⊢lit cloΓ)
t-imply (⊢var cloΓ x∈Γ) = typs ~Z (⊢var cloΓ x∈Γ)
t-imply (⊢ann ⊢e) with t-imply ⊢e
... | typs ~∞ ⊢e₁ = typs ~Z (⊢ann ⊢e₁)
t-imply (⊢app ⊢e) with t-imply ⊢e
... | typs (~I ⊢e₂ j~Σ) ⊢e₁ = typs j~Σ (⊢app ⊢e₁)
... | typs (~C ⊢e₂ j~Σ) ⊢e₁ = typs j~Σ (⊢app ⊢e₁)
t-imply (⊢lam₁ ⊢e) with t-imply ⊢e
... | typs ~∞ ⊢e₁ = typs ~∞ (⊢lam₁ ⊢e₁)
t-imply (⊢lam₂ ⊢e up-c ⊢e₁) with t-imply ⊢e | t-imply ⊢e₁
... | typs ~Z ⊢e₂ | typs j~Σ₁ ⊢e₃ = typs (~I (sound-0 ⊢e) (~weaken0 j~Σ₁ up-c)) (⊢lam₂ ⊢e₂ up-c ⊢e₃)
t-imply (⊢sub ⊢e ne gc cloΣ s) with s-imply s (polar-r (⊢closeΓ ⊢e) cloΣ) | t-imply ⊢e
... | subs j~Σ s₁ | typs ~Z ⊢e₁ = typs j~Σ (⊢sub ⊢e₁ ne gc cloΣ s₁)
t-imply (⊢tabs ⊢e) with t-imply ⊢e
... | typs ~Z ⊢e₁ = typs ~Z (⊢tabs ⊢e₁)

s-imply s-int pr = subs ~∞ s-int
s-imply (s-empty clo) pr = subs ~Z (s-empty clo)
s-imply s-var pr = subs ~∞ s-var
s-imply (s-ex-l^ x-in inst) pr = subs ~∞ (s-ex-l^ x-in inst)
s-imply (s-ex-l= x-in s) pr with s-imply s (polar-in-l pr x-in)
... | subs ~∞ s₁ = subs ~∞ (s-ex-l= x-in s₁)
s-imply (s-ex-r^ x-in inst) pr = subs ~∞ (s-ex-r^ x-in inst)
s-imply (s-ex-r= x-in s) pr with s-imply s (polar-in-r pr x-in)
... | subs ~∞ s₁ = subs ~∞ (s-ex-r= x-in s₁)
s-imply (s-arr s s₁) pr with s-imply s (polar-arr-l pr) | s-imply s₁ (polar-⊆ (polar-arr-r pr) (s-⊆ s (polar-arr-l pr)))
... | subs ~∞ s₂ | subs ~∞ s₃ = subs ~∞ (s-arr s₂ s₃)
s-imply (s-term-c ⊢e s) pr with s-imply s (polar-tm-r pr) | t-imply ⊢e
... | subs j~Σ s₁ | typs ~∞ ⊢e₁ = subs (~C (t-⊆-prv (sound-∞ ⊢e) (s-⊆ s (polar-tm-r pr))) j~Σ) (s-term-c ⊢e₁ s₁)
s-imply s'@(s-term-o opnA ⊢e s s₁) pr@(polar-r cloΓ cloΣ) with s-imply s (polar-l cloΓ (⊢closeA ⊢e))
                                                          | s-imply s₁ (polar-⊆ (polar-tm-r pr) (s-⊆ s (polar-l cloΓ (⊢closeA ⊢e))))
                                                          | t-imply ⊢e
... | subs ~∞ s₂ | subs j~Σ s₃ | typs ~Z ⊢e₁ = subs (~I (t-⊆-prv (sound-0 ⊢e) (s-⊆ s' pr)) j~Σ) (s-term-o opnA ⊢e₁ s₂ s₃)
s-imply (s-∀ s) pr with s-imply s (polar-∀ pr)
... | subs ~∞ s₁ = subs ~∞ (s-∀ s₁)
s-imply (s-∀l s upᶜ upᵉ st₁ st₂) (polar-r cloΓ cloΣ) with s-imply s (polar-r (clo-S^ cloΓ) (⊢cᶜ-weaken^0 cloΣ (↑tyᶜ-e upᵉ upᶜ)))
... | subs j~Σ s₁ = subs (~subst j~Σ {!!} (st-arr st₁ st₂)) (s-∀l s₁ upᶜ upᵉ st₁ st₂)
