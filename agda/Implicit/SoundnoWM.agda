module Implicit.SoundnoWM where

open import Implicit.Language
open import Implicit.Decl renaming (find to d-find)
open import Implicit.Algo renaming (find to a-find)

private variable
  Ψ Ψ' : SEnv n m
  A B C : Type m
  Γ Γ' : Env n m

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

  s-w-m : ∀ {Γ : Env n m} {A B j}
    → 𝕄 (𝕎 Γ) ⊢ j # A ≤ B
    → Γ ⊢ j # A ≤ B

  ~-w-m : ∀ {Γ : Env n m} {j A Σ}
    → 𝕄 (𝕎 Γ) ⊢ ⟨ j , A ⟩ ~ Σ
    → Γ ⊢ ⟨ j , A ⟩ ~ Σ

  ~-subst : ∀ {Γ : Env n m} {Σ A B j Σ' A'}
    → (Γ ,= B) ⊢ ⟨ j , A ⟩ ~ Σ
    → ⟦ B ⟧ᶜ Σ ⇘ Σ'
    → ⟦ B ⟧ A ⇘ A'
    → Γ ⊢ ⟨ j , A' ⟩ ~ Σ'

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

e-ic : ∀ {Γ : Env n m} {j A Σ e}
  → Γ ⊢ ⟨ j , A ⟩ ~ [ e ]↝ Σ
  → 𝕚𝕔 j
e-ic (~I ⊢e ~j) = case-𝕚
e-ic (~C ⊢e ~j) = case-𝕔

infix 3 _⇌_
data _⇌_ : SEnv n m → Env n m → Set where
  ⇌∅ : ∅ ⇌ ∅
  ⇌, : Ψ ⇌ Γ
     → Ψ , A ⇌ Γ , A
  ⇌∙ : Ψ ⇌ Γ
     → Ψ ,∙ ⇌ Γ ,∙
  ⇌= : Ψ ⇌ Γ
     → Ψ ,= A ⇌ Γ ,= A


𝕎⇌Γ : 𝕎 Γ ⇌ Γ
𝕎⇌Γ {Γ = ∅} = ⇌∅
𝕎⇌Γ {Γ = Γ , A} = ⇌, 𝕎⇌Γ
𝕎⇌Γ {Γ = Γ ,∙} = ⇌∙ 𝕎⇌Γ
𝕎⇌Γ {Γ = Γ ,= A} = ⇌= 𝕎⇌Γ


data JustSub (Γ : Env n m) (Σ : Context n m) (A : Type m) (B : Type m) : Set where
  subs : ∀ {j}
    → (j~Σ : Γ ⊢ ⟨ j , B ⟩ ~ Σ)
    → (s : Γ ⊢ j # A ≤ B)
    → JustSub Γ Σ A B

data JustSub' (Γ : Env n m) (Σ : Context n m) (A : Type m) (B : Type m) : Set where
  subs : ∀ {j}
    → (j~Σ : Γ ⊢ ⟨ j , B ⟩ ~ Σ)
    → (s : Γ ⊢ j # A ≤ B)
    → JustSub' Γ Σ A B

data JustTyping (Γ : Env n m) (Σ : Context n m) (e : Term n m) (A : Type m) : Set where
  typs : ∀ {j}
    → (j~Σ : Γ ⊢ ⟨ j , A ⟩ ~ Σ)
    → (s : Γ ⊢ j # e ⦂ A)
    → JustTyping Γ Σ e A

sound : ∀ {Γ : Env n m} {Σ e A}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → JustTyping Γ Σ e A

sound-find : ∀ {Γ : Env n m} {k Σ A B j}
  → a-find Γ A k Σ
  → Γ ⊢ ⟨ j , B ⟩ ~ Σ
  → d-find A k j

sound-s⁺ : ∀ {Ψ Ψ' : SEnv n m} {Σ A B}
  → Ψ ⊢ A ≤⁺ Σ ⊣ Ψ' ↪ B
  → Ψ' ⇌ Γ
  → JustSub Γ Σ A B

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

sound ⊢lit = typs ~Z ⊢lit
sound (⊢var x∈Γ) = typs ~Z (⊢var x∈Γ)
sound (⊢ann ⊢e) = typs ~Z (⊢ann (sound-∞ ⊢e))
sound (⊢app ⊢e) with sound ⊢e
... | typs (~I ⊢e₁ j~Σ) ⊢e = typs j~Σ (⊢app₂ ⊢e ⊢e₁)
... | typs (~C ⊢e₁ j~Σ) ⊢e = typs j~Σ (⊢app₁ ⊢e ⊢e₁)
sound (⊢lam₁ ⊢e) with sound ⊢e
... | typs ~∞ s = typs ~∞ (⊢lam₁ s)
sound (⊢lam₂ ⊢e up-c ⊢e₁) with sound ⊢e₁
... | typs j ⊢e' = typs (~I (sound-0 ⊢e) {!!}) (⊢lam₂ ⊢e') -- weaken
sound (⊢sub ⊢e ne gc s) with sound-s⁺ s 𝕎⇌Γ
... | subs j~Σ s₁ = typs j~Σ (⊢sub' (sound-0 ⊢e) s₁)
sound (⊢tabs ⊢e) with sound ⊢e
... | typs ~Z s = typs ~Z (⊢tabs s)

sound-s⁺ s⁺-int toΓ = subs ~∞ s-int
sound-s⁺ (s⁺-empty cloA) toΓ = subs ~Z s-refl
sound-s⁺ (s⁺-var cloX) toΓ = subs ~∞ s-var
sound-s⁺ (s⁺-ex-l^ cloA x-in inst) toΓ = subs ~∞ {!!}
sound-s⁺ (s⁺-ex-l= cloA x-in s) toΓ = {!!}
sound-s⁺ (s⁺-ex-r= cloA x-in s) toΓ = {!!}
sound-s⁺ (s⁺-arr cloC cloD s s₁) toΓ = {!!}
sound-s⁺ (s⁺-term-c cloA cloΣ ⊢e s) toΓ with sound-s⁺ s toΓ
... | subs j~Σ s₁ with ⊢id0 ⊢e
...   | refl = subs (~C {!sound-∞ ⊢e!} j~Σ) (s-arr₃ s₁)
sound-s⁺ (s⁺-term-o opnA cloΣ ⊢e s s₁) toΓ = {!!}
sound-s⁺ (s⁺-∀ cloB s) toΓ = {!!}
sound-s⁺ (s⁺-∀l cloΣ s upᶜ upᵉ st₁ st₂) toΓ = {!!}

sound-find {Σ = □} fd j~Σ = {!!}
sound-find {Σ = τ A} fd j~Σ = {!!}
sound-find {Σ = [ e ]↝ Σ} (a-find.f-arr-l bd ⊢e) j~Σ = {!!}
sound-find {Σ = [ e ]↝ Σ} (a-find.f-arr-r x ⊢e fd) j~Σ = {!!}
sound-find {Σ = [ e ]↝ Σ} (a-find.f-∀ fd x) j~Σ = {!!}
