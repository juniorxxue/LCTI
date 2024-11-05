module Implicit.Sound where

open import Implicit.Common
open import Implicit.Decl renaming (_:=_∈_ to _:=_∈d_; find to d-find; bound to d-bound)
open import Implicit.Decl.Subst
open import Implicit.Decl.Properties
open import Implicit.Algo renaming (_:=_∈_ to _:=_∈a_)
open import Implicit.Algo.Properties
open import Implicit.Algo.Environments
open import Implicit.Algo.Find renaming (find to a-find; bound to a-bound)

postulate
  ∈a→∈d : ∀ {Ψ : SEnv n m} {X A}
    → X := A ∈a Ψ
    → X := A ∈d 𝕄 Ψ

  ⊆-:= : ∀ {Ψ Ψ' : SEnv n m} {X A}
    → Ψ ⊆ Ψ'
    → X := A ∈a Ψ
    → X := A ∈a Ψ'

  s-⊆-prv : ∀ {Ψ Ψ' : SEnv n m} {A B}
    → Ψ ⊆ Ψ'
    → 𝕄 Ψ ⊢ ∞ # A ≤ B
    → 𝕄 Ψ' ⊢ ∞ # A ≤ B

  ⊢d-⊆-prv : ∀ {Ψ Ψ' : SEnv n m} {A e j}
    → Ψ ⊆ Ψ'
    → 𝕄 Ψ ⊢ j # e ⦂ A
    → 𝕄 Ψ' ⊢ j # e ⦂ A


infix 3 _⊢_~_
data _⊢_~_ : Env n m → Counter × Type m → Context n m → Set where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~I : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ Z # e ⦂ A) -- is A or not
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ I j , A `→ B ⟩ ~ ([ e ]↝ Σ)

  ~C : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ ∞ # e ⦂ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ C j , A `→ B ⟩ ~ ([ e ]↝ Σ)

postulate

  s-w-m : ∀ {Γ : Env n m} {A B j}
    →  𝕄 (𝕎 Γ) ⊢ j # A ≤ B
    → Γ ⊢ j # A ≤ B

  ~-w-m : ∀ {Γ : Env n m} {j A Σ}
    → 𝕄 (𝕎 Γ) ⊢ ⟨ j , A ⟩ ~ Σ
    → Γ ⊢ ⟨ j , A ⟩ ~ Σ

  ~-weaken : ∀ {Γ : Env n m} {Σ A B j}
    → Γ , A ⊢ ⟨ j , B ⟩ ~ ↑Σ0 Σ
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ

  ~-subst : ∀ {Γ : Env n m} {Σ A B j Σ' A'}
    → (Γ ,= B) ⊢ ⟨ j , A ⟩ ~ Σ
    → [ B ]ᶜ Σ ⇨ Σ'
    → [ B ]ˢ A ⇨ A'
    → Γ ⊢ ⟨ j , A' ⟩ ~ Σ'

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

e-ic : ∀ {Γ : Env n m} {j A Σ e}
  → Γ ⊢ ⟨ j , A ⟩ ~ [ e ]↝ Σ
  → IC j
e-ic (~I ⊢e ~j) = ic-I
e-ic (~C ⊢e ~j) = ic-C


data JustSub (Ψ : SEnv n m) (Σ : Context n m) (A : Type m) (B : Type m) : Set where
  subs : ∀ {j}
    → (j~Σ : 𝕄 Ψ ⊢ ⟨ j , B ⟩ ~ Σ)
    → (s : 𝕄 Ψ ⊢ j # A ≤ B)
    → JustSub Ψ Σ A B

data JustTyping (Γ : Env n m) (Σ : Context n m) (e : Term n m) (A : Type m) : Set where
  typs : ∀ {j}
    → (j~Σ : Γ ⊢ ⟨ j , A ⟩ ~ Σ)
    → (s : Γ ⊢ j # e ⦂ A)
    → JustTyping Γ Σ e A

data JustFind (Γ : Env n m) (A : Type m) (k : Fin m) (Σ : Context n m) : Set where
  finds : ∀ {j B}
    → (j~Σ : Γ ⊢ ⟨ j , B ⟩ ~ Σ)
    → d-find A k j
    → JustFind Γ A k Σ

sound : ∀ {Γ : Env n m} {Σ e A}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → JustTyping Γ Σ e A

sound-s : ∀ {Ψ Ψ' : SEnv n m} {Σ A B}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → JustSub Ψ' Σ A B

sound-find : ∀ {Γ : Env n m} {k Σ A B j}
  → a-find Γ A k Σ
  → Γ ⊢ ⟨ j , B ⟩ ~ Σ
  → d-find A k j

sound-find' : ∀ {Γ : Env n m} {k Σ A}
  → a-find Γ A k Σ
  → JustFind Γ A k Σ

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
sound (⊢lam₂ ⊢e ⊢e₁) with sound ⊢e₁
... | typs j ⊢e' = typs (~I (sound-0 ⊢e) (~-weaken j)) (⊢lam₂ ⊢e')
sound (⊢sub ⊢e ne gc s) with sound-s s
... | subs j~Σ s₁ = typs (~-w-m j~Σ) (⊢sub' (sound-0 ⊢e) (s-w-m s₁))
sound (⊢tabs ⊢e) with sound ⊢e
... | typs ~Z s = typs ~Z (⊢tabs s)

sound-s s-int = subs ~∞ s-int
sound-s (s-empty p) = subs ~Z s-refl
sound-s s-var = subs ~∞ s-var
sound-s (s-ex-l^ clo x-in inst) = subs ~∞ (s-var-l (∈a→∈d (inst-in inst)) s-refl-∞)
sound-s (s-ex-l= clo x-in s) with sound-s s
... | subs ~∞ s' = subs ~∞ (s-var-l (∈a→∈d (⊆-:= (s-⊆ s) x-in)) s')
sound-s (s-ex-r^ clo x-in inst) = subs ~∞ (s-var-r (∈a→∈d (inst-in inst)) s-refl-∞)
sound-s (s-ex-r= clo x-in s) with sound-s s
... | subs ~∞ s' = subs ~∞ (s-var-r (∈a→∈d (⊆-:= (s-⊆ s) x-in)) s')
sound-s (s-arr s s₁) with sound-s s | sound-s s₁
... | subs ~∞ s₂ | subs ~∞ s₃ = subs ~∞ (s-arr₁ (s-⊆-prv (s-⊆ s₁) s₂) s₃)
sound-s (s-term-c cloA ⊢e s) with sound-s s
... | subs j~Σ s' with ⊢id0 ⊢e
...   | refl = subs (~C (⊢d-⊆-prv (s-⊆ s) (sound-∞ ⊢e)) j~Σ) (s-arr₃ s')
sound-s (s-term-o ⊢e s s₁) with sound-s s | sound-s s₁ | sound-0 ⊢e
... | subs ~∞ s'' | subs j~Σ s' | ⊢e' rewrite ≤id0 s = subs (~I (⊢d-⊆-prv (⊆trans (s-⊆ s) (s-⊆ s₁)) ⊢e') j~Σ) (s-arr₂ {!s''!} s') -- ok, same as above
sound-s (s-∀ s) with sound-s s
... | subs ~∞ s' = subs ~∞ (s-∀ s')
sound-s (s-∀l s st₁ st₂) with sound-s s
... | subs j~Σ s' = subs (~-subst j~Σ {!!} (st-arr st₁ st₂)) (s-∀l s' (e-ic {!!}) (sound-find (s-find s) j~Σ) st₁ st₂) -- ok

sound-find (f-τ bd) j~Σ = {!!}
sound-find (f-arr-l bd ⊢e) (~I ⊢e₁ j~Σ) = {!!}
sound-find (f-arr-l bd ⊢e) (~C ⊢e₁ j~Σ) = {!!}
sound-find (f-arr-r fd) j~Σ = {!!}
sound-find (f-∀ fd) j~Σ = {!!}


sound-find' (f-τ bd) = finds ~∞ {!!}
sound-find' (f-arr-l bd ⊢e) = finds (~I (sound-0 ⊢e) {!!}) (f-arr-I-l {!!})
sound-find' (f-arr-r fd) = finds (~C {!!} {!!}) (f-arr-C {!!})
sound-find' (f-∀ fd) = {!!}
