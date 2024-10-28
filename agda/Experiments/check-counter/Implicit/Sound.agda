module Implicit.Sound where

open import Implicit.Common
open import Implicit.Decl
open import Implicit.Decl.Subst
open import Implicit.Decl.Properties
open import Implicit.Algo
open import Implicit.Algo.Properties

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

{-
  spl-weaken : ∀ {Σ Σ' : Context n m} {A e̅ A̅ A' k}
    → ⟦ Σ , A ⟧→⟦ e̅ , Σ' , A̅ , A' ⟧
    → ⟦ ↑Σ k Σ , A ⟧→⟦ up k e̅ , ↑Σ k Σ' , A̅ , A' ⟧
-}    

  spl-unique : ∀ {Σ : Context n m} {A Σ₁' Σ₂' A̅₁ A̅₂ A₁' A₂' e̅₁ e̅₂}
    → ⟦ Σ , A ⟧→⟦ e̅₁ , Σ₁' , A̅₁ , A₁' ⟧
    → ⟦ Σ , A ⟧→⟦ e̅₂ , Σ₂' , A̅₂ , A₂' ⟧
    → (e̅₁ ≡ e̅₂) × (Σ₁' ≡ Σ₂') × (A̅₁ ≡ A̅₂) × (A₁' ≡ A₂')

  ⊢spl-τ : ∀ {Γ : Env n m} {Σ e A es As A' T}
    → Γ ⊢ Σ ⇒ e ⇒ A
    → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
    → T ≡ A'

  s-w-m : ∀ {Γ : Env n m} {A B j}
    →  𝕄 (𝕎 Γ) ⊢ j # A ≤ B
    → Γ ⊢ j # A ≤ B

  ~-w-m : ∀ {Γ : Env n m} {j A Σ}
    → 𝕄 (𝕎 Γ) ⊢ ⟨ j , A ⟩ ~ Σ
    → Γ ⊢ ⟨ j , A ⟩ ~ Σ

  ~-weaken : ∀ {Γ : Env n m} {Σ A B j}
    → Γ , A ⊢ ⟨ j , B ⟩ ~ ↑Σ0 Σ
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ


----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

-- split a Apps by index k
data SplitApps : Apps n m → ℕ → Apps n m × Apps n m → Set where
  case-0 : ∀ {e̅ : Apps n m}
    → SplitApps e̅ 0 ⟨ nil , e̅ ⟩
  case-S : ∀ {e̅ : Apps n m} {e j e̅₁ e̅₂}
    → SplitApps e̅ j ⟨ e̅₁ , e̅₂ ⟩
    → SplitApps (e ∷a e̅) (suc j) ⟨ e ∷a e̅₁ , e̅₂ ⟩


-- (infs, chks)
data SplitAppsType : AppsType m → ℕ → AppsType m × AppsType m → Set where
  case-0 : ∀ {A̅ : AppsType m}
    → SplitAppsType A̅ 0 ⟨ nil , A̅ ⟩
  case-S : ∀ {A̅ : AppsType m} {A j A̅₁ A̅₂}
    → SplitAppsType A̅ j ⟨ A̅₁ , A̅₂ ⟩
    → SplitAppsType (A ∷a A̅) (suc j) ⟨ A ∷a A̅₁ , A̅₂ ⟩

infix 3 _⊢_⇇_
infix 3 _⊢_⇉_

data _⊢_⇇_ : Env n m → Apps n m → AppsType m → Set where
  case-0 : ∀ {Γ : Env n m}
    → Γ ⊢ nil ⇇ nil
  case-S : ∀ {Γ : Env n m} {e̅ A e A̅}
    → (⊢e : Γ ⊢ ∞ # e ⦂ A)
    → Γ ⊢ e̅ ⇇ A̅
    → Γ ⊢ e ∷a e̅ ⇇ A ∷a A̅

data _⊢_⇉_ : Env n m → Apps n m → AppsType m → Set where
  case-0 : ∀ {Γ : Env n m}
    → Γ ⊢ nil ⇉ nil
  case-S : ∀ {Γ : Env n m} {e̅ A e A̅}
    → (⊢e : Γ ⊢ Z # e ⦂ A)
    → Γ ⊢ e̅ ⇉ A̅
    → Γ ⊢ e ∷a e̅ ⇉ A ∷a A̅

postulate

  infs-w-m : ∀ {Γ : Env n m} {e̅ A̅}
    → 𝕄 (𝕎 Γ) ⊢ e̅ ⇉ A̅
    → Γ ⊢ e̅ ⇉ A̅
  chks-w-m : ∀ {Γ : Env n m} {e̅ A̅}
    → 𝕄 (𝕎 Γ) ⊢ e̅ ⇇ A̅
    → Γ ⊢ e̅ ⇇ A̅

-- context can only be empty for full type, come from the split result
data MakeCounter : ℕ → Context n m → Counter → Set where
  mk-empty : MakeCounter 0 (Context n m ∋⦂ □) Z
  mk-type  : ∀ {A} → MakeCounter 0 (Context n m ∋⦂ (τ A)) ∞
  mk-S     : ∀ {Σ : Context n m} {k j}
    → MakeCounter k Σ j
    → MakeCounter (suc k) Σ (I j)


    
    
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

sound : ∀ {Γ : Env n m} {Σ e A}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → JustTyping Γ Σ e A

sound-s : ∀ {Ψ Ψ' : SEnv n m} {Σ A B}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → JustSub Ψ' Σ A B

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
sound-s (s-ex-l^ clo x-in inst) = subs ~∞ (s-var-l {!!} s-refl-∞) -- ok
sound-s (s-ex-l= clo x-in s) with sound-s s
... | subs ~∞ s' = subs ~∞ (s-var-l {!!} s') -- ok
sound-s (s-ex-r^ clo x-in inst) = subs ~∞ (s-var-r {!!} s-refl-∞) -- ok
sound-s (s-ex-r= clo x-in s) with sound-s s
... | subs ~∞ s' = subs ~∞ (s-var-r {!!} s') -- ok
sound-s (s-arr s s₁) with sound-s s | sound-s s₁
... | subs ~∞ s₂ | subs ~∞ s₃ = subs ~∞ (s-arr₁ {!!} {!!}) -- ok, the subtyping relation is preserved during the env extension
sound-s (s-term-c cloA cloB ⊢e s) with sound-s s
... | subs j~Σ s' rewrite ⊢id0 ⊢e = subs (~C {!sound-∞ ⊢e!} j~Σ) (s-arr₃ s') -- ok, typing is preserved during the env extension
sound-s (s-term-o op ⊢e s s₁) with sound-s s | sound-s s₁
... | subs ~∞ s'' | subs j~Σ s' rewrite ≤id0 s = subs (~I (sound-0 {!⊢e!}) j~Σ) (s-arr₂ {!s''!} s') -- ok, same as above
sound-s (s-∀ s) with sound-s s
... | subs ~∞ s' = subs ~∞ (s-∀ s')
sound-s (s-∀l-^ s) with sound-s s
... | subs j~Σ s' = subs {!j~Σ!} {!s'!}
sound-s (s-∀l-eq s st₁ st₂) with sound-s s
... | subs j~Σ s' = subs {!j~Σ!} {!!}
