module Implicit.Sound where

open import Implicit.Common
open import Implicit.Decl
open import Implicit.Decl.Subst
open import Implicit.Decl.Properties
open import Implicit.Algo

----------------------------------------------------------------------
--+                             Split                              +--
----------------------------------------------------------------------

postulate

  spl-weaken : ∀ {Σ Σ' : Context n m} {A e̅ A̅ A' k}
    → ⟦ Σ , A ⟧→⟦ e̅ , Σ' , A̅ , A' ⟧
    → ⟦ ↑Σ k Σ , A ⟧→⟦ up k e̅ , ↑Σ k Σ' , A̅ , A' ⟧

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
    → MakeCounter (suc k) Σ (S j)

data AppsCheck : Apps n m → AppsType m → Set where
  case-0 : 
      AppsCheck (Apps n m ∋⦂ nil) nil
  case-S : ∀ {e : Term n m} {Γ e̅ A A̅ B}
    → Γ ⊢ τ A ⇒ e ⇒ B
    → AppsCheck e̅ A̅
    → AppsCheck (e ∷a e̅) (A ∷a A̅)

data JustSub (Ψ : SEnv n m) (Σ : Context n m) (A : Type m) (B : Type m) : Set where
  subs : ∀ {e̅ Σ' B̅ B' B̅₁ B̅₂ e̅₁ e̅₂ j k}
    → (spl : ⟦ Σ , B ⟧→⟦ e̅ , Σ' , B̅ , B' ⟧)
    → (spl-apps : SplitApps e̅ k ⟨ e̅₁ , e̅₂ ⟩)
    → (spl-appst : SplitAppsType B̅ k ⟨ B̅₁ , B̅₂ ⟩)
    → (mk-j : MakeCounter k Σ' j)
    → (infs : 𝕄 Ψ ⊢ e̅₁ ⇉ B̅₁)
    → (chks : 𝕄 Ψ ⊢ e̅₂ ⇇ B̅₂)
    → (sub : 𝕄 Ψ ⊢ j # A ≤ B)
    → JustSub Ψ Σ A B


-- there might be an intermediate form n that connects

app-elim : ∀ {Γ : Env n m} {j A̅ A' Σ A e e̅ e̅₁ e̅₂ A̅₁ A̅₂ k}
  → Γ ⊢ j # e ⦂ A
  → (spl : ⟦ Σ , A ⟧→⟦ e̅ , □ , A̅ , A' ⟧)
  → (spl-apps : SplitApps e̅ k ⟨ e̅₁ , e̅₂ ⟩)
  → (spl-appst : SplitAppsType A̅ k ⟨ A̅₁ , A̅₂ ⟩)
  → (mk : MakeCounter k (Context n m ∋⦂ □) j)
  → (infs : Γ ⊢ e̅₁ ⇉ A̅₁)
  → (chks : Γ ⊢ e̅₂ ⇇ A̅₂)
  → Γ ⊢ Z # e ▻ e̅ ⦂ A'
app-elim ⊢e none-□ case-0 case-0 mk-empty case-0 case-0 = ⊢e
app-elim ⊢e (have-e spl) case-0 case-0 mk-empty case-0 (case-S ⊢e₁ chks) = app-elim (⊢app₁ ⊢e ⊢e₁) spl case-0 case-0 mk-empty case-0 chks
app-elim ⊢e (have-e spl) (case-S spl-apps) (case-S spl-appst) (mk-S mk) (case-S ⊢e₁ infs) chks = app-elim (⊢app₂ ⊢e ⊢e₁) spl spl-apps spl-appst mk infs chks

app-elim' : ∀ {Γ : Env n m} {j A̅ A' Σ A e e̅ e̅₁ e̅₂ A̅₁ A̅₂ k C}
  → Γ ⊢ j # e ⦂ A
  → (spl : ⟦ Σ , A ⟧→⟦ e̅ , τ C , A̅ , A' ⟧)
  → (spl-apps : SplitApps e̅ k ⟨ e̅₁ , e̅₂ ⟩)
  → (spl-appst : SplitAppsType A̅ k ⟨ A̅₁ , A̅₂ ⟩)
  → (mk : MakeCounter k (Context n m ∋⦂ τ C) j)
  → (infs : Γ ⊢ e̅₁ ⇉ A̅₁)
  → (chks : Γ ⊢ e̅₂ ⇇ A̅₂)
  → Γ ⊢ ∞ # e ▻ e̅ ⦂ A'
app-elim' ⊢e none-τ case-0 case-0 mk-type case-0 case-0 = ⊢e
app-elim' ⊢e (have-e spl) case-0 case-0 mk-type case-0 (case-S ⊢e₁ chks) = app-elim' {!!} spl case-0 case-0 mk-type case-0 chks
app-elim' ⊢e (have-e spl) (case-S spl-apps) (case-S spl-appst) (mk-S mk) (case-S ⊢e₁ infs) chks = app-elim' (⊢app₂ ⊢e ⊢e₁) spl spl-apps spl-appst mk infs chks


----------------------------------------------------------------------
--+                          Main Logics                           +--
----------------------------------------------------------------------


sound-i : ∀ {Γ : Env n m} {Σ e e̅ A A' A̅}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ e̅ , □ , A̅ , A' ⟧
  → Γ ⊢ Z # e ▻ e̅ ⦂ A'

sound-c : ∀ {Γ : Env n m} {Σ e e̅ A A' A̅ T}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ e̅ , τ T , A̅ , A' ⟧
  → Γ ⊢ ∞ # e ▻ e̅ ⦂ T

sound-i-0 : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ □ ⇒ e ⇒ A
  → Γ ⊢ Z # e ⦂ A
sound-i-0 ⊢e = sound-i ⊢e none-□

sound-c-0 : ∀ {Γ : Env n m} {e A B}
  → Γ ⊢ τ B ⇒ e ⇒ A
  → Γ ⊢ ∞ # e ⦂ B
sound-c-0 ⊢e = sound-c ⊢e none-τ


sound-≤ : ∀ {Ψ Ψ' : SEnv n m} {Σ A B}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → JustSub Ψ' Σ A B

sound-i ⊢lit none-□ = ⊢lit
sound-i (⊢var x∈Γ) none-□ = ⊢var x∈Γ
sound-i (⊢ann ⊢e) none-□ = ⊢ann (sound-c-0 ⊢e)
sound-i (⊢app ⊢e) spl = sound-i ⊢e (have-e spl)
sound-i {e̅ = e ∷a e̅} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = subst e̅ (sound-i ⊢e₁ (spl-weaken spl)) (sound-i-0 ⊢e)

sound-i (⊢sub ⊢e ne gc s) spl with sound-≤ s
... | subs spl₁ spl-apps spl-appst mk-j infs chks sub with spl-unique spl spl₁
... | ⟨ refl , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩ = app-elim (⊢sub' (sound-i-0 ⊢e) (s-w-m sub)) spl spl-apps spl-appst mk-j (infs-w-m infs) (chks-w-m chks) -- ok


sound-i (⊢tabs ⊢e) none-□ = ⊢tabs (sound-i-0 ⊢e)

sound-c (⊢app ⊢e) spl = sound-c ⊢e (have-e spl)
sound-c (⊢lam₁ ⊢e) none-τ = ⊢lam₁ (sound-c-0 ⊢e)
sound-c {e̅ = e ∷a e̅} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = subst e̅ (sound-c ⊢e₁ (spl-weaken spl)) (sound-i-0 ⊢e)
sound-c ⊢e'@(⊢sub ⊢e ne gc s) spl rewrite ⊢spl-τ ⊢e' spl with sound-≤ s
... | subs spl₁ spl-apps spl-appst mk-j infs chks sub with spl-unique spl spl₁
... | ⟨ refl , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩ = ⊢sub' {!!} s-refl-∞

-- app-elim' (⊢sub' (sound-i-0 ⊢e) (s-w-m sub)) spl₁ spl-apps spl-appst mk-j (infs-w-m infs) (chks-w-m chks) -- ok

  
sound-≤ s-int = subs none-τ case-0 case-0 mk-type case-0 case-0 s-int
sound-≤ (s-empty p) = subs none-□ case-0 case-0 mk-empty case-0 case-0 s-refl
sound-≤ s-var = subs none-τ case-0 case-0 mk-type case-0 case-0 s-var
sound-≤ (s-ex-l^ clo x-in inst) = subs none-τ case-0 case-0 mk-type case-0 case-0 {!!}
sound-≤ (s-ex-l= clo x-in s) = subs none-τ case-0 case-0 mk-type case-0 case-0 {!!}
sound-≤ (s-ex-r^ clo x-in inst) = {!!}
sound-≤ (s-ex-r= clo x-in s) = {!!}
sound-≤ (s-arr s s₁) = subs none-τ case-0 case-0 mk-type case-0 case-0 (s-arr₁ {!!} {!!})
sound-≤ (s-term-c cloA cloB ⊢e s) with sound-≤ s
... | r = subs (have-e {!!}) {!!} {!!} {!!} {!!} {!!} {!!}
sound-≤ (s-term-o op ⊢e s s₁) = {!!}
sound-≤ (s-∀ s) = {!!}
sound-≤ (s-∀l-^ s) = {!!}
sound-≤ (s-∀l-eq s st₁ st₂) = {!!}

