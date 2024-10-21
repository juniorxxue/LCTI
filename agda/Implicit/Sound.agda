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



----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

-- split a Apps by index k
data SplitApps : Apps n m → Counter → Apps n m × Apps n m → Set where
  case-0 : ∀ {e̅ : Apps n m}
    → SplitApps e̅ Z ⟨ nil , e̅ ⟩
  case-∞ : ∀ {e̅ : Apps n m}
    → SplitApps e̅ ∞ ⟨ nil , e̅ ⟩
  case-S : ∀ {e̅ : Apps n m} {e j e̅₁ e̅₂}
    → SplitApps e̅ j ⟨ e̅₁ , e̅₂ ⟩
    → SplitApps (e ∷a e̅) (S j) ⟨ e ∷a e̅₁ , e̅₂ ⟩


-- (infs, chks)
data SplitAppsType : AppsType m → Counter → AppsType m × AppsType m → Set where
  case-0 : ∀ {A̅ : AppsType m}
    → SplitAppsType A̅ Z ⟨ nil , A̅ ⟩
  case-∞ : ∀ {A̅ : AppsType m}
    → SplitAppsType A̅ ∞ ⟨ nil , A̅ ⟩
  case-S : ∀ {A̅ : AppsType m} {A j A̅₁ A̅₂}
    → SplitAppsType A̅ j ⟨ A̅₁ , A̅₂ ⟩
    → SplitAppsType (A ∷a A̅) (S j) ⟨ A ∷a A̅₁ , A̅₂ ⟩

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

data AppsCheck : Apps n m → AppsType m → Set where
  case-0 : 
      AppsCheck (Apps n m ∋⦂ nil) nil
  case-S : ∀ {e : Term n m} {Γ e̅ A A̅ B}
    → Γ ⊢ τ A ⇒ e ⇒ B
    → AppsCheck e̅ A̅
    → AppsCheck (e ∷a e̅) (A ∷a A̅)

data FineSplits (Ψ : SEnv n m) (A : Type m) (Σ : Context n m) : Set where
  fines : ∀ {j e̅ e̅₁ e̅₂ A̅₁ A̅₂ A' Σ' A̅}
    → (spl : ⟦ Σ , A ⟧→⟦ e̅ , Σ' , A̅ , A' ⟧)
    → (spl-apps : SplitApps e̅ j ⟨ e̅₁ , e̅₂ ⟩)
    → (spl-appst : SplitAppsType A̅ j ⟨ A̅₁ , A̅₂ ⟩)
    → (infs : 𝕄 Ψ ⊢ e̅₁ ⇉ A̅₁)
    → (chks : 𝕄 Ψ ⊢ e̅₂ ⇇ A̅₂)
    → FineSplits Ψ A Σ

data JustSub (Ψ : SEnv n m) (Σ : Context n m) (A : Type m) (B : Type m) : Set where
  subs : ∀ {e̅ Σ' B̅ B' B̅₁ B̅₂ e̅₁ e̅₂ j}
    → (spl : ⟦ Σ , B ⟧→⟦ e̅ , Σ' , B̅ , B' ⟧)
    → (spl-apps : SplitApps e̅ j ⟨ e̅₁ , e̅₂ ⟩)
    → (spl-appst : SplitAppsType B̅ j ⟨ B̅₁ , B̅₂ ⟩)
    → (infs : 𝕄 Ψ ⊢ e̅₁ ⇉ B̅₁)
    → (chks : 𝕄 Ψ ⊢ e̅₂ ⇇ B̅₂)
    → 𝕄 Ψ ⊢ j # A ≤ B
    → JustSub Ψ Σ A B


sound-≤ : ∀ {Ψ Ψ' : SEnv n m} {Σ A B}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → JustSub Ψ' Σ A B
sound-≤ s-int = subs none-τ case-0 case-0 case-0 case-0 s-refl
sound-≤ (s-empty p) = subs none-□ case-0 case-0 case-0 case-0 s-refl
sound-≤ s-var = subs none-τ case-0 case-0 case-0 case-0 s-refl
sound-≤ (s-ex-l^ clo x-in inst) = subs {j = ∞} none-τ case-∞ case-∞ case-0 case-0 (s-var-l {!!} s-refl-∞)
sound-≤ (s-ex-l= clo x-in s) = {!!}
sound-≤ (s-ex-r^ clo x-in inst) = {!!}
sound-≤ (s-ex-r= clo x-in s) = {!!}
sound-≤ (s-arr s s₁) = {!!}
sound-≤ (s-term-c cloA cloB ⊢e s) = {!!}
sound-≤ (s-term-o op ⊢e s s₁) = {!!}
sound-≤ (s-∀ s) = {!!}
sound-≤ (s-∀l-^ s) = {!!}
sound-≤ (s-∀l-eq s st₁ st₂) = {!!}

-- there might be an intermediate form n that connects

app-elim : ∀ {Γ : Env n m} {j A̅ A' Σ A e e̅ Σ' e̅₁ e̅₂ A̅₁ A̅₂}
  → Γ ⊢ j # e ⦂ A
  → (spl : ⟦ Σ , A ⟧→⟦ e̅ , □ , A̅ , A' ⟧)
  → (spl-apps : SplitApps e̅ j ⟨ e̅₁ , e̅₂ ⟩)
  → (spl-appst : SplitAppsType A̅ j ⟨ A̅₁ , A̅₂ ⟩)
  → (infs : Γ ⊢ e̅₁ ⇉ A̅₁)
  → (chks : Γ ⊢ e̅₂ ⇇ A̅₂)
  → Γ ⊢ Z # e ▻ e̅ ⦂ A'
app-elim ⊢e none-□ case-∞ case-∞ case-0 case-0 = {!!}
app-elim ⊢e (have-e spl) spl-apps case-∞ case-0 (case-S ⊢e' chks) = {!!}
app-elim ⊢e none-□ case-0 case-0 case-0 case-0 = ⊢e
app-elim ⊢e (have-e spl) case-0 case-0 case-0 (case-S ⊢e' chks) = app-elim (⊢app₁ ⊢e ⊢e') spl case-0 case-0 case-0 chks
app-elim ⊢e (have-e spl) (case-S spl-apps) (case-S spl-appst) (case-S ⊢e' infs) chks = app-elim (⊢app₂ ⊢e ⊢e') spl spl-apps spl-appst infs chks

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

t-e̅ : ∀ {Ψ Ψ' : SEnv n m} {Σ A B}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → FineSplits Ψ' B Σ
  
t-e̅ s-int = fines none-τ case-0 case-0 case-0 case-0
t-e̅ (s-empty p) = fines none-□ case-0 case-0 case-0 case-0
t-e̅ s-var = fines none-τ case-0 case-0 case-0 case-0
t-e̅ (s-ex-l^ clo x-in inst) = fines none-τ case-0 case-0 case-0 case-0
t-e̅ (s-ex-l= clo x-in s) = fines none-τ case-0 case-0 case-0 case-0
t-e̅ (s-ex-r^ clo x-in inst) = fines none-τ case-0 case-0 case-0 case-0
t-e̅ (s-ex-r= clo x-in s) = fines none-τ case-0 case-0 case-0 case-0
t-e̅ (s-arr s s₁) = fines none-τ case-0 case-0 case-0 case-0
t-e̅ (s-term-c cloA cloB ⊢e s) with t-e̅ s
... | fines {j = j} spl spl-apps spl-appst infs chks = {!!} -- j must be a Z
t-e̅ (s-term-o op ⊢e s s₁) with t-e̅ s₁
... | fines {j = j} spl spl-apps spl-appst infs chks = fines {j = S j} (have-e spl) (case-S spl-apps) (case-S spl-appst) (case-S {!!} infs) chks -- ok
t-e̅ (s-∀ s) = fines none-τ case-0 case-0 case-0 case-0
t-e̅ (s-∀l-^ s) = {!!}
t-e̅ (s-∀l-eq s st₁ st₂) with t-e̅ s
... | fines spl spl-apps spl-appst infs chks = fines {!!} case-0 case-0 case-0 case-0


sound-i ⊢lit none-□ = ⊢lit
sound-i (⊢var x∈Γ) none-□ = ⊢var x∈Γ
sound-i (⊢ann ⊢e) none-□ = ⊢ann (sound-c-0 ⊢e)
sound-i (⊢app ⊢e) spl = sound-i ⊢e (have-e spl)
sound-i {e̅ = e ∷a e̅} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = subst e̅ (sound-i ⊢e₁ (spl-weaken spl)) (sound-i-0 ⊢e)

sound-i (⊢sub ⊢e ne gc s) spl = {!!}


sound-i (⊢tabs ⊢e) none-□ = ⊢tabs (sound-i-0 ⊢e)

sound-c (⊢app ⊢e) spl = sound-c ⊢e (have-e spl)
sound-c (⊢lam₁ ⊢e) none-τ = ⊢lam₁ (sound-c-0 ⊢e)
sound-c {e̅ = e ∷a e̅} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = subst e̅ (sound-c ⊢e₁ (spl-weaken spl)) (sound-i-0 ⊢e)
sound-c (⊢sub ⊢e ne gc s) spl = {!!}
