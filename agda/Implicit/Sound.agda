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
  case-S : ∀ {e̅ : Apps n m} {e j e̅₁ e̅₂}
    → SplitApps e̅ j ⟨ e̅₁ , e̅₂ ⟩
    → SplitApps (e ∷a e̅) (S j) ⟨ e ∷a e̅₁ , e̅₂ ⟩

data SplitAppsType : AppsType m → Counter → AppsType m × AppsType m → Set where
  case-0 : ∀ {A̅ : AppsType m}
    → SplitAppsType A̅ Z ⟨ nil , A̅ ⟩
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

data FineSplits (Ψ : SEnv n m) (e̅ : Apps n m) (A̅ : AppsType m) : Set where
  fines : ∀ {j e̅₁ e̅₂ A̅₁ A̅₂}
    → (spl-apps : SplitApps e̅ j ⟨ e̅₁ , e̅₂ ⟩)
    → (spl-appst : SplitAppsType A̅ j ⟨ A̅₁ , A̅₂ ⟩)
    → (infs : 𝕄 Ψ ⊢ e̅₁ ⇉ A̅₁)
    → (chks : 𝕄 Ψ ⊢ e̅₂ ⇇ A̅₂)
    → FineSplits Ψ e̅ A̅


-- e̅ ≡ e̅₁ ++ e̅₂

app-elim : ∀ {Γ : Env n m} {j A̅ A' Σ A e e̅ Σ' e̅₁ e̅₂ A̅₁ A̅₂}
  → Γ ⊢ j # e ⦂ A
  → (spl : ⟦ Σ , A ⟧→⟦ e̅ , Σ' , A̅ , A' ⟧)
  → (spl-apps : SplitApps e̅ j ⟨ e̅₁ , e̅₂ ⟩)
  → (spl-appst : SplitAppsType A̅ j ⟨ A̅₁ , A̅₂ ⟩)
  → (infs : Γ ⊢ e̅₁ ⇉ A̅₁)
  → (chks : Γ ⊢ e̅₂ ⇇ A̅₂)
  → Γ ⊢ Z # e ▻ e̅ ⦂ A'
app-elim ⊢e none-□ case-0 case-0 case-0 case-0 = ⊢e
app-elim ⊢e none-τ case-0 case-0 case-0 case-0 = ⊢e
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


t-e̅ : ∀ {Ψ Ψ' : SEnv n m} {Σ A B e̅ Σ' B̅ B'}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → ⟦ Σ , B ⟧→⟦ e̅ , Σ' , B̅ , B' ⟧
  → FineSplits Ψ' e̅ B̅
  
t-e̅ s-int none-τ = fines case-0 case-0 case-0 case-0
t-e̅ (s-empty p) none-□ = fines case-0 case-0 case-0 case-0
t-e̅ s-var none-τ = fines case-0 case-0 case-0 case-0
t-e̅ (s-ex-l^ clo x-in inst) none-τ = fines case-0 case-0 case-0 case-0
t-e̅ (s-ex-l= clo x-in s) none-τ = t-e̅ s none-τ
t-e̅ (s-ex-r^ clo x-in inst) none-τ = fines case-0 case-0 case-0 case-0
t-e̅ (s-ex-r= clo x-in s) none-τ = t-e̅ s none-τ
t-e̅ (s-arr s s₁) none-τ = t-e̅ s₁ none-τ
t-e̅ (s-term-c cloA cloB ⊢e s) (have-e spl) with t-e̅ s spl
... | fines {j = j} spl-apps spl-appst infs chks = {!!} -- j can only be Z counter, since B is closed
t-e̅ (s-term-o op ⊢e s s₁) (have-e spl) with t-e̅ s₁ spl
... | fines {j = j} spl-apps spl-appst infs chks = fines {j = S j} (case-S spl-apps) (case-S spl-appst) (case-S {!!} infs) chks 
t-e̅ (s-∀ s) none-τ = fines case-0 case-0 case-0 case-0
t-e̅ (s-∀l-^ s) spl = {!t-e̅ s!}
t-e̅ (s-∀l-eq s st₁ st₂) spl = {!t-e̅ s!}


sound-i ⊢lit none-□ = ⊢lit
sound-i (⊢var x∈Γ) none-□ = ⊢var x∈Γ
sound-i (⊢ann ⊢e) none-□ = ⊢ann (sound-c-0 ⊢e)
sound-i (⊢app ⊢e) spl = sound-i ⊢e (have-e spl)
sound-i {e̅ = e ∷a e̅} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = subst e̅ (sound-i ⊢e₁ (spl-weaken spl)) (sound-i-0 ⊢e)

sound-i (⊢sub ⊢e ne gc s) spl with t-e̅ s spl
... | fines {j = j} spl-apps spl-appst infs chks = app-elim (⊢sub' (sound-i-0 ⊢e) {!!}) spl spl-apps spl-appst {!infs!} {!!}


sound-i (⊢tabs ⊢e) none-□ = ⊢tabs (sound-i-0 ⊢e)

sound-c (⊢app ⊢e) spl = sound-c ⊢e (have-e spl)
sound-c (⊢lam₁ ⊢e) none-τ = ⊢lam₁ (sound-c-0 ⊢e)
sound-c {e̅ = e ∷a e̅} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = subst e̅ (sound-c ⊢e₁ (spl-weaken spl)) (sound-i-0 ⊢e)
sound-c (⊢sub ⊢e ne gc s) spl with t-e̅ s spl
... | fines {j = j} spl-apps spl-appst infs chks = {!!}
