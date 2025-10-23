module Implicit.Interm2Algo.Counter2Context where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm.Base

----------------------------------------------------------------------
--+                       counter to context                       +--
----------------------------------------------------------------------

infix 3 _⊢_~s_
data _⊢_~s_ : Env n m → Mask × Type m → Context n m → Set where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ `■ , A ⟩ ~s □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ `□ , A ⟩ ~s τ A

  ~I : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : 𝕣 Γ ⊢ □ ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~s Σ
    → Γ ⊢ ⟨ □ · j , A `→ B ⟩ ~s ([ e ]↝ Σ)

  ~C : ∀ {Γ : Env n m} {j B Σ e}
    → (⊢e : 𝕣 Γ ⊢ τ A% ⇒ e ⇒ A%)
    → Γ ⊢ ⟨ j , B ⟩ ~s Σ
    → Γ ⊢ ⟨ ■ · j , A% `→ B ⟩ ~s ([ e ]↝ Σ)

infix 3 _⊢_~t_
data _⊢_~t_ : Env n m → Mask × Type m → Context n m → Set where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ `■ , A ⟩ ~t □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ `□ , A ⟩ ~t τ A

  ~I : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ □ ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~t Σ
    → Γ ⊢ ⟨ □ · j , A `→ B ⟩ ~t ([ e ]↝ Σ)

  ~C : ∀ {Γ : Env n m} {j B Σ e}
    → (⊢e : Γ ⊢ τ A% ⇒ e ⇒ A%)
    → Γ ⊢ ⟨ j , B ⟩ ~t Σ
    → Γ ⊢ ⟨ ■ · j , A% `→ B ⟩ ~t ([ e ]↝ Σ)

~weaken,0 : Γ ⊢ ⟨ j , B ⟩ ~t Σ
          → ↑tmᶜ0 Σ ⇘ Σ'
          → Γ ⊢r A
          → Γ , A ⊢ ⟨ j , B ⟩ ~t Σ'
~weaken,0 ~Z ↑tmᶜ-□ regA = ~Z
~weaken,0 ~∞ ↑tmᶜ-τ regA = ~∞
~weaken,0 (~I ⊢e j~Σ) (↑tmᶜ-e up-e upΣ) regA = ~I (t-weaken,0 ⊢e ↑tmᶜ-□ up-e regA) (~weaken,0 j~Σ upΣ regA)
~weaken,0 (~C ⊢e j~Σ) (↑tmᶜ-e up-e upΣ) regA = ~C (t-weaken,0 ⊢e ↑tmᶜ-τ up-e regA) (~weaken,0 j~Σ upΣ regA)


~weaken=0 : Γ ⊢ ⟨ j , A ⟩ ~s Σ
          → ↑ty0 A ⇘ A'
          → ↑tyᶜ0 Σ ⇘ Σ'
          → Γ ⊢r T
          → Γ ,= T ⊢ ⟨ j , A' ⟩ ~s Σ'
~weaken=0 ~Z upA ↑tyᶜ-□ regT = ~Z
~weaken=0 ~∞ upA (↑tyᶜ-τ up-t) regT
  with refl ← ↑ty-unique upA up-t = ~∞
~weaken=0 (~I ⊢e ~s) (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) regT =
  ~I (t-weaken= ⊢e (▶Z (⊢r-𝕣' regT)) ↑tyᶜ-□ up-e upA) (~weaken=0 ~s upA₁ upΣ regT)
~weaken=0 (~C ⊢e ~s) (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) regT =
  ~C (t-weaken= ⊢e (▶Z (⊢r-𝕣' regT)) (↑tyᶜ-τ upA) up-e upA) (~weaken=0 ~s upA₁ upΣ regT)

~weaken^0 : Γ ⊢ ⟨ j , A ⟩ ~s Σ
          → ↑ty0 A ⇘ A'
          → ↑tyᶜ0 Σ ⇘ Σ'
          → Γ ,^ ⊢ ⟨ j , A' ⟩ ~s Σ'
~weaken^0 ~Z upA ↑tyᶜ-□ = ~Z
~weaken^0 ~∞ upA (↑tyᶜ-τ up-t)
  with refl ← ↑ty-unique upA up-t = ~∞
~weaken^0 (~I ⊢e ~j) (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) = ~I (t-weaken^0 ⊢e ↑tyᶜ-□ up-e upA) (~weaken^0 ~j upA₁ upΣ)
~weaken^0 (~C ⊢e ~j) (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) = ~C (t-weaken^0 ⊢e (↑tyᶜ-τ upA) up-e upA) (~weaken^0 ~j upA₁ upΣ)

~t-~s : Γ ⊢ ⟨ j , B ⟩ ~t Σ
      → Γ ⋈ ⊢ ⟨ j , B ⟩ ~s Σ
~t-~s ~Z = ~Z
~t-~s ~∞ = ~∞
~t-~s (~I ⊢e j~Σ) = ~I ⊢e (~t-~s j~Σ)
~t-~s (~C ⊢e j~Σ) = ~C ⊢e (~t-~s j~Σ)

----------------------------------------------------------------------
--+                             Irrev                              +--
----------------------------------------------------------------------

~irrev : Γ ⊢ ⟨ j , D ⟩ ~s Σ
        → Γ ⊆ Ω
        → Ω ⊢ ⟨ j , D ⟩ ~s Σ
~irrev ~Z ext = ~Z
~irrev ~∞ ext = ~∞
~irrev (~I ⊢e ~j) ext = ~I (t-irrev-⊆ ⊢e ext) (~irrev ~j ext)
~irrev (~C ⊢e ~j) ext = ~C (t-irrev-⊆ ⊢e ext) (~irrev ~j ext)
