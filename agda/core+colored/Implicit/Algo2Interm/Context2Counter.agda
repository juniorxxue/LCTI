module Implicit.Algo2Interm.Context2Counter where

open import Implicit.Language.All
open import Implicit.Interm.All
open import Implicit.Algo.All
open import Implicit.Algo2Interm.AlgoCounter.All

infix 3 _⊢_~t_
data _⊢_~t_ : Env n m → Counter m × Type m → Context n m → Set where

  ~tZ : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~t □

  ~t∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~t τ A

  ~tI : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ Z # e ⦂ A)
    → Γ ⊢ ⟨ j , B ⟩ ~t Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ~t ([ e ]↝ Σ)

  ~tC : ∀ {Γ : Env n m} {j A B Σ e}
    (⊢e : Γ ⊢ ∞ # e ⦂ A)
    → Γ ⊢ ⟨ j , B ⟩ ~t Σ
    → Γ ⊢ ⟨ 𝕔 j , A `→ B ⟩ ~t ([ e ]↝ Σ)

  ~tT : Γ ⊢ ⟨ j , B* ⟩ ~t Σ
     → (st : ⟦ A ⟧ B ⇘ B*)
     → Γ ⊢ ⟨ 𝕋₍ A ₎ j , `∀ B ⟩ ~t A ⓪↝ Σ

infix 3 _⊢_~s_
data _⊢_~s_ : Env n m → Counter m × Type m → Context n m → Set where

  ~sZ : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~s □

  ~s∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~s τ A

  ~sI : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : 𝕣 Γ ⊢ Z # e ⦂ A)
    → Γ ⊢ ⟨ j , B ⟩ ~s Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ~s ([ e ]↝ Σ)

  ~sC : ∀ {Γ : Env n m} {j A B Σ e}
    (⊢e : 𝕣 Γ ⊢ ∞ # e ⦂ A)
    → Γ ⊢ ⟨ j , B ⟩ ~s Σ
    → Γ ⊢ ⟨ 𝕔 j , A `→ B ⟩ ~s ([ e ]↝ Σ)

  ~sT : Γ ⊢ ⟨ j , B* ⟩ ~s Σ
     → (st : ⟦ A ⟧ B ⇘ B*)
     → Γ ⊢ ⟨ 𝕋₍ A ₎ j , `∀ B ⟩ ~s A ⓪↝ Σ

~s-~t : Γ ⊢ ⟨ j , A ⟩ ~s Σ
      → 𝕣 Γ ⊢ ⟨ j , A ⟩ ~t Σ
~s-~t ~sZ = ~tZ
~s-~t ~s∞ = ~t∞
~s-~t (~sI ⊢e ~s) = ~tI ⊢e (~s-~t ~s)
~s-~t (~sC ⊢e ~s) = ~tC ⊢e (~s-~t ~s)
~s-~t (~sT ~s st) = ~tT (~s-~t ~s) st

NonEmpty-NonZ : NonEmpty Σ
              → Γ ⊢ ⟨ j , A ⟩ ~t Σ
              → NonZ j
NonEmpty-NonZ ne-τ ~t∞ = nz-∞
NonEmpty-NonZ ne-app (~tI ⊢e j~Σ) = nz-I
NonEmpty-NonZ ne-app (~tC ⊢e j~Σ) = nz-C
NonEmpty-NonZ ne-tapp (~tT ~J st) = nz-T



~s-strengthen=0 : Γ ,= T ⊢ ⟨ j' , A' ⟩ ~s Σ'
                 → ↑ty0 A ⇘ A'
                 → ↑tyᶜ0 Σ ⇘ Σ'
                 → ↑tyʲ0 j ⇘ j'
                 → Γ ⊢ ⟨ j , A ⟩ ~s Σ
~s-strengthen=0 ~sZ upA ↑tyᶜ-□ ↑tyʲ-Z = ~sZ
~s-strengthen=0 ~s∞ upA (↑tyᶜ-τ up-t) ↑tyʲ-∞ with refl ← ↑ty-unique-inver upA up-t = ~s∞
~s-strengthen=0 (~sI ⊢e ~s) (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) (↑tyʲ-𝕚 upj) = ~sI (t-strengthen= ⊢e ◀Z up-e upA ↑tyʲ-Z) (~s-strengthen=0 ~s upA₁ upΣ upj)
~s-strengthen=0 (~sC ⊢e ~s) (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) (↑tyʲ-𝕔 upj) = ~sC (t-strengthen= ⊢e ◀Z up-e upA ↑tyʲ-∞) (~s-strengthen=0 ~s upA₁ upΣ upj)
~s-strengthen=0 (~sT ~s st) (↑ty-∀ {A = C} upA) (↑tyᶜ-⓪ x upΣ) (↑tyʲ-𝕋 {A = A} upj upA₁) with refl ← ↑ty-unique-inver upA₁ x
  with ⟨ C* , stC ⟩ ← st0-total A C
  = ~sT (~s-strengthen=0 ~s (↑ty-st-comm0' stC x upA st) upΣ upj) stC
{-
~s-strengthen=0 ~sZ upA ↑tyᶜ-□ = ~sZ
~s-strengthen=0 ~s∞ upA (↑tyᶜ-τ up-t) with refl ← ↑ty-unique-inver upA up-t = ~s∞
~s-strengthen=0 (~sI ⊢e ~s) (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) = ~sI (t-strengthen= ⊢e ◀Z up-e upA) (~s-strengthen=0 ~s upA₁ upΣ)
~s-strengthen=0 (~sC ⊢e ~s) (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) = ~sC (t-strengthen= ⊢e ◀Z up-e upA) (~s-strengthen=0 ~s upA₁ upΣ)
-}

~t-strengthen,0 : Γ , A ⊢ ⟨ j , B ⟩ ~t Σ'
                → ↑tmᶜ0 Σ ⇘ Σ'
                → Γ ⊢ ⟨ j , B ⟩ ~t Σ
~t-strengthen,0 ~tZ ↑tmᶜ-□ = ~tZ
~t-strengthen,0 ~t∞ ↑tmᶜ-τ = ~t∞
~t-strengthen,0 (~tI ⊢e ~t) (↑tmᶜ-e up-e upΣ) = ~tI (t-strengthen,0 ⊢e up-e) (~t-strengthen,0 ~t upΣ)
~t-strengthen,0 (~tC ⊢e ~t) (↑tmᶜ-e up-e upΣ) = ~tC (t-strengthen,0 ⊢e up-e) (~t-strengthen,0 ~t upΣ)
~t-strengthen,0 (~tT ~t st) (↑tmᶜ-⓪ upΣ) = ~tT (~t-strengthen,0 ~t upΣ) st
