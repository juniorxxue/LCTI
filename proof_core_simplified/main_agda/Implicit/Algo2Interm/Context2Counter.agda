module Implicit.Algo2Interm.Context2Counter where

open import Implicit.Language.All
open import Implicit.Interm.All
open import Implicit.Algo.All
open import Implicit.Algo2Interm.AlgoCounter.All

infix 3 _⊢_~t_
data _⊢_~t_ : Env n m → Counter × Type m → Context n m → Set where

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

infix 3 _⊢_~inf_
data _⊢_~inf_ : Env n m → Counter × Type m → Context n m → Set where

  ~i∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~inf τ A

  ~iI : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ Z # e ⦂ A)
    → Γ ⊢ ⟨ j , B ⟩ ~inf Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ~inf ([ e ]↝ Σ)


infix 3 _⊢_~s_
data _⊢_~s_ : Env n m → Counter × Type m → Context n m → Set where

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

~s-~t : Γ ⊢ ⟨ j , A ⟩ ~s Σ
      → 𝕣 Γ ⊢ ⟨ j , A ⟩ ~t Σ
~s-~t ~sZ = ~tZ
~s-~t ~s∞ = ~t∞
~s-~t (~sI ⊢e ~s) = ~tI ⊢e (~s-~t ~s)
~s-~t (~sC ⊢e ~s) = ~tC ⊢e (~s-~t ~s)

~t-~s : 𝕣 Γ ⊢ ⟨ j , A ⟩ ~t Σ
      → Γ ⊢ ⟨ j , A ⟩ ~s Σ
~t-~s ~tZ = ~sZ
~t-~s ~t∞ = ~s∞
~t-~s (~tI ⊢e ~t) = ~sI ⊢e (~t-~s ~t )
~t-~s (~tC ⊢e ~t) = ~sC ⊢e (~t-~s ~t )

~infs-~t : Γ ⊢ ⟨ j , A ⟩ ~inf Σ
         → Γ ⊢ ⟨ j , A ⟩ ~t Σ
~infs-~t ~i∞ = ~t∞
~infs-~t (~iI ⊢e ~inf) = ~tI ⊢e (~infs-~t ~inf)

~s-irrev-⊆ : Γ ⊢ ⟨ j , A ⟩ ~s Σ
           → Γ ⊆ Δ
           → Δ ⊢ ⟨ j , A ⟩ ~s Σ
~s-irrev-⊆ ~sZ ext = ~sZ
~s-irrev-⊆ ~s∞ ext = ~s∞
~s-irrev-⊆ (~sI ⊢e ~s) ext = ~sI (t-⊆-prv ⊢e ext) (~s-irrev-⊆ ~s ext)
~s-irrev-⊆ (~sC ⊢e ~s) ext = ~sC (t-⊆-prv ⊢e ext) (~s-irrev-⊆ ~s ext)

NonEmpty-NonZ : NonEmpty Σ
              → Γ ⊢ ⟨ j , A ⟩ ~t Σ
              → NonZ j
NonEmpty-NonZ ne-τ ~t∞ = nz-∞
NonEmpty-NonZ ne-app (~tI ⊢e j~Σ) = nz-I
NonEmpty-NonZ ne-app (~tC ⊢e j~Σ) = nz-C



~s-strengthen^0 : Γ ,^ ⊢ ⟨ j , A' ⟩ ~s Σ'
                 → ↑ty0 A ⇘ A'
                 → ↑tyᶜ0 Σ ⇘ Σ'
                 → Γ ⊢ ⟨ j , A ⟩ ~s Σ
~s-strengthen^0 ~sZ upA ↑tyᶜ-□ = ~sZ
~s-strengthen^0 ~s∞ upA (↑tyᶜ-τ up-t) with refl ← ↑ty-unique-inver upA up-t = ~s∞
~s-strengthen^0 (~sI ⊢e ~s) (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) = ~sI (t-strengthen^ ⊢e ◀Z up-e upA) (~s-strengthen^0 ~s upA₁ upΣ)
~s-strengthen^0 (~sC ⊢e ~s) (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) = ~sC (t-strengthen^ ⊢e ◀Z up-e upA) (~s-strengthen^0 ~s upA₁ upΣ)

~s-strengthen=0 : Γ ,= T ⊢ ⟨ j , A' ⟩ ~s Σ'
                 → ↑ty0 A ⇘ A'
                 → ↑tyᶜ0 Σ ⇘ Σ'
                 → Γ ⊢ ⟨ j , A ⟩ ~s Σ
~s-strengthen=0 ~sZ upA ↑tyᶜ-□ = ~sZ
~s-strengthen=0 ~s∞ upA (↑tyᶜ-τ up-t) with refl ← ↑ty-unique-inver upA up-t = ~s∞
~s-strengthen=0 (~sI ⊢e ~s) (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) = ~sI (t-strengthen= ⊢e ◀Z up-e upA) (~s-strengthen=0 ~s upA₁ upΣ)
~s-strengthen=0 (~sC ⊢e ~s) (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) = ~sC (t-strengthen= ⊢e ◀Z up-e upA) (~s-strengthen=0 ~s upA₁ upΣ)

~t-strengthen,0 : Γ , A ⊢ ⟨ j , B ⟩ ~t Σ'
                → ↑tmᶜ0 Σ ⇘ Σ'
                → Γ ⊢ ⟨ j , B ⟩ ~t Σ
~t-strengthen,0 ~tZ ↑tmᶜ-□ = ~tZ
~t-strengthen,0 ~t∞ ↑tmᶜ-τ = ~t∞
~t-strengthen,0 (~tI ⊢e ~t) (↑tmᶜ-e up-e upΣ) = ~tI (t-strengthen,0 ⊢e up-e) (~t-strengthen,0 ~t upΣ)
~t-strengthen,0 (~tC ⊢e ~t) (↑tmᶜ-e up-e upΣ) = ~tC (t-strengthen,0 ⊢e up-e) (~t-strengthen,0 ~t upΣ)
