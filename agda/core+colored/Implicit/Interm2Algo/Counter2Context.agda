module Implicit.Interm2Algo.Counter2Context where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm.Base

----------------------------------------------------------------------
--+                       counter to context                       +--
----------------------------------------------------------------------

infix 3 _~₁_
data _~₁_ : ℕ × Type m → ParType m → Set where
  ~₁Z : ⟨ 0 , A ⟩ ~₁ □
  ~₁S : ⟨ i , B ⟩ ~₁ P
      → ⟨ suc i , A `→ B ⟩ ~₁ A ◐↝ P

infix 3 _~₂_
data _~₂_ : ENat × Type m → EContext m → Set where
  ~₂∞ : ⟨ ∞ , A ⟩ ~₂ τ A
  ~₂p : ⟨ i , A ⟩ ~₁ P
      → ⟨ 𝕟 i , A ⟩ ~₂ p P

infix 3 _⊢_~s_
data _⊢_~s_ : Env n m → Counter m × Type m → Context n m → Set where
  ~𝔼 : ⟨ 𝕖 , A ⟩ ~₂ δ
     → Γ ⊢ ⟨ 𝔼 𝕖 , A ⟩ ~s 𝔼 δ
  ~𝕊 : ⟨ 𝕖 , A ⟩ ~₂ δ
     → (⊢e : 𝕣 Γ ⊢ 𝔼 δ ⇒ e ⇒ A)
     → Γ ⊢ ⟨ j , B ⟩ ~s Σ
     → Γ ⊢ ⟨ 𝕊₍ 𝕖 ₎ j , A `→ B ⟩ ~s [ e ]↝ Σ
  ~𝕋 : Γ ⊢ ⟨ j , B* ⟩ ~s Σ
     → (st : ⟦ A ⟧ B ⇘ B*)
     → Γ ⊢ ⟨ 𝕋₍ A ₎ j , `∀ B ⟩ ~s A ⓪↝ Σ

infix 3 _⊢_~t_
data _⊢_~t_ : Env n m → Counter m × Type m → Context n m → Set where
  ~𝔼 : ⟨ 𝕖 , A ⟩ ~₂ δ
     → Γ ⊢ ⟨ 𝔼 𝕖 , A ⟩ ~t 𝔼 δ
  ~𝕊 : ⟨ 𝕖 , A ⟩ ~₂ δ
     → (⊢e : Γ ⊢ 𝔼 δ ⇒ e ⇒ A)
     → Γ ⊢ ⟨ j , B ⟩ ~t Σ
     → Γ ⊢ ⟨ 𝕊₍ 𝕖 ₎ j , A `→ B ⟩ ~t [ e ]↝ Σ
  ~𝕋 : Γ ⊢ ⟨ j , B* ⟩ ~t Σ
     → (st : ⟦ A ⟧ B ⇘ B*)
     → Γ ⊢ ⟨ 𝕋₍ A ₎ j , `∀ B ⟩ ~t A ⓪↝ Σ

postulate
  ~weaken,0 : Γ ⊢ ⟨ j , B ⟩ ~t Σ
          → ↑tmᶜ0 Σ ⇘ Σ'
          → Γ ⊢r A
          → Γ , A ⊢ ⟨ j , B ⟩ ~t Σ'


  ~weaken=0 : Γ ⊢ ⟨ j , A ⟩ ~s Σ
          → ↑ty0 A ⇘ A'
          → ↑tyᶜ0 Σ ⇘ Σ'
          → ↑tyʲ0 j ⇘ j'
          → Γ ⊢r T
          → Γ ,= T ⊢ ⟨ j' , A' ⟩ ~s Σ'


  ~weaken^0 : Γ ⊢ ⟨ j , A ⟩ ~s Σ
          → ↑ty0 A ⇘ A'
          → ↑tyᶜ0 Σ ⇘ Σ'
          → ↑tyʲ0 j ⇘ j'
          → Γ ,^ ⊢ ⟨ j' , A' ⟩ ~s Σ'

~t-~s : Γ ⊢ ⟨ j , B ⟩ ~t Σ
      → Γ ⋈ ⊢ ⟨ j , B ⟩ ~s Σ
~t-~s (~𝔼 x) = ~𝔼 x
~t-~s (~𝕊 x ⊢e ~j) = ~𝕊 x ⊢e (~t-~s ~j)
~t-~s (~𝕋 ~j st) = ~𝕋 (~t-~s ~j) st

----------------------------------------------------------------------
--+                             Irrev                              +--
----------------------------------------------------------------------

postulate
  ~irrev : Γ ⊢ ⟨ j , D ⟩ ~s Σ
        → Γ ⊆ Ω
        → Ω ⊢ ⟨ j , D ⟩ ~s Σ
