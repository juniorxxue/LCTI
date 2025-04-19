module Implicit.Algo.Properties.WeakenTVar where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Id


postulate
  t-weaken, : Γ ⊢ Σ ⇒ e ⇒ A
          → Γ ▶ k , T ⇘ Γ'
          → Σ ↑tmᶜ k ⇘ Σ'
          → e ↑tm k ⇘ e'
          → Γ' ⊢ Σ' ⇒ e' ⇒ A

  s-weaken, : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
          → Σ ↑tmᶜ k ⇘ Σ'
          → Γ ⨟ Δ ▶s k , T ⇘ Γ' ⨟ Δ'
          → Γ' ⊢ A ≤⁺ Σ' ⊣ Δ' ↪ B

s-weaken,0 : Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Δ ⋈ ↪ B
           → ↑tmᶜ0 Σ ⇘ Σ'
           → Γ ⊢r T
           → Γ , T ⋈ ⊢ A ≤⁺ Σ' ⊣ Δ , T ⋈  ↪ B
s-weaken,0 s upΣ regT = s-weaken, s upΣ (▶sS⋈ (▶Z regT))

t-weaken,0 : Γ ⊢ Σ ⇒ e ⇒ A
           → ↑tmᶜ0 Σ ⇘ Σ'
           → ↑tm0 e ⇘ e'
           → Γ ⊢r T
           → Γ , T ⊢ Σ' ⇒ e' ⇒ A
t-weaken,0 ⊢e upΣ upe regT = t-weaken, ⊢e (▶Z regT) upΣ upe
