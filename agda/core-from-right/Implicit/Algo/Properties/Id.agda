{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}
module Implicit.Algo.Properties.Id where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Subst

data Id : Context n m → Type m → Set where
  id-□ : Id (Context n m ∋⦂ □) A
  id-τ : Id (Context n m ∋⦂ τ A) A
  id-e : Id Σ B
       → Id ([ e ]↝ Σ) (A `→ B)
  id-⓪ : Id Σ B*
       → (st : ⟦ A ⟧ B ⇘ B*)
       → Id (A ⓪↝ Σ) (`∀ B)

id-st' : Id Σ A
       → ⟦ k / T ⟧ᶜ Σ ⇘ Σ*
       → ⟦ k / T ⟧ A ⇘ A*
       → Id Σ* A*
id-st' id-□ empty stA = id-□
id-st' id-τ (fulltype st) stA with refl ← st-unique st stA = id-τ
id-st' (id-e id₁) (term stc ste) (st-arr stA stA₁) = id-e (id-st' id₁ stc stA₁)
id-st' {k = k} {T} (id-⓪ {B* = B*} id₁ st) (tapp stc x) (st-∀ up stA)
  with ⟨ B*' , stB* ⟩ ← st-total T k B* = id-⓪ (id-st' id₁ stc stB*) (st-st-comm z≤n st stB* up stA x)

id-↑tm : Id Σ' A
       → Σ ↑tmᶜ k ⇘ Σ'
       → Id Σ A
id-↑tm id-□ ↑tmᶜ-□ = id-□
id-↑tm id-τ ↑tmᶜ-τ = id-τ
id-↑tm (id-e id₁) (↑tmᶜ-e up-e upΣ) = id-e (id-↑tm id₁ upΣ)
id-↑tm (id-⓪ id₁ st) (↑tmᶜ-⓪ upΣ) = id-⓪ (id-↑tm id₁ upΣ) st

⊢id' : Γ ⊢ Σ ⇒ e ⇒ A
     → Id Σ A

s-id' : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
      → Id Σ B

⊢id' (⊢lit regΓ) = id-□
⊢id' (⊢var regΓ x∈Γ) = id-□
⊢id' (⊢ann ⊢e) = id-□
⊢id' (⊢app ⊢e) with ⊢id' ⊢e
... | id-e r = r
⊢id' (⊢lam₁ ⊢e) with ⊢id' ⊢e
... | id-τ = id-τ
⊢id' (⊢lam₂ ⊢e up-c ⊢e₁) with ⊢id' ⊢e₁
... | r = id-e (id-↑tm r up-c)
⊢id' (⊢sub ⊢e ne gc s) = s-id' s
⊢id' (⊢tabs ⊢e) = id-□
⊢id' (⊢tapp ⊢e st') with ⊢id' ⊢e
... | id-⓪ r st
  with refl ← st-unique st st' = r

s-id' (s-empty regΓ cloA grd) = id-□
s-id' (s-type ss) = id-τ
s-id' (s-term-c cloA ap ⊢e s) = id-e (s-id' s)
s-id' (s-term-o opnA ⊢e ss s) = id-e (s-id' s)
s-id' (s-∀l s upᶜ upᵉ upC upD) with s-id' s
... | id-e r = id-e (id-st' {T = Int} r (↑tyᶜ-st upᶜ) (↑ty-st upD))
s-id' (s-∀l-no s upᶜ upᵉ upC upD) with s-id' s
... | id-e r = id-e (id-st' {T = Int} r (↑tyᶜ-st upᶜ) (↑ty-st upD))
s-id' (s-tapp {B = B} {C = C} s upᶜ)
  with ⟨ B* , stB ⟩ ← st0-total B C = id-⓪ (id-st' (s-id' s) (↑tyᶜ-st upᶜ) stB) stB

⊢id0 : Γ ⊢ τ B ⇒ e ⇒ A
     → B ≡ A
⊢id0 ⊢e with ⊢id' ⊢e
... | id-τ = refl

s-id0 : Γ ⊢ A ≤⁺ τ B ⊣ Γ' ↪ C
      → B ≡ C
s-id0 (s-type ss) = refl
