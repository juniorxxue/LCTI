module Implicit.Algo.Properties.Id where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Subst
open import Implicit.Algo.Properties.Regularity

data Id : Context n m → Type m → Set where
  id-□ : Id (Context n m ∋⦂ □) A
  id-τ : Id (Context n m ∋⦂ τ A) A
  id-e : Id Σ B
       → Id ([ e ]↝ Σ) (A `→ B)
  id-⓪ : Id Σ B
       → (up : ↑ty0 B ⇘ B')
       → Id (A ⓪↝ Σ) (`∀ B')

id-↑tm : Id Σ' A
       → Σ ↑tmᶜ k ⇘ Σ'
       → Id Σ A
id-↑tm id-□ ↑tmᶜ-□ = id-□
id-↑tm id-τ ↑tmᶜ-τ = id-τ
id-↑tm (id-e id₁) (↑tmᶜ-e up-e upΣ) = id-e (id-↑tm id₁ upΣ)
id-↑tm (id-⓪ id₁ st) (↑tmᶜ-⓪ upΣ) = id-⓪ (id-↑tm id₁ upΣ) st

id-st' : Id Σ A
       → ⟦ k / T ⟧ᶜ Σ ⇘ Σ*
       → ⟦ k / T ⟧ A ⇘ A*
       → Id Σ* A*
id-st' id-□ empty stA = id-□
id-st' id-τ (fulltype st) stA with refl ← st-unique st stA = id-τ
id-st' (id-e id₁) (term stc ste) (st-arr stA stA₁) = id-e (id-st' id₁ stc stA₁)
id-st' {k = k} {T} (id-⓪ {B = B} {B' = B'} id₁ st) (tapp stc x) (st-∀ up stA)
   with ⟨ B* , stB ⟩ ← st-total T k B
   = id-⓪ (id-st' id₁ stc stB) (↑ty-st-comm1 z≤n stB up st stA)


id-↑ty : Id Σ' A'
       → Σ ↑tyᶜ k ⇘ Σ'
       → A ↑ty k ⇘ A'
       → Id Σ A
id-↑ty id upΣ upA = id-st' {T = Int} id (↑tyᶜ-st upΣ) (↑ty-st upA)


⊢id' : Γ ⊢ Σ ⇒ e ⇒ A
     → Id Σ A

s-id' : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
      → Id Σ B

infs-id' : Γ ⊨ Σ ⟹ A
         → Id Σ A

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
⊢id' (⊢tabs-τ ⊢e) with ⊢id' ⊢e
... | id-τ = id-τ
⊢id' (⊢tapp ⊢e st') with ⊢id' ⊢e
... | id-⓪ r st
  with refl ← ↑ty-unique-inver st st' = r

s-id' (s-empty regΓ cloA grd) = id-□
s-id' (s-type ss) = id-τ
s-id' (s-term-c cloA ap ⊢e s) = id-e (s-id' s)
s-id' (s-term-o opnA ⊢e ss s) = id-e (s-id' s)
-- s-id' (s-tapp {B = B} {C = C} s upᶜ)
-- with ⟨ B* , stB ⟩ ← st0-total B C = id-⓪ (id-st' (s-id' s) (↑tyᶜ-st upᶜ) stB) stB
s-id' (s-svar-term inΓ s) = s-id' s
s-id' (s-svar-tapp inΓ s) = s-id' s
s-id' (s-evar-infers infs inst) = infs-id' infs
s-id' s'@(s-∀l-y pk upB x upᶜ upᵉ upC upD) = id-↑ty (s-id' x) (↑tyᶜ-e upᵉ upᶜ) (↑ty-arr upC upD)
s-id' (s-∀l-n-y ¬pk x upᶜ upᵉ upC upD) = id-↑ty (s-id' x) (↑tyᶜ-e upᵉ upᶜ) (↑ty-arr upC upD)
s-id' (s-∀l-n-n ¬pk x upᶜ upᵉ upC upD) = id-↑ty (s-id' x) (↑tyᶜ-e upᵉ upᶜ) (↑ty-arr upC upD)
s-id' (s-tapp x upᶜ)
  with regC ← s-⊢r x
  with ¬inC ← ⊢r-=∈-¬ε regC Z
  with ⟨ pC , upC' ⟩ ← ↑ty-surjective ¬inC
  = id-⓪ (id-↑ty (s-id' x) upᶜ upC') upC'

infs-id' (infs-z regΓ regA) = id-τ
infs-id' (infs-s x infs) = id-e (infs-id' infs)


⊢id0 : Γ ⊢ τ B ⇒ e ⇒ A
     → B ≡ A
⊢id0 ⊢e with ⊢id' ⊢e
... | id-τ = refl

s-id0 : Γ ⊢ A ≤⁺ τ B ⊣ Γ' ↪ C
      → B ≡ C
s-id0 (s-type ss) = refl
