module Implicit.Algo.Properties.OpenClose where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Lookup
open import Implicit.Algo.Properties.Extension

----------------------------------------------------------------------
--+                       Lemmas around ⊢cᶜ                        +--
----------------------------------------------------------------------

postulate
  ⊢cᶜ-strengthen0 : Γ , A ⊢cᶜ Σ'
                  → ↑tmᶜ0 Σ ⇘ Σ'
                  → Γ ⊢cᶜ Σ

----------------------------------------------------------------------
--+                           Extension                            +--
----------------------------------------------------------------------


⊆-closed : Γ ⊢c A
         → Γ ⊆ Γ'
         → Γ' ⊢c A
⊆-closed ⊢c-int ss = ⊢c-int
⊆-closed (⊢c-var-∙ x) ss = ⊢c-var-∙ (⊆-in∙ x ss)
⊆-closed (⊢c-var-= x) ss = ⊢c-var-= (⊆-in= x ss)
⊆-closed (⊢c-arr clo clo₁) ss = ⊢c-arr (⊆-closed clo ss) (⊆-closed clo₁ ss)
⊆-closed (⊢c-∀ clo) ss = ⊢c-∀ (⊆-closed clo (uvar ss))

⊆-closedᵉ : Γ ⊢cᵉ e
          → Γ ⊆ Γ'
          → Γ' ⊢cᵉ e
⊆-closedᵉ ⊢c-lit ss = ⊢c-lit
⊆-closedᵉ ⊢c-var ss = ⊢c-var
⊆-closedᵉ (⊢c-lam clo) ss = ⊢c-lam (⊆-closedᵉ clo (var ss))
⊆-closedᵉ (⊢c-app clo clo₁) ss = ⊢c-app (⊆-closedᵉ clo ss) (⊆-closedᵉ clo₁ ss)
⊆-closedᵉ (⊢c-ann x clo) ss = ⊢c-ann (⊆-closed x ss) (⊆-closedᵉ clo ss)
⊆-closedᵉ (⊢c-tlam clo) ss = ⊢c-tlam (⊆-closedᵉ clo (uvar ss))

⊆-closedᶜ : Γ ⊢cᶜ Σ
          → Γ ⊆ Γ'
          → Γ' ⊢cᶜ Σ
⊆-closedᶜ ⊢c-empty ss = ⊢c-empty
⊆-closedᶜ (⊢c-τ cloA) ss = ⊢c-τ (⊆-closed cloA ss)
⊆-closedᶜ (⊢c-term cloe clo) ss = ⊢c-term (⊆-closedᵉ cloe ss) (⊆-closedᶜ clo ss)



----------------------------------------------------------------------
--+                            Polarity                            +--
----------------------------------------------------------------------


polar-arr-l : Polarity Γ (A `→ B) (τ (C `→ D)) ≤
            → Polarity Γ C (τ A) (⋆ ≤)
polar-arr-l (polar-l (⊢c-arr cloA cloA₁)) = polar-r (⊢c-τ cloA)
polar-arr-l (polar-r (⊢c-τ (⊢c-arr cloA cloA₁))) = polar-l cloA

polar-arr-r : Polarity Γ (A `→ B) (τ (C `→ D)) ≤
            → Polarity Γ B (τ D) ≤
polar-arr-r (polar-l (⊢c-arr cloA cloA₁)) = polar-l cloA₁
polar-arr-r (polar-r (⊢c-τ (⊢c-arr cloA cloA₁))) = polar-r (⊢c-τ cloA₁)

polar-∀ : Polarity Γ (`∀ A) (τ (`∀ B)) ≤
        → Polarity (Γ ,∙) A (τ B) ≤
polar-∀ (polar-l (⊢c-∀ cloA)) = polar-l cloA
polar-∀ (polar-r (⊢c-τ (⊢c-∀ cloA))) = polar-r (⊢c-τ cloA)

polar-tm-r : Polarity Γ (A `→ B) ([ e ]↝ Σ) ≤
           → Polarity Γ B Σ ≤
polar-tm-r (polar-l (⊢c-arr cloA cloA₁)) = polar-l cloA₁
polar-tm-r (polar-r (⊢c-term cloe cloA)) = polar-r cloA

polar-⊆ : Polarity Γ A Σ ≤
        → Γ ⊆ Γ'
        → Polarity Γ' A Σ ≤
polar-⊆ (polar-l cloA) ss = polar-l (⊆-closed cloA ss)
polar-⊆ (polar-r cloA) ss = polar-r (⊆-closedᶜ cloA ss)

----------------------------------------------------------------------
--+                    Typing implies closeness                    +--
----------------------------------------------------------------------


⊢closeΓ : Γ ⊢ Σ ⇒ e ⇒ A
        → Closed Γ

⊢closeΣ : Γ ⊢ Σ ⇒ e ⇒ A
        → Γ ⊢cᶜ Σ

⊢closee : Γ ⊢ Σ ⇒ e ⇒ A
        → Γ ⊢cᵉ e

⊢closeA : Γ ⊢ Σ ⇒ e ⇒ A
        → Γ ⊢c A

-- inference result is closed under output env
s-closed : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
         → Polarity Γ A Σ ≤
         → Δ ⊢c B

⊢closeΓ (⊢lit cloΓ) = cloΓ
⊢closeΓ (⊢var cloΓ x∈Γ) = cloΓ
⊢closeΓ (⊢ann ⊢e) = ⊢closeΓ ⊢e
⊢closeΓ (⊢app ⊢e) = ⊢closeΓ ⊢e
⊢closeΓ (⊢lam₁ ⊢e) with ⊢closeΓ ⊢e
... | clo-S, clo cloA = clo
⊢closeΓ (⊢lam₂ ⊢e up-c ⊢e₁) = ⊢closeΓ ⊢e
⊢closeΓ (⊢sub ⊢e ne gc cloΣ s) = ⊢closeΓ ⊢e
⊢closeΓ (⊢tabs ⊢e) with ⊢closeΓ ⊢e
... | clo-S∙ clo = clo

⊢closeΣ (⊢lit cloΓ) = ⊢c-empty
⊢closeΣ (⊢var cloΓ x∈Γ) = ⊢c-empty
⊢closeΣ (⊢ann ⊢e) = ⊢c-empty
⊢closeΣ (⊢app ⊢e) with ⊢closeΣ ⊢e
... | ⊢c-term cloe clo = clo
⊢closeΣ (⊢lam₁ ⊢e) with ⊢closeΓ ⊢e | ⊢closeΣ ⊢e
... | clo-S, clo1 cloA | ⊢c-τ cloA₁ = ⊢c-τ (⊢c-arr cloA (⊢c-strengthen,0 cloA₁))
⊢closeΣ (⊢lam₂ ⊢e up-c ⊢e₁) with ⊢closeΣ ⊢e₁
... | clo = ⊢c-term (⊢closee ⊢e) (⊢cᶜ-strengthen0 clo up-c)
⊢closeΣ (⊢sub ⊢e ne gc cloΣ s) = cloΣ
⊢closeΣ (⊢tabs ⊢e) = ⊢c-empty

⊢closee (⊢lit cloΓ) = ⊢c-lit
⊢closee (⊢var cloΓ x∈Γ) = ⊢c-var
⊢closee (⊢ann ⊢e) with ⊢closeΣ ⊢e
... | ⊢c-τ cloA = ⊢c-ann cloA (⊢closee ⊢e)
⊢closee (⊢app ⊢e) with ⊢closeΣ ⊢e
... | ⊢c-term cloe clo = ⊢c-app (⊢closee ⊢e) cloe
⊢closee (⊢lam₁ ⊢e) = ⊢c-lam (⊢closee ⊢e)
⊢closee (⊢lam₂ ⊢e up-c ⊢e₁) = ⊢c-lam (⊢closee ⊢e₁)
⊢closee (⊢sub ⊢e ne gc cloΣ s) = ⊢closee ⊢e
⊢closee (⊢tabs ⊢e) = ⊢c-tlam (⊢closee ⊢e)

⊢closeA (⊢lit cloΓ) = ⊢c-int
⊢closeA (⊢var cloΓ x∈Γ) = ∋⦂-closed cloΓ x∈Γ
⊢closeA (⊢ann ⊢e) with ⊢closeΣ ⊢e
... | ⊢c-τ cloA = cloA
⊢closeA (⊢app ⊢e) with ⊢closeA ⊢e
... | ⊢c-arr clo clo₁ = clo₁
⊢closeA (⊢lam₁ ⊢e) with ⊢closeΓ ⊢e | ⊢closeA ⊢e
... | clo-S, cloΓ cloA | clo' = ⊢c-arr cloA (⊢c-strengthen,0 clo')
⊢closeA (⊢lam₂ ⊢e up-c ⊢e₁) = ⊢c-arr (⊢closeA ⊢e) (⊢c-strengthen,0 (⊢closeA ⊢e₁))
⊢closeA (⊢sub ⊢e ne gc cloΣ s) = s-closed s (polar-r cloΣ)
⊢closeA (⊢tabs ⊢e) = ⊢c-∀ (⊢closeA ⊢e)

s-closed s-int pl = ⊢c-int
s-closed (s-empty clo) pl = clo
s-closed s-var (polar-l cloA) = cloA
s-closed s-var (polar-r (⊢c-τ cloA)) = cloA
s-closed (s-ex-l^ x-in inst) (polar-r (⊢c-τ cloA)) = {!!}
s-closed (s-ex-l= x-in s) pl = {!!}
s-closed (s-ex-r^ x-in inst) pl = {!!}
s-closed (s-ex-r= x-in s) pl = {!!}
s-closed (s-arr s s₁) pl = {!!}
s-closed (s-term-c ⊢e s) pl = ⊢c-arr (⊆-closed (⊢closeA ⊢e) (s-⊆ s)) (s-closed s (polar-tm-r pl))
s-closed (s-term-o opnA ⊢e s s₁) pl = {!!}
s-closed (s-∀ s) pl = {!!}
s-closed (s-∀l s upᶜ upᵉ st₁ st₂) pl = {!!}
