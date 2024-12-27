module Implicit.Algo.Properties.OpenClose where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Id
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
polar-arr-l (polar-l cloΓ (⊢c-arr cloA cloA₁)) = polar-r cloΓ (⊢c-τ cloA)
polar-arr-l (polar-r cloΓ (⊢c-τ (⊢c-arr cloA cloA₁))) = polar-l cloΓ cloA

polar-arr-r : Polarity Γ (A `→ B) (τ (C `→ D)) ≤
            → Polarity Γ B (τ D) ≤
polar-arr-r (polar-l cloΓ (⊢c-arr cloA cloA₁)) = polar-l cloΓ cloA₁
polar-arr-r (polar-r cloΓ (⊢c-τ (⊢c-arr cloA cloA₁))) = polar-r cloΓ (⊢c-τ cloA₁)

polar-∀ : Polarity Γ (`∀ A) (τ (`∀ B)) ≤
        → Polarity (Γ ,∙) A (τ B) ≤
polar-∀ (polar-l cloΓ (⊢c-∀ cloA)) = polar-l (clo-S∙ cloΓ) cloA
polar-∀ (polar-r cloΓ (⊢c-τ (⊢c-∀ cloA))) = polar-r (clo-S∙ cloΓ) (⊢c-τ cloA)

polar-tm-r : Polarity Γ (A `→ B) ([ e ]↝ Σ) ≤
           → Polarity Γ B Σ ≤
polar-tm-r (polar-l cloΓ (⊢c-arr cloA cloA₁)) = polar-l cloΓ cloA₁
polar-tm-r (polar-r cloΓ (⊢c-term cloe cloA)) = polar-r cloΓ cloA

{-
polar-⊆ : Polarity Γ A Σ ≤
        → Γ ⊆ Γ'
        → Polarity Γ' A Σ ≤
polar-⊆ (polar-l cloΓ cloA) ss = polar-l {!!} (⊆-closed cloA ss)
polar-⊆ (polar-r cloΓ cloA) ss = polar-r {!!} (⊆-closedᶜ cloA ss)
-}

polar-in-l : Polarity Γ (‶ X) Σ ≤
           → Γ ∋ X := A
           → Polarity Γ A Σ ≤
polar-in-l (polar-l cloΓ (⊢c-var-∙ inΓ₁)) inΓ = ⊥-elim (∙∈-=∈-false inΓ₁ inΓ)
polar-in-l (polar-l cloΓ (⊢c-var-= inΓ₁)) inΓ = polar-l cloΓ (∋=-closed cloΓ inΓ)
polar-in-l (polar-r cloΓ cloΣ) inΓ = polar-r cloΓ cloΣ

polar-in-r : Polarity Γ A (τ (‶ X)) ≤
           → Γ ∋ X := B
           → Polarity Γ A (τ B) ≤
polar-in-r (polar-l cloΓ cloA) inΓ = polar-l cloΓ cloA
polar-in-r (polar-r cloΓ (⊢c-τ cloA)) inΓ = polar-r cloΓ (⊢c-τ (∋=-closed cloΓ inΓ))


inst-closedΓ : Closed Γ
             → Γ ⊢c A
             → [ A / X ] Γ ⟹ Δ ↪ B
             → Closed Δ
inst-closedΓ (clo-S^ cloΓ) cloA (⟹^0 up) = clo-S= cloΓ (⊢c-strengthen^0 cloA up)
inst-closedΓ (clo-S^ cloΓ) cloA (⟹^S inst up1 up2) = clo-S^ (inst-closedΓ cloΓ (⊢c-strengthen^0 cloA up1) inst)
inst-closedΓ (clo-S∙ cloΓ) cloA (⟹∙S inst up1 up2) = clo-S∙ (inst-closedΓ cloΓ (⊢c-strengthen∙0 cloA up1) inst)
inst-closedΓ (clo-S, cloΓ cloA₁) cloA (⟹,S inst) =
  clo-S, (inst-closedΓ cloΓ (⊢c-strengthen,0 cloA) inst) (⊆-closed cloA₁ (inst-⊆ inst))
inst-closedΓ (clo-S= cloΓ cloA₁) cloA (⟹=S inst up1 up2) =
  clo-S= (inst-closedΓ cloΓ (⊢c-strengthen=0 cloA up1) inst) (⊆-closed cloA₁ (inst-⊆ inst))

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
-- output env is closed
s-closed-env : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
             → Polarity Γ A Σ ≤
             → Closed Δ
             
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
⊢closeA (⊢sub ⊢e ne gc cloΣ s) = s-closed s (polar-r (⊢closeΓ ⊢e) cloΣ)
⊢closeA (⊢tabs ⊢e) = ⊢c-∀ (⊢closeA ⊢e)

s-closed s-int pl = ⊢c-int
s-closed (s-empty clo) pl = clo
s-closed s-var (polar-l cloΓ cloA) = cloA
s-closed s-var (polar-r cloΓ (⊢c-τ cloA)) = cloA
s-closed (s-ex-l^ x-in inst) (polar-r cloΓ (⊢c-τ cloA)) = ⊆-closed cloA (inst-⊆ inst)
s-closed (s-ex-l= x-in s) pl with ≤id0 s
... | refl = s-closed s (polar-in-l pl x-in)
s-closed (s-ex-r^ x-in inst) pl = ⊢c-var-= (:=to= (inst-in inst))
s-closed (s-ex-r= x-in s) pl = ⊢c-var-= (:=to= (⊆-in:= x-in (s-⊆ s)))
s-closed (s-arr s s₁) (polar-l cloΓ (⊢c-arr cloA cloA₁)) = ⊢c-arr {!!} {!!}
s-closed (s-arr s s₁) (polar-r cloΓ cloΣ) = {!!}
s-closed (s-term-c ⊢e s) pl = ⊢c-arr (⊆-closed (⊢closeA ⊢e) (s-⊆ s)) (s-closed s (polar-tm-r pl))
s-closed (s-term-o opnA ⊢e s s₁) pl = {!!}
s-closed (s-∀ s) pl = ⊢c-∀ (s-closed s (polar-∀ pl))
s-closed (s-∀l s upᶜ upᵉ st₁ st₂) pl = {!!}

s-closed-env s-int (polar-l cloΓ cloA) = cloΓ
s-closed-env s-int (polar-r cloΓ cloΣ) = cloΓ
s-closed-env (s-empty clo) (polar-r cloΓ cloΣ) = cloΓ
s-closed-env s-var (polar-l cloΓ cloA) = cloΓ
s-closed-env s-var (polar-r cloΓ cloΣ) = cloΓ
s-closed-env (s-ex-l^ x-in inst) (polar-r cloΓ (⊢c-τ cloA)) = inst-closedΓ cloΓ cloA inst
s-closed-env (s-ex-l= x-in s) (polar-l cloΓ cloA) = s-closed-env s (polar-in-l (polar-l cloΓ cloA) x-in)
s-closed-env (s-ex-l= x-in s) (polar-r cloΓ cloΣ) = s-closed-env s (polar-r cloΓ cloΣ)
s-closed-env (s-ex-r^ x-in inst) (polar-l cloΓ cloA) = inst-closedΓ cloΓ cloA inst
s-closed-env (s-ex-r= x-in s) (polar-l cloΓ cloA) = s-closed-env s (polar-l cloΓ cloA)
s-closed-env (s-ex-r= x-in s) (polar-r cloΓ cloΣ) = s-closed-env s (polar-in-r (polar-r cloΓ cloΣ) x-in)
s-closed-env (s-arr s s₁) (polar-l cloΓ (⊢c-arr cloA cloA₁)) with s-closed-env s (polar-r cloΓ (⊢c-τ cloA))
... | cloΓ1 = s-closed-env s₁ (polar-l cloΓ1 (⊆-closed cloA₁ (s-⊆ s)))
s-closed-env (s-arr s s₁) (polar-r cloΓ (⊢c-τ (⊢c-arr cloA cloA₁))) with s-closed-env s (polar-l cloΓ cloA)
... | cloΓ1 = s-closed-env s₁ (polar-r cloΓ1 (⊢c-τ (⊆-closed cloA₁ (s-⊆ s))))
s-closed-env (s-term-c ⊢e s) (polar-r cloΓ (⊢c-term cloe cloΣ)) = s-closed-env s (polar-r cloΓ cloΣ)
s-closed-env (s-term-o opnA ⊢e s s₁) (polar-r cloΓ (⊢c-term cloe cloΣ)) with s-closed-env s (polar-l cloΓ (⊢closeA ⊢e))
... | r = s-closed-env s₁ (polar-r r (⊆-closedᶜ cloΣ (s-⊆ s)))
s-closed-env (s-∀ s) pl with s-closed-env s (polar-∀ pl)
... | clo-S∙ r = r
s-closed-env (s-∀l s upᶜ upᵉ st₁ st₂) pl with s-closed-env s {!!}
... | clo-S= r cloA = r


s-closed-l : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
           → Polarity Γ A Σ ≤
           → Δ ⊢c A

s-closed-r : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
           → Polarity Γ A Σ ≤
           → Δ ⊢cᶜ Σ

s-closed-l s-int pr = ⊢c-int
s-closed-l (s-empty clo) pr = clo
s-closed-l s-var (polar-l cloΓ cloA) = cloA
s-closed-l s-var (polar-r cloΓ (⊢c-τ cloA)) = cloA
s-closed-l (s-ex-l^ x-in inst) (polar-r cloΓ cloΣ) = ⊢c-var-= (:=to= (inst-in inst))
s-closed-l (s-ex-l= x-in s) pr = ⊢c-var-= (⊆-in= (:=to= x-in) (s-⊆ s))
s-closed-l s'@(s-ex-r^ x-in inst) (polar-l cloΓ cloA) = ⊆-closed cloA (s-⊆ (s-ex-r^ x-in inst))
s-closed-l (s-ex-r= x-in s) pr = s-closed-l s (polar-in-r pr x-in)
s-closed-l (s-arr s s₁) pr with s-closed-r s (polar-arr-l pr) | s-closed-l s₁ {!!}
... | clo1 | clo2 = ⊢c-arr {!!} {!!}
s-closed-l (s-term-c ⊢e s) pr = {!!}
s-closed-l (s-term-o opnA ⊢e s s₁) pr = {!!}
s-closed-l (s-∀ s) pr = {!!}
s-closed-l (s-∀l s upᶜ upᵉ st₁ st₂) pr = {!!}

s-closed-r s-int pr = {!!}
s-closed-r (s-empty clo) pr = {!!}
s-closed-r s-var pr = {!!}
s-closed-r (s-ex-l^ x-in inst) pr = {!!}
s-closed-r (s-ex-l= x-in s) pr = {!!}
s-closed-r (s-ex-r^ x-in inst) pr = {!!}
s-closed-r (s-ex-r= x-in s) pr = {!!}
s-closed-r (s-arr s s₁) pr = {!!}
s-closed-r (s-term-c ⊢e s) pr = {!!}
s-closed-r (s-term-o opnA ⊢e s s₁) pr = {!!}
s-closed-r (s-∀ s) pr = {!!}
s-closed-r (s-∀l s upᶜ upᵉ st₁ st₂) pr = {!!}

