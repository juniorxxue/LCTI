module Implicit.Algo.Properties.Polarity where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.Lookup
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.OpenClose

-- the logic seems messed around
-- will rewrite it if needed, perhaps some properties about polarity are needed
-- since we construct polarity in many times

----------------------------------------------------------------------
--+                            Polarity                            +--
----------------------------------------------------------------------

polar-⊆ : Polarity Γ A Σ ≤
        → Γ ⊆ Γ'
        → Polarity Γ' A Σ ≤
polar-⊆ (polar-l cloΓ cloA) ss = polar-l (⊆-closed cloΓ ss) (⊆-cloA cloA ss)
polar-⊆ (polar-r cloΓ cloA) ss = polar-r (⊆-closed cloΓ ss) (⊆-cloAᶜ cloA ss)

inst-closedΓ : Closed Γ
             → Γ ⊢c A
             → [ A / X ] Γ ⟹ Δ ↪ B
             → Closed Δ
inst-closedΓ (clo-S^ cloΓ) cloA (⟹^0 up) = clo-S= cloΓ (⊢c-strengthen^0 cloA up)
inst-closedΓ (clo-S^ cloΓ) cloA (⟹^S inst up1 up2) = clo-S^ (inst-closedΓ cloΓ (⊢c-strengthen^0 cloA up1) inst)
inst-closedΓ (clo-S∙ cloΓ) cloA (⟹∙S inst up1 up2) = clo-S∙ (inst-closedΓ cloΓ (⊢c-strengthen∙0 cloA up1) inst)
inst-closedΓ (clo-S, cloΓ cloA₁) cloA (⟹,S inst) =
  clo-S, (inst-closedΓ cloΓ (⊢c-strengthen,0 cloA) inst) (⊆-cloA cloA₁ (inst-⊆ inst (⊢c-strengthen,0 cloA)))
inst-closedΓ (clo-S= cloΓ cloA₁) cloA (⟹=S inst up1 up2) =
  clo-S= (inst-closedΓ cloΓ (⊢c-strengthen=0 cloA up1) inst) (⊆-cloA cloA₁ (inst-⊆ inst (⊢c-strengthen=0 cloA up1)))

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

s-⊆ : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Γ' ↪ B
    → Polarity Γ A Σ ≤
    → Γ ⊆ Γ'

-- inference result is closed under output env
s-closed : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
         → Polarity Γ A Σ ≤
         → Δ ⊢c B

-- output env is closed
s-closed-env : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
             → Polarity Γ A Σ ≤
             → Closed Δ

s-closed-l : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
           → Polarity Γ A Σ ≤
           → Δ ⊢c A

s-closed-r : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
           → Polarity Γ A Σ ≤
           → Δ ⊢cᶜ Σ

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
... | clo = ⊢c-term (⊢closee ⊢e) (⊢cᶜ-strengthen,0 clo up-c)
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
s-closed (s-ex-l^ x-in inst) (polar-r cloΓ (⊢c-τ cloA)) = ⊆-cloA cloA (inst-⊆ inst cloA)
s-closed (s-ex-l= x-in s) pl with ≤id0 s
... | refl = s-closed s (polar-in-l pl x-in)
s-closed (s-ex-r^ x-in inst) pl = ⊢c-var-= (:=to= (inst-in inst))
s-closed (s-ex-r= x-in s) pl = ⊢c-var-= (:=to= (⊆-in:= x-in (s-⊆ s (polar-in-r pl x-in))))
s-closed (s-arr s s₁) (polar-l cloΓ (⊢c-arr cloA cloA₁)) with polar-r cloΓ (⊢c-τ cloA)
... | pr' with s-closed-r s₁ (polar-l (s-closed-env s pr') (⊆-cloA cloA₁ (s-⊆ s pr')))
... | ⊢c-τ cloA₂ = ⊢c-arr (⊆-cloA (s-closed-l s pr') (s-⊆ s₁ (polar-l (s-closed-env s pr')
                                                                      (⊆-cloA cloA₁ (s-⊆ s pr'))))) cloA₂
s-closed s'@(s-arr s s₁) (polar-r cloΓ (⊢c-τ cloA)) = ⊆-cloA cloA (s-⊆ (s-arr s s₁) (polar-r cloΓ (⊢c-τ cloA)))
s-closed (s-term-c ⊢e s) pl = ⊢c-arr (⊆-cloA (⊢closeA ⊢e) (s-⊆ s (polar-tm-r pl))) (s-closed s (polar-tm-r pl))
s-closed s'@(s-term-o opnA ⊢e s s₁) pr@(polar-r cloΓ (⊢c-term cloe cloΣ)) = let pr' = polar-l cloΓ (⊢closeA ⊢e) in
  ⊢c-arr (⊆-cloA (⊢closeA ⊢e) (s-⊆ s' pr)) (s-closed s₁ (polar-r (s-closed-env s pr') (⊆-cloAᶜ cloΣ (s-⊆ s pr'))))
s-closed (s-∀ s) pl = ⊢c-∀ (s-closed s (polar-∀ pl))
s-closed (s-∀l s upᶜ upᵉ st₁ st₂) (polar-r cloΓ cloΣ) with s-closed-env s (polar-r (clo-S^ cloΓ) (⊢cᶜ-weaken^0 cloΣ (↑tyᶜ-e upᵉ upᶜ)))
... | clo-S= cloΔ cloA = ⊢c-subst0 (s-closed s (polar-r (clo-S^ cloΓ) (⊢cᶜ-weaken^0 cloΣ (↑tyᶜ-e upᵉ upᶜ)))) cloA (st-arr st₁ st₂)


s-closed-env s pr = ⊆-closed (polar-closed pr) (s-⊆ s pr)

----------------------------------------------------------------------
--+                      Output env is closed                      +--
----------------------------------------------------------------------

s-closed-l s-int pr = ⊢c-int
s-closed-l (s-empty clo) pr = clo
s-closed-l s-var (polar-l cloΓ cloA) = cloA
s-closed-l s-var (polar-r cloΓ (⊢c-τ cloA)) = cloA
s-closed-l (s-ex-l^ x-in inst) (polar-r cloΓ cloΣ) = ⊢c-var-= (:=to= (inst-in inst))
s-closed-l (s-ex-l= x-in s) pr = ⊢c-var-= (⊆-in= (:=to= x-in) (s-⊆ s (polar-in-l pr x-in)))
s-closed-l s'@(s-ex-r^ x-in inst) (polar-l cloΓ cloA) = ⊆-cloA cloA (s-⊆ (s-ex-r^ x-in inst) (polar-l cloΓ cloA))
s-closed-l (s-ex-r= x-in s) pr = s-closed-l s (polar-in-r pr x-in)
s-closed-l s'@(s-arr s s₁) (polar-l cloΓ cloA) = ⊆-cloA cloA (s-⊆ s' (polar-l cloΓ cloA))
s-closed-l s'@(s-arr s s₁) (polar-r cloΓ (⊢c-τ (⊢c-arr cloA cloA₁))) with s-closed-r s (polar-l cloΓ cloA)
... | ⊢c-τ cloA₂ = let pr' = polar-r (s-closed-env s (polar-l cloΓ cloA)) (⊢c-τ (⊆-cloA cloA₁ (s-⊆ s (polar-l cloΓ cloA))))
                   in ⊢c-arr (⊆-cloA cloA₂ (s-⊆ s₁ pr'))
                             (s-closed-l s₁ pr')
s-closed-l (s-term-c ⊢e s) (polar-r cloΓ (⊢c-term cloe cloΣ)) with ⊢closeΣ ⊢e
... | ⊢c-τ cloA = ⊢c-arr (⊆-cloA cloA (s-⊆ s (polar-r cloΓ cloΣ))) (s-closed-l s (polar-r cloΓ cloΣ))
s-closed-l (s-term-o opnA ⊢e s s₁) (polar-r cloΓ (⊢c-term cloe cloΣ)) with s-closed-r s (polar-l cloΓ (⊢closeA ⊢e))
... | ⊢c-τ cloA = let pr' = (polar-l cloΓ (⊢closeA ⊢e))
                  in ⊢c-arr (⊆-cloA cloA (s-⊆ s₁ (polar-r (s-closed-env s pr') (⊆-cloAᶜ cloΣ (s-⊆ s pr')))))
                            (s-closed-l s₁ (polar-r (s-closed-env s pr') (⊆-cloAᶜ cloΣ (s-⊆ s pr'))))
s-closed-l (s-∀ s) pr = ⊢c-∀ (s-closed-l s (polar-∀ pr))
s-closed-l (s-∀l s upᶜ upᵉ st₁ st₂) (polar-r cloΓ cloΣ) =
  ⊢c-∀ (⊢c-◆0 (s-closed-l s (polar-r (clo-S^ cloΓ) (⊢cᶜ-weaken^0 cloΣ (↑tyᶜ-e upᵉ upᶜ)))))

s-closed-r s-int pr = ⊢c-τ ⊢c-int
s-closed-r (s-empty clo) pr = ⊢c-empty
s-closed-r s-var (polar-l cloΓ cloA) = ⊢c-τ cloA
s-closed-r s-var (polar-r cloΓ cloΣ) = cloΣ
s-closed-r (s-ex-l^ x-in inst) (polar-r cloΓ (⊢c-τ cloA)) = ⊆-cloAᶜ (⊢c-τ cloA) (inst-⊆ inst cloA)
s-closed-r (s-ex-l= x-in s) pr = s-closed-r s (polar-in-l pr x-in)
s-closed-r (s-ex-r^ x-in inst) (polar-l cloΓ cloA) = ⊢c-τ (⊢c-var-= (:=to= (inst-in inst)))
s-closed-r (s-ex-r= x-in s) pr = ⊢c-τ (⊆-cloA (⊢c-var-= (:=to= x-in)) (s-⊆ s (polar-in-r pr x-in)))
s-closed-r (s-arr s s₁) (polar-l cloΓ (⊢c-arr cloA cloA₁)) with s-closed-r s₁ (polar-l (s-closed-env s (polar-r cloΓ (⊢c-τ cloA))) (⊆-cloA cloA₁ (s-⊆ s (polar-r cloΓ (⊢c-τ cloA)))))
... | ⊢c-τ cloA₂ = ⊢c-τ (⊢c-arr (⊆-cloA (s-closed-l s (polar-r cloΓ (⊢c-τ cloA)))
                                (s-⊆ s₁ (polar-l (s-closed-env s (polar-r cloΓ (⊢c-τ cloA))) (⊆-cloA cloA₁ (s-⊆ s (polar-r cloΓ (⊢c-τ cloA))))))) cloA₂)
s-closed-r s'@(s-arr s s₁) pr'@(polar-r cloΓ (⊢c-τ cloA)) = ⊢c-τ (⊆-cloA cloA (s-⊆ s' pr'))
s-closed-r (s-term-c ⊢e s) (polar-r cloΓ (⊢c-term cloe cloΣ)) = ⊆-cloAᶜ (⊢c-term cloe cloΣ) (s-⊆ s (polar-r cloΓ cloΣ))
s-closed-r s'@(s-term-o opnA ⊢e s s₁) (polar-r cloΓ cloΣ) = ⊆-cloAᶜ cloΣ (s-⊆ s' (polar-r cloΓ cloΣ))
s-closed-r (s-∀ s) pr with s-closed-r s (polar-∀ pr)
... | ⊢c-τ cloA = ⊢c-τ (⊢c-∀ cloA)
s-closed-r s'@(s-∀l s upᶜ upᵉ st₁ st₂) (polar-r cloΓ cloΣ) = ⊆-cloAᶜ cloΣ (s-⊆ s' (polar-r cloΓ cloΣ))

s-⊆ s-int pr = ⊆-refl
s-⊆ (s-empty clo) pr = ⊆-refl
s-⊆ s-var pr = ⊆-refl
s-⊆ (s-ex-l^ x-in inst) (polar-r cloΓ (⊢c-τ cloA)) = inst-⊆ inst cloA
s-⊆ (s-ex-l= x-in s) pr = s-⊆ s (polar-in-l pr x-in)
s-⊆ (s-ex-r^ x-in inst) (polar-l cloΓ cloA) = inst-⊆ inst cloA
s-⊆ (s-ex-r= x-in s) pr = s-⊆ s (polar-in-r pr x-in)
s-⊆ (s-arr s s₁) pr = ⊆-trans (s-⊆ s (polar-arr-l pr)) (s-⊆ s₁ (polar-⊆ (polar-arr-r pr) (s-⊆ s ((polar-arr-l pr)))))
s-⊆ (s-term-c ⊢e s) pr = s-⊆ s (polar-tm-r pr)
s-⊆ (s-term-o opnA ⊢e s s₁) (polar-r cloΓ (⊢c-term cloe cloΣ)) with s-⊆ s (polar-l cloΓ (⊢closeA ⊢e))
... | r = ⊆-trans r (s-⊆ s₁ (polar-r (⊆-closed cloΓ r) (⊆-cloAᶜ cloΣ r)))
s-⊆ (s-∀ s) pr with s-⊆ s (polar-∀ pr)
... | uvar r = r
s-⊆ (s-∀l s upᶜ upᵉ st₁ st₂) (polar-r cloΓ cloΣ) with s-⊆ s (polar-r (clo-S^ cloΓ) (⊢cᶜ-weaken^0 cloΣ (↑tyᶜ-e upᵉ upᶜ)))
... | evar-sol r cloA = r


----------------------------------------------------------------------
--+                           Corollaries                          +--
----------------------------------------------------------------------

⊢close-τ : Γ ⊢ τ A ⇒ e ⇒ B
     → Γ ⊢c A
⊢close-τ ⊢e with ⊢closeΣ ⊢e
... | ⊢c-τ cloA = cloA
