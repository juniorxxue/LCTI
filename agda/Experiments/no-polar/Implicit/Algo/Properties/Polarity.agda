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

inst-closedΓ : Closed Γ
             → Γ ⊢c A
             → [ A / X ] Γ ⟹ Δ
             → Closed Δ
inst-closedΓ (clo-S^ cloΓ) cloA (⟹^0 up) = clo-S= cloΓ (⊢c-strengthen^0 cloA up)
inst-closedΓ (clo-S^ cloΓ) cloA (⟹^S inst up1) = clo-S^ (inst-closedΓ cloΓ (⊢c-strengthen^0 cloA up1) inst)
inst-closedΓ (clo-S∙ cloΓ) cloA (⟹∙S inst up1) = clo-S∙ (inst-closedΓ cloΓ (⊢c-strengthen∙0 cloA up1) inst)
inst-closedΓ (clo-S, cloΓ cloA₁) cloA (⟹,S inst) =
  clo-S, (inst-closedΓ cloΓ (⊢c-strengthen,0 cloA) inst) (⊆-cloA cloA₁ (inst-⊆ inst (⊢c-strengthen,0 cloA)))
inst-closedΓ (clo-S= cloΓ cloA₁) cloA (⟹=S inst up1) =
  clo-S= (inst-closedΓ cloΓ (⊢c-strengthen=0 cloA up1) inst) (⊆-cloA cloA₁ (inst-⊆ inst (⊢c-strengthen=0 cloA up1)))

----------------------------------------------------------------------
--+                    Typing implies closeness                    +--
----------------------------------------------------------------------


⊢cloΓ : Γ ⊢ Σ ⇒ e ⇒ A
        → Closed Γ

⊢cloΣ : Γ ⊢ Σ ⇒ e ⇒ A
        → Γ ⊢cᶜ Σ

⊢cloe : Γ ⊢ Σ ⇒ e ⇒ A
        → Γ ⊢cᵉ e

⊢cloA : Γ ⊢ Σ ⇒ e ⇒ A
        → Γ ⊢c A


s-clo-in : Γ ⊢ A ≤ Σ ⊣ Δ ↪ B
           → Closed Γ

s-clo-out : Γ ⊢ A ≤ Σ ⊣ Δ ↪ B
          → Closed Δ

s-clo-ret : Γ ⊢ A ≤ Σ ⊣ Δ ↪ B
          → Δ ⊢c B

s-clo-l : Γ ⊢ A ≤ Σ ⊣ Δ ↪ B
           → Δ ⊢c A

s-clo-r : Γ ⊢ A ≤ Σ ⊣ Δ ↪ B
           → Δ ⊢cᶜ Σ

s-clo-r' : Γ ⊢ A ≤ (τ B) ⊣ Δ ↪ C
            → Δ ⊢c B
s-clo-r' s with s-clo-r s
... | ⊢c-τ cloA = cloA

⊢cloΓ (⊢lit cloΓ) = cloΓ
⊢cloΓ (⊢var cloΓ x∈Γ) = cloΓ
⊢cloΓ (⊢ann ⊢e) = ⊢cloΓ ⊢e
⊢cloΓ (⊢app ⊢e) = ⊢cloΓ ⊢e
⊢cloΓ (⊢lam₁ ⊢e) with ⊢cloΓ ⊢e
... | clo-S, clo cloA = clo
⊢cloΓ (⊢lam₂ ⊢e up-c ⊢e₁) = ⊢cloΓ ⊢e
⊢cloΓ (⊢sub ⊢e ne gc s) = ⊢cloΓ ⊢e
⊢cloΓ (⊢tabs ⊢e) with ⊢cloΓ ⊢e
... | clo-S∙ clo = clo

⊢cloΣ (⊢lit cloΓ) = ⊢c-empty
⊢cloΣ (⊢var cloΓ x∈Γ) = ⊢c-empty
⊢cloΣ (⊢ann ⊢e) = ⊢c-empty
⊢cloΣ (⊢app ⊢e) with ⊢cloΣ ⊢e
... | ⊢c-term cloe clo = clo
⊢cloΣ (⊢lam₁ ⊢e) with ⊢cloΓ ⊢e | ⊢cloΣ ⊢e
... | clo-S, clo1 cloA | ⊢c-τ cloA₁ = ⊢c-τ (⊢c-arr cloA (⊢c-strengthen,0 cloA₁))
⊢cloΣ (⊢lam₂ ⊢e up-c ⊢e₁) with ⊢cloΣ ⊢e₁
... | clo = ⊢c-term (⊢cloe ⊢e) (⊢cᶜ-strengthen,0 clo up-c)
⊢cloΣ (⊢sub ⊢e ne gc s) = s-clo-r s
⊢cloΣ (⊢tabs ⊢e) = ⊢c-empty

⊢cloe (⊢lit cloΓ) = ⊢c-lit
⊢cloe (⊢var cloΓ x∈Γ) = ⊢c-var
⊢cloe (⊢ann ⊢e) with ⊢cloΣ ⊢e
... | ⊢c-τ cloA = ⊢c-ann cloA (⊢cloe ⊢e)
⊢cloe (⊢app ⊢e) with ⊢cloΣ ⊢e
... | ⊢c-term cloe clo = ⊢c-app (⊢cloe ⊢e) cloe
⊢cloe (⊢lam₁ ⊢e) = ⊢c-lam (⊢cᵉ-◈0 (⊢cloe ⊢e))
⊢cloe (⊢lam₂ ⊢e up-c ⊢e₁) = ⊢c-lam (⊢cᵉ-◈0 (⊢cloe ⊢e₁))
⊢cloe (⊢sub ⊢e ne gc s) = ⊢cloe ⊢e
⊢cloe (⊢tabs ⊢e) = ⊢c-tlam (⊢cloe ⊢e)

⊢cloA (⊢lit cloΓ) = ⊢c-int
⊢cloA (⊢var cloΓ x∈Γ) = ∋⦂-closed cloΓ x∈Γ
⊢cloA (⊢ann ⊢e) with ⊢cloΣ ⊢e
... | ⊢c-τ cloA = cloA
⊢cloA (⊢app ⊢e) with ⊢cloA ⊢e
... | ⊢c-arr clo clo₁ = clo₁
⊢cloA (⊢lam₁ ⊢e) with ⊢cloΓ ⊢e | ⊢cloA ⊢e
... | clo-S, cloΓ cloA | clo' = ⊢c-arr cloA (⊢c-strengthen,0 clo')
⊢cloA (⊢lam₂ ⊢e up-c ⊢e₁) = ⊢c-arr (⊢cloA ⊢e) (⊢c-strengthen,0 (⊢cloA ⊢e₁))
⊢cloA (⊢sub ⊢e ne gc s) = s-clo-ret s
⊢cloA (⊢tabs ⊢e) = ⊢c-∀ (⊢cloA ⊢e)

s-clo-ret {Σ = □} (s-empty cloΓ clo) = clo
s-clo-ret {Σ = τ A} s with ≤id0 s
... | refl = s-clo-r' s
s-clo-ret {Σ = [ e ]↝ Σ} (s-term-c ⊢e s) = ⊢c-arr (⊆-cloA (⊢cloA ⊢e) (s-⊆ s)) (s-clo-ret s)
s-clo-ret {Σ = [ e ]↝ Σ} s'@(s-term-o opnA ⊢e s s₁) = ⊢c-arr (⊆-cloA (⊢cloA ⊢e) (s-⊆ s')) (s-clo-ret s₁)
s-clo-ret {Σ = [ e ]↝ Σ} (s-∀l s upᶜ upᵉ st₁ st₂) with s-clo-out s
... | clo-S= r cloA = ⊢c-subst0 (s-clo-ret s) cloA (st-arr st₁ st₂)

s-clo-l (s-int cloΓ) = ⊢c-int
s-clo-l (s-empty cloΓ clo) = clo
s-clo-l (s-var-∙ cloΓ x-in) = ⊢c-var-∙ x-in
s-clo-l (s-var-= cloΓ x-in) = ⊢c-var-= x-in
s-clo-l (s-ex-l^ cloA cloΓ x-in inst) = ⊢c-var-= (:=to= (inst-in inst))
s-clo-l (s-ex-l= x-in s) = ⊢c-var-= (:=to= (⊆-in:= x-in (s-⊆ s)))
s-clo-l s'@(s-ex-r^ cloA cloΓ x-in inst) = ⊆-cloA cloA (s-⊆ s')
s-clo-l (s-ex-r= x-in s) = s-clo-l s
s-clo-l s'@(s-arr s s₁) = ⊢c-arr (⊆-cloA (s-clo-r' s) (s-⊆ s₁)) (s-clo-l s₁)
s-clo-l (s-term-c ⊢e s) with ⊢id0 ⊢e
... | refl = ⊢c-arr (⊆-cloA (⊢cloA ⊢e) (s-⊆ s)) (s-clo-l s)
s-clo-l (s-term-o opnA ⊢e s s₁) = ⊢c-arr (⊆-cloA (s-clo-r' s) (s-⊆ s₁)) (s-clo-l s₁)
s-clo-l (s-∀ s) = ⊢c-∀ (s-clo-l s)
s-clo-l (s-∀l s upᶜ upᵉ st₁ st₂) = ⊢c-∀ (⊢c-◆0 (s-clo-l s))

s-clo-r (s-int cloΓ) = ⊢c-τ ⊢c-int
s-clo-r (s-empty cloΓ clo) = ⊢c-empty
s-clo-r (s-var-∙ cloΓ x-in) = ⊢c-τ (⊢c-var-∙ x-in)
s-clo-r (s-var-= cloΓ x-in) = ⊢c-τ (⊢c-var-= x-in)
s-clo-r s'@(s-ex-l^ cloA cloΓ x-in inst) = ⊢c-τ (⊆-cloA cloA (s-⊆ s'))
s-clo-r (s-ex-l= x-in s) = s-clo-r s
s-clo-r (s-ex-r^ cloA cloΓ x-in inst) = ⊢c-τ (⊢c-var-= (:=to= (inst-in inst)))
s-clo-r (s-ex-r= x-in s) = ⊢c-τ (⊢c-var-= (:=to= (⊆-in:= x-in (s-⊆ s))))
s-clo-r (s-arr s s₁) = ⊢c-τ (⊢c-arr (⊆-cloA (s-clo-l s) (s-⊆ s₁)) (s-clo-r' s₁))
s-clo-r (s-term-c ⊢e s) = ⊢c-term (⊆-cloᵉ (⊢cloe ⊢e) (s-⊆ s)) (s-clo-r s)
s-clo-r s'@(s-term-o opnA ⊢e s s₁) = ⊢c-term (⊆-cloᵉ (⊢cloe ⊢e) (s-⊆ s')) (s-clo-r s₁)
s-clo-r (s-∀ s) = ⊢c-τ (⊢c-∀ (s-clo-r' s))
s-clo-r (s-∀l s upᶜ upᵉ st₁ st₂) = ⊢cᶜ-strengthen=0 (s-clo-r s) (↑tyᶜ-e upᵉ upᶜ)


s-clo-in (s-int cloΓ) = cloΓ
s-clo-in (s-empty cloΓ clo) = cloΓ
s-clo-in (s-var-∙ cloΓ x-in) = cloΓ
s-clo-in (s-var-= cloΓ x-in) = cloΓ
s-clo-in (s-ex-l^ cloA cloΓ x-in inst) = cloΓ
s-clo-in (s-ex-l= x-in s) = s-clo-in s
s-clo-in (s-ex-r^ cloA cloΓ x-in inst) = cloΓ
s-clo-in (s-ex-r= x-in s) = s-clo-in s
s-clo-in (s-arr s s₁) = s-clo-in s
s-clo-in (s-term-c ⊢e s) = s-clo-in s
s-clo-in (s-term-o opnA ⊢e s s₁) = s-clo-in s
s-clo-in (s-∀ s) with s-clo-in s
... | clo-S∙ r = r
s-clo-in (s-∀l s upᶜ upᵉ st₁ st₂) with s-clo-in s
... | clo-S^ r = r

s-clo-out s = ⊆-closed (s-clo-in s) (s-⊆ s)
