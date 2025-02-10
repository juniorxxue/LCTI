module Implicit.Algo.Properties.Extension where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.OpenClose
open import Implicit.Algo.Properties.Polarity

s-⊆/-l : Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Δ ↪ B
           → Closed Γ
           → Γ ⊢cᶜ Σ
           → Γ ⊆ Δ w/t A

s-⊆/-r : Γ ⊢ A ⌞ ≤⁻ ⌝ (τ B) ⊣ Δ ↪ C
           → Closed Γ
           → Γ ⊢c A
           → Γ ⊆ Δ w/t B

s-all-closed : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
             → Closed Γ
             → Γ ⊢c A
             → Γ ⊢cᶜ Σ
             → Γ ≡ Δ
s-all-closed {≤ = ≤⁺} s cloΓ cloA cloΣ with s-⊆/-l s cloΓ cloΣ
... | ext = ⊆/-close-eq cloA ext
s-all-closed {≤ = ≤⁻} {τ A} s cloΓ cloA (⊢c-τ cloA₁) with s-⊆/-r s cloΓ cloA
... | ext = ⊆/-close-eq cloA₁ ext

s-⊆/-l s-int cloΓ cloΣ = ext-int
s-⊆/-l (s-empty clo) cloΓ cloΣ = ⊆/-close clo
s-⊆/-l s-var cloΓ (⊢c-τ cloA) = ⊆/-close cloA
s-⊆/-l (s-ex-l^ x-in inst) cloΓ (⊢c-τ cloA) = ext-var (inst-⊆/x inst cloA)
s-⊆/-l (s-ex-l= x-in s) cloΓ cloΣ with s-all-closed s cloΓ (∋=-closed cloΓ x-in) cloΣ
... | refl = ext-var (⊆/x-= (∋:=to∋= x-in))
s-⊆/-l (s-ex-r= x-in s) cloΓ (⊢c-τ cloA) = s-⊆/-l s cloΓ (⊢c-τ (∋=-closed cloΓ x-in))
s-⊆/-l (s-arr s s₁) cloΓ (⊢c-τ (⊢c-arr cloA cloA₁)) with s-⊆/-r s cloΓ cloA
                        | s-⊆/-l s₁ (s-closed-env s (polar-l cloΓ cloA)) (⊢c-τ (⊆-cloA cloA₁ (s-⊆ s (polar-l cloΓ cloA))))
... | r1 | r2 = ext-arr r1 r2
s-⊆/-l (s-term-c ⊢e s) cloΓ (⊢c-term cloe cloΣ) = ext-arr (⊆/-close (⊢close-τ ⊢e)) (s-⊆/-l s cloΓ cloΣ)
s-⊆/-l (s-term-o opnA ⊢e s s₁) cloΓ (⊢c-term cloe cloΣ) = let cloC = ⊢closeA ⊢e
                                                              ext  = s-⊆ s (polar-l cloΓ cloC)
  in ext-arr (s-⊆/-r s cloΓ cloC) (s-⊆/-l s₁ (s-closed-env s (polar-l cloΓ cloC)) (⊆-cloAᶜ cloΣ ext))
s-⊆/-l (s-∀ s) cloΓ (⊢c-τ (⊢c-∀ cloA)) = ext-∀ (s-⊆/-l s (clo-S∙ cloΓ) (⊢c-τ cloA))
s-⊆/-l (s-∀l s upᶜ upᵉ st₁ st₂) cloΓ cloΣ with s-⊆/-l s (clo-S^ cloΓ) (⊢cᶜ-weaken^0 cloΣ (↑tyᶜ-e upᵉ upᶜ))
... | r = ext-∀ (helper r)
  where helper : Γ ,^ ⊆ Δ ,= B w/t A → Γ ,∙ ⊆ Δ ,∙ w/t A
        helper ext = ⊆/-◆◇-derived ext ◇Z ◆Z

s-⊆/-r s-int cloΓ cloA = ext-int
s-⊆/-r s-var cloΓ cloA = ⊆/-close cloA
s-⊆/-r (s-ex-l= x-in s) cloΓ cloA = s-⊆/-r s cloΓ (∋=-closed cloΓ x-in)
s-⊆/-r (s-ex-r^ x-in inst) cloΓ cloA = ext-var (inst-⊆/x inst cloA)
s-⊆/-r (s-ex-r= x-in s) cloΓ cloA with s-all-closed s cloΓ cloA (⊢c-τ (∋=-closed cloΓ x-in))
... | refl = ext-var (⊆/x-= (∋:=to∋= x-in))
s-⊆/-r (s-arr s s₁) cloΓ (⊢c-arr cloA cloA₁) = ext-arr (s-⊆/-l s cloΓ (⊢c-τ cloA))
  (s-⊆/-r s₁ (s-closed-env s (polar-r cloΓ (⊢c-τ cloA))) (⊆-cloA cloA₁ (s-⊆ s (polar-r cloΓ (⊢c-τ cloA)))))
s-⊆/-r (s-∀ s) cloΓ (⊢c-∀ cloA) = ext-∀ (s-⊆/-r s (clo-S∙ cloΓ) cloA)
