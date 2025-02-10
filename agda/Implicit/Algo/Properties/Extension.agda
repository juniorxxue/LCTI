module Implicit.Algo.Properties.Extension where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.OpenClose
open import Implicit.Algo.Properties.Polarity

s-extend-l : Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Δ ↪ B
           → Closed Γ
           → Γ ⊢cᶜ Σ
           → Γ ⊆ Δ w/t A

s-extend-r : Γ ⊢ A ⌞ ≤⁻ ⌝ (τ B) ⊣ Δ ↪ C
           → Closed Γ
           → Γ ⊢c A
           → Γ ⊆ Δ w/t B

s-all-closed : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
             → Closed Γ
             → Γ ⊢c A
             → Γ ⊢cᶜ Σ
             → Γ ≡ Δ
s-all-closed {≤ = ≤⁺} s cloΓ cloA cloΣ with s-extend-l s cloΓ cloΣ
... | ext = ext-close-eq cloA ext
s-all-closed {≤ = ≤⁻} {τ A} s cloΓ cloA (⊢c-τ cloA₁) with s-extend-r s cloΓ cloA
... | ext = ext-close-eq cloA₁ ext

s-extend-l s-int cloΓ cloΣ = ext-int
s-extend-l (s-empty clo) cloΓ cloΣ = ext-close clo
s-extend-l s-var cloΓ (⊢c-τ cloA) = ext-close cloA
s-extend-l (s-ex-l^ x-in inst) cloΓ (⊢c-τ cloA) = ext-var (inst-extv inst cloA)
s-extend-l (s-ex-l= x-in s) cloΓ cloΣ with s-all-closed s cloΓ (∋=-closed cloΓ x-in) cloΣ
... | refl = ext-var (extv-= (∋:=to∋= x-in))
s-extend-l (s-ex-r= x-in s) cloΓ (⊢c-τ cloA) = s-extend-l s cloΓ (⊢c-τ (∋=-closed cloΓ x-in))
s-extend-l (s-arr s s₁) cloΓ (⊢c-τ (⊢c-arr cloA cloA₁)) with s-extend-r s cloΓ cloA
                        | s-extend-l s₁ (s-closed-env s (polar-l cloΓ cloA)) (⊢c-τ (⊆-cloA cloA₁ (s-⊆ s (polar-l cloΓ cloA))))
... | r1 | r2 = ext-arr r1 r2
s-extend-l (s-term-c ⊢e s) cloΓ (⊢c-term cloe cloΣ) = ext-arr (ext-close (⊢close-τ ⊢e)) (s-extend-l s cloΓ cloΣ)
s-extend-l (s-term-o opnA ⊢e s s₁) cloΓ (⊢c-term cloe cloΣ) = let cloC = ⊢closeA ⊢e
                                                                  ext = s-⊆ s (polar-l cloΓ cloC)
  in ext-arr (s-extend-r s cloΓ cloC) (s-extend-l s₁ (s-closed-env s (polar-l cloΓ cloC)) (⊆-cloAᶜ cloΣ ext))
s-extend-l (s-∀ s) cloΓ (⊢c-τ (⊢c-∀ cloA)) = ext-∀ (s-extend-l s (clo-S∙ cloΓ) (⊢c-τ cloA))
s-extend-l (s-∀l s upᶜ upᵉ st₁ st₂) cloΓ cloΣ with s-extend-l s (clo-S^ cloΓ) (⊢cᶜ-weaken^0 cloΣ (↑tyᶜ-e upᵉ upᶜ))
... | r = ext-∀ (helper r)
  where helper : Γ ,^ ⊆ Δ ,= B w/t A → Γ ,∙ ⊆ Δ ,∙ w/t A
        helper ext = ext-◆◇-derived ext ◇Z ◆Z

s-extend-r s-int cloΓ cloA = ext-int
s-extend-r s-var cloΓ cloA = ext-close cloA
s-extend-r (s-ex-l= x-in s) cloΓ cloA = s-extend-r s cloΓ (∋=-closed cloΓ x-in)
s-extend-r (s-ex-r^ x-in inst) cloΓ cloA = ext-var (inst-extv inst cloA)
s-extend-r (s-ex-r= x-in s) cloΓ cloA with s-all-closed s cloΓ cloA (⊢c-τ (∋=-closed cloΓ x-in))
... | refl = ext-var (extv-= (∋:=to∋= x-in))
s-extend-r (s-arr s s₁) cloΓ (⊢c-arr cloA cloA₁) = ext-arr (s-extend-l s cloΓ (⊢c-τ cloA))
  (s-extend-r s₁ (s-closed-env s (polar-r cloΓ (⊢c-τ cloA))) (⊆-cloA cloA₁ (s-⊆ s (polar-r cloΓ (⊢c-τ cloA)))))
s-extend-r (s-∀ s) cloΓ (⊢c-∀ cloA) = ext-∀ (s-extend-r s (clo-S∙ cloΓ) cloA)
