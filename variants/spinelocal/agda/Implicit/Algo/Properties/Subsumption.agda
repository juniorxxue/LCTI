module Implicit.Algo.Properties.Subsumption where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.Reflexivity
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Regularity
open import Implicit.Algo.Properties.Polarity
open import Implicit.Algo.Properties.StrengthenTVar
open import Implicit.Algo.Properties.StrengthenSVar
open import Implicit.Algo.Properties.StrengthenEVar
open import Implicit.Algo.Properties.Weaken
open import Implicit.Algo.Properties.Irrelevance

ss-grd+ : SRegular Γ
       → Γ ⊢c A
         → Γ ≫ A ⇘ B
         → Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Γ
ss-grd- : SRegular Γ
       → Γ ⊢c A
         → Γ ≫ A ⇘ B
         → Γ ⊢ B ⌞ ≤⁻ ⌝ A ⊣ Γ

ss-grd+ regΓ cloA grd-int = s-int regΓ
ss-grd+ regΓ cloA (grd-var= x) = s-ex-l= regΓ x
ss-grd+ regΓ cloA (grd-var∙ x) = s-var-∙ regΓ x
ss-grd+ regΓ (⊢c-arr cloA cloA₁) (grd-arr grd grd₁) = s-arr (ss-grd- regΓ cloA grd) (ss-grd+ regΓ cloA₁ grd₁)
ss-grd+ regΓ (⊢c-∀ cloA) (grd-∀ grd) = s-∀ (ss-grd+ (reg-S∙ regΓ) cloA grd)

ss-grd- regΓ cloA grd-int = s-int regΓ
ss-grd- regΓ cloA (grd-var= x) = s-ex-r= regΓ x
ss-grd- regΓ cloA (grd-var∙ x) = s-var-∙ regΓ x
ss-grd- regΓ (⊢c-arr cloA cloA₁) (grd-arr grd grd₁) = s-arr (ss-grd+ regΓ cloA grd) (ss-grd- regΓ cloA₁ grd₁)
ss-grd- regΓ (⊢c-∀ cloA) (grd-∀ grd) = s-∀ (ss-grd- (reg-S∙ regΓ) cloA grd)


private variable
  σ σ' : Context n m

infix 3 _≊_by_
data _≊_by_ : Context n m → Context n m → Type m → Set where
  ≋□ : (Context n m ∋⦂ □) ≊ (τ A) by A
  ≊S : Σ ≊ σ by B
     → [ e ]↝ Σ ≊ [ e ]↝ σ by A `→ B
  ≊⓪ : Σ ≊ σ by B*
     → ⟦ A ⟧ B ⇘ B*
     → A ⓪↝ Σ ≊ A ⓪↝ σ by `∀ B

≊-↑ty : Σ ≊ σ by A
      → ↑tyᶜ0 Σ ⇘ Σ'
      → ↑tyᶜ0 σ ⇘ σ'
      → ↑ty0 A ⇘ A'
      → Σ' ≊ σ' by A'
≊-↑ty ≋□ ↑tyᶜ-□ (↑tyᶜ-τ up-t) upA with refl ← ↑ty-unique up-t upA = ≋□
≊-↑ty (≊S new) (↑tyᶜ-e up-e upΣ) (↑tyᶜ-e up-e₁ upσ) (↑ty-arr upA upA₁)
  with refl ← ↑tyᵉ-unique up-e up-e₁ = ≊S (≊-↑ty new upΣ upσ upA₁)
≊-↑ty (≊⓪ {B* = B*} new x) (↑tyᶜ-⓪ upA₁ upΣ) (↑tyᶜ-⓪ upA₂ upσ) (↑ty-∀ upA)
  with refl ← ↑ty-unique upA₁ upA₂
  with ⟨ B*' , upB* ⟩ ← ↑ty0-total B* = ≊⓪ (≊-↑ty new upΣ upσ upB*) (↑ty-st-comm z≤n x upA upA₁ upB*)

≊-↑tm : Σ ≊ σ by A
      → ↑tmᶜ0 Σ ⇘ Σ'
      → ↑tmᶜ0 σ ⇘ σ'
      → Σ' ≊ σ' by A
≊-↑tm ≋□ ↑tmᶜ-□ ↑tmᶜ-τ = ≋□
≊-↑tm (≊S new) (↑tmᶜ-e up-e upΣ) (↑tmᶜ-e up-e₁ upσ)
  with refl ← ↑tm-unique up-e up-e₁ = ≊S (≊-↑tm new upΣ upσ)
≊-↑tm (≊⓪ new x) (↑tmᶜ-⓪ upΣ) (↑tmᶜ-⓪ upσ) = ≊⓪ (≊-↑tm new upΣ upσ) x

≊-nonempty : NonEmpty Σ
           → Σ ≊ Σ' by A
           → NonEmpty Σ'
≊-nonempty ne-app (≊S new) = ne-app
≊-nonempty ne-tapp (≊⓪ new x) = ne-tapp


~pk~-≊by-false : A ~pk~ Σ w/ k ↪ B
               → Σ ≊ σ by C
               → ⊥
~pk~-≊by-false (pk-term pk) (≊S new) = ~pk~-≊by-false pk new
~pk~-≊by-false {σ = σ} {C = C} (pk-∀l pk upΣ upe upC) new
  with ⟨ σ' , upσ ⟩ ← ↑tyᶜ0-total σ
  with ⟨ C' , upC ⟩ ← ↑ty0-total C
  = ~pk~-≊by-false pk (≊-↑ty new (↑tyᶜ-e upe upΣ) upσ upC)
~pk~-≊by-false (pk-tapp pk upC upΣ) (≊⓪ {σ = σ} {B* = C} new x)
  with ⟨ σ' , upσ ⟩ ← ↑tyᶜ0-total σ
  with ⟨ C' , upC ⟩ ← ↑ty0-total C
  = ~pk~-≊by-false pk (≊-↑ty new upΣ upσ upC)


infs-subsumption : 𝕣 Γ ⊨ Σ ⟹ A
                 → Σ ≊ σ by A
                 → 𝕣 Γ ⊨ σ ⟹ A

s-subsumtion : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
             → Σ ≊ Σ' by B
             → Γ ⊢ A ≤⁺ Σ' ⊣ Δ ↪ B

s-subsumtion (s-empty regΓ cloA grd) ≋□ = s-type (ss-grd+ regΓ cloA grd)
s-subsumtion (s-term-c cloA ap ⊢e s) (≊S new) = s-term-c cloA ap ⊢e (s-subsumtion s new)
s-subsumtion (s-term-o opnA ⊢e ss s) (≊S new) = s-term-o opnA ⊢e ss (s-subsumtion s new)
s-subsumtion (s-tapp s upᶜ) (≊⓪ {σ = σ} new x)
  with ⟨ σ' , upσ ⟩ ←  ↑tyᶜ0-total σ
  with ninC ← ⊢r-¬ε (s-⊢r s) Z
  with ⟨ up , upp ⟩ ← ↑ty-surjective ninC
  with refl ← ↑ty-st-eq upp x = s-tapp (s-subsumtion s (≊-↑ty new upᶜ upσ upp)) upσ
s-subsumtion (s-evar-infers {Δ = Δ} infs inst) (≊S new) = s-evar-infers (infs-subsumption {Γ = Δ} infs (≊S new)) inst
s-subsumtion (s-svar-term inΔ s) (≊S new) = s-svar-term inΔ (s-subsumtion s (≊S new))
s-subsumtion (s-svar-tapp inΔ s) (≊⓪ new x) = s-svar-tapp inΔ (s-subsumtion s (≊⓪ new x))
s-subsumtion {Σ' = σ} (s-∀l-y pk upB s up-c up-e upC upD) new
  with ⟨ σ' , upσ ⟩ ←  ↑tyᶜ0-total σ
  = ⊥-elim (~pk~-≊by-false pk (≊-↑ty new (↑tyᶜ-e up-e up-c) upσ (↑ty-arr upC upD)))
s-subsumtion (s-∀l-n-y s1 up-c up-e upC upD) (≊S {σ = σ} new)
  with ⟨ σ' , upσ ⟩ ←  ↑tyᶜ0-total σ = s-∀l-n-y (s-subsumtion s1 (≊S (≊-↑ty new up-c upσ upD))) upσ up-e upC upD
s-subsumtion (s-∀l-n-n s up-c up-e upC upD) (≊S {σ = σ} new)
  with ⟨ σ' , upσ ⟩ ←  ↑tyᶜ0-total σ = s-∀l-n-n (s-subsumtion s (≊S (≊-↑ty new up-c upσ upD))) upσ up-e upC upD


infs-subsumption {Γ = Γ} (infs-s ⊢e infs) (≊S new) = infs-s ⊢e (infs-subsumption {Γ = Γ} infs new)

subsumption : Γ ⊢ Σ ⇒ e ⇒ A
             → Σ ≊ Σ' by A
             → Γ ⊢ Σ' ⇒ e ⇒ A
subsumption (⊢lit regΓ) ≋□ = ⊢sub (⊢lit regΓ) ne-τ gc-i (s-type (s-int (reg-Z regΓ)))
subsumption (⊢var regΓ x∈Γ) ≋□ = ⊢sub (⊢var regΓ x∈Γ) ne-τ gc-var (s-type (s-refl (reg-Z regΓ) (⊢r-𝕣 (∋⦂-⊢r regΓ x∈Γ))))
subsumption (⊢ann ⊢e) ≋□ with t-⊢rᶜ ⊢e
... | ⊢rᶜ-τ regA = ⊢sub (⊢ann ⊢e) ne-τ gc-ann (s-type (s-refl (reg-Z (t-env ⊢e)) (⊢r-𝕣 regA)))
subsumption (⊢app ⊢e) new = ⊢app (subsumption ⊢e (≊S new))
subsumption (⊢lam₂ ⊢e up-c ⊢e₁) (≊S {σ = σ} new)
  with ⟨ σ' , upσ ⟩ ← ↑tmᶜ0-total σ = ⊢lam₂ ⊢e upσ (subsumption ⊢e₁ (≊-↑tm new up-c upσ))
subsumption (⊢sub ⊢e ne gc s) new = ⊢sub ⊢e (≊-nonempty ne new) gc (s-subsumtion s new)
subsumption (⊢tabs ⊢e) ≋□ = ⊢sub (⊢tabs ⊢e) ne-τ gc-tlam (s-type (s-refl (reg-Z (t-env (⊢tabs ⊢e))) (⊢r-𝕣 (⊢r-∀ (t-⊢r ⊢e)))))
subsumption (⊢tapp ⊢e up) new = ⊢tapp (subsumption ⊢e (≊⓪ new (↑ty-st up))) up
-- ⊢tapp (subsumption ⊢e (≊⓪ new st)) st

subsumption0 : Γ ⊢ □ ⇒ e ⇒ A
             → Γ ⊢ τ A ⇒ e ⇒ A
subsumption0 ⊢e = subsumption ⊢e ≋□
