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
-- open import Implicit.Algo.Properties.Trans
open import Implicit.Algo.Properties.SubIrrelevance

≊-weaken : Σ₁ ≊ Σ₂
         → ↑tmᶜ0 Σ₁ ⇘ Σ₁'
         → ↑tmᶜ0 Σ₂ ⇘ Σ₂'
         → Σ₁' ≊ Σ₂'
≊-weaken ≊Z ↑tmᶜ-□ ↑tmᶜ-τ = ≊Z
≊-weaken (≊S new) (↑tmᶜ-e up-e up1) (↑tmᶜ-e up-e₁ up2) with refl ← ↑tm-unique up-e up-e₁ = ≊S (≊-weaken new up1 up2)
≊-weaken (≊⓪ new) (↑tmᶜ-⓪ up1) (↑tmᶜ-⓪ up2) = ≊⓪ (≊-weaken new up1 up2)

-- aux lemmas
t-inf-open-false : Γ ⊢ □ ⇒ e ⇒ A
                 → Γ ⋈ ⊢o A
                 → ⊥
t-inf-open-false ⊢e opnA = ⊢r-⊢o-false (⊢r-𝕣 (t-⊢r ⊢e)) opnA

⊢to≤ : Γ ⊢ Σ ⇒ e ⇒ A
     → Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ A

subsumption :  Γ ⊢ Σ ⇒ e ⇒ A
             → Σ ≊ Σ'
             → Γ ⋈ ⊢ A ≤⁺ Σ' ⊣ Γ ⋈ ↪ A'
             → Γ ⊢ Σ' ⇒ e ⇒ A'

infs-sub' : 𝕣 Γ ⊨ Σ ⟹ A
          → SRegular Γ
          → Γ ⊢ A ≤⁺ Σ ⊣ Γ ↪ A

subsumption0 : Γ ⊢ □ ⇒ e ⇒ A
             → Γ ⊢ τ A ⇒ e ⇒ A
subsumption0 ⊢e = subsumption ⊢e ≊Z (s-type (s-refl (reg-Z (t-env ⊢e)) (⊢r-weaken⋈0 (t-⊢r ⊢e))))


s-refined-p : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
            → Δ ⊢ B ≤⁺ Σ ⊣ Δ ↪ B
s-refined-p (s-empty cloΓ cloA x) = let regB = (⊢c-≫-⊢r cloΓ cloA x) in s-empty cloΓ (⊢r-⊢c regB ) (⊢r-≫-eq regB)
s-refined-p (s-type ss) = s-type (s-refl (ss-env-out ss) (ss-polarity+-out ss))
s-refined-p (s-term-c ap ⊢e s) with ⊢id0 ⊢e
... | refl = let regA = ⊆-⊢r (⊢c-≫-⊢r (s-env-in s) ? ap) (s-⊆ s)
             in s-term-c (⊢r-≫-eq regA) (t-irrev-⊆ ⊢e (s-⊆ s)) (s-refined-p s)
s-refined-p s'@(s-term-o ⊢e ss s) with subsumption0 ⊢e
... | ih = let regA = ⊆-⊢r (ss-polarity- ss) (s-⊆ s')
         in s-term-c (⊢r-≫-eq regA) (t-irrev-⊆ ih (s-⊆ s')) (s-refined-p s)
s-refined-p (s-∀l s upᶜ upᵉ upC upD) = s-strengthen=0 (s-refined-p s) (↑ty-arr upC upD) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
s-refined-p (s-∀l-no s upᶜ upᵉ upC upD) = s-strengthen^0 (s-refined-p s) (↑ty-arr upC upD) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
-- s-strengthen=0 (s-refined-p s) (↑ty-arr upC upD) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
s-refined-p (s-tapp s upᶜ) = s-tapp (s-refined-p s) upᶜ
s-refined-p (s-svar-term inΓ s) = s-refined-p s
s-refined-p (s-svar-tapp inΓ s) = s-refined-p s
s-refined-p (s-evar-infers (infs-s ⊢e infs) inst)
  with regA ← (⊆-⊢r (⊢r-𝕣 (t-⊢r ⊢e)) (inst-⊆ inst))
  with ih ← infs-sub' infs (inst-env-in inst)
  = s-term-c (⊢r-≫-eq regA) (t-irrev-⊆ (subsumption0 ⊢e) (inst-⊆ inst)) (s-irrev-⊆ ih (inst-⊆ inst))

infs-sub' (infs-z regΓ regA) regΓ' = s-type (s-refl regΓ' (⊢r-𝕣 regA))
infs-sub' (infs-s ⊢e infs) regΓ'
  with regA ← (⊢r-𝕣 (t-⊢r ⊢e))
  = s-term-c (⊢r-≫-eq regA) (subsumption0 ⊢e) (infs-sub' infs regΓ')



⊢to≤ (⊢lit regΓ) = s-empty (reg-Z regΓ) ⊢c-int grd-int
⊢to≤ (⊢var cloΓ x∈Γ) = let regA = ⊢r-𝕣 (∋⦂-⊢r cloΓ x∈Γ)
                       in s-empty (reg-Z cloΓ) (⊢r-⊢c regA) (⊢r-≫-eq regA)
⊢to≤ (⊢ann ⊢e) with refl ← ⊢id0 ⊢e = let regA = ⊢r-𝕣 (t-⊢r ⊢e)
                                     in s-empty (reg-Z (t-env ⊢e)) (⊢r-⊢c regA) (⊢r-≫-eq regA)
⊢to≤ (⊢app ⊢e) with ⊢to≤ ⊢e
... | s-term-c ap ⊢e₁ r = r
... | s-term-o ⊢e₁ x r = ?
⊢to≤ (⊢lam₁ ⊢e)
  with refl ← ⊢id0 ⊢e
  with reg-S, r regA ← t-env ⊢e
  with regB ← t-⊢r ⊢e = s-type (s-refl (reg-Z r) (⊢r-arr (⊢r-𝕣 regA) (⊢r-𝕣 (⊢r-strengthen,0 regB))))
⊢to≤ (⊢lam₂ ⊢e up-c ⊢e₁) with ⊢to≤ ⊢e₁
... | ih = let regA = ⊢r-𝕣 (t-⊢r ⊢e) in s-term-c (⊢r-≫-eq regA) (subsumption0 ⊢e) (s-strengthen,0 ih up-c)
⊢to≤ (⊢sub ⊢e ne gc s) = s-refined-p s
⊢to≤ (⊢tabs ⊢e) with t-env ⊢e
... | reg-S∙ r = let regA = ⊢r-𝕣 (t-⊢r ⊢e) in s-empty (reg-Z r) (⊢c-∀ (⊢r-⊢c regA)) (grd-∀ (⊢r-≫-eq regA))
⊢to≤ (⊢tapp ⊢e st) with ⊢to≤ ⊢e
... | s-tapp r upᶜ = let upA = (st-↑ty (⊢r-¬ε (s-⊢r r) Z) st)
                     in s-strengthen=0 r upA upA upᶜ

subsumption {Σ' = τ A} (⊢lit regΓ) ≊Z s = ⊢sub (⊢lit regΓ) ne-τ gc-i s
subsumption {Σ' = τ A} (⊢var cloΓ x∈Γ) ≊Z s = ⊢sub (⊢var cloΓ x∈Γ) ne-τ gc-var s
subsumption {Σ' = τ A} (⊢ann ⊢e) ≊Z s = ⊢sub (⊢ann ⊢e) ne-τ gc-ann s
subsumption {Σ' = τ A} (⊢app ⊢e) ≊Z s with ⊢to≤ ⊢e
... | s-term-c ap ⊢e₁ s₁ = ⊢app (subsumption ⊢e (≊S ≊Z) (s-term-c cloA ap ⊢e₁ s))
... | s-term-o ⊢e₁ x s₁ = ⊥-elim (t-inf-open-false ⊢e₁ opnA)
subsumption {Σ' = τ A} (⊢tabs ⊢e) ≊Z s = ⊢sub (⊢tabs ⊢e) ne-τ gc-tlam s
subsumption {Σ' = τ A} {A' = A′} (⊢tapp ⊢e st) ≊Z s
  with ⟨ A' , upA ⟩ ← ↑ty0-total A
  with refl ← s-id0 s
  with s-tapp (s-empty regΓ'@(reg-S= regΓ regA) cloA grd) ↑tyᶜ-□ ← ⊢to≤ ⊢e =
    let upA₁ = (st-↑ty (⊢r-¬ε (⊢c-≫-⊢r regΓ' cloA grd) Z) st)
    in ⊢tapp (subsumption ⊢e (≊⓪ ≊Z) (s-tapp (s-weaken=0 s upA₁ (↑tyᶜ-τ upA) upA regA) (↑tyᶜ-τ upA))) (↑ty-st upA)

subsumption {Σ' = [ e ]↝ Σ'} (⊢app ⊢e) (≊S newΣ) s with ⊢to≤ ⊢e
... | s-term-c cloA ap ⊢e₁ r = ⊢app (subsumption ⊢e (≊S (≊S newΣ)) (s-term-c cloA ap ⊢e₁ s))
... | s-term-o opnA ⊢e₁ x r = ⊥-elim (t-inf-open-false ⊢e₁ opnA)
subsumption {Σ' = [ e ]↝ Σ'} (⊢lam₂ ⊢e up-c ⊢e₁) (≊S newΣ) (s-term-c cloA ap ⊢e₂ s)
  with relf ← ⊢id0 ⊢e₂
  with reg-S, regΓ regA ← t-env ⊢e₁
  with refl ← ⊢r-≫-eq' (⊢r-𝕣 regA) ap
  with ⟨ nΣ' , upΣ ⟩ ← ↑tmᶜ0-total Σ' = ⊢lam₂ ⊢e upΣ (subsumption ⊢e₁ (≊-weaken newΣ up-c upΣ) (s-weaken,0 s upΣ regA))
subsumption {Σ' = [ e ]↝ Σ'} (⊢lam₂ ⊢e up-c ⊢e₁) (≊S newΣ) (s-term-o opnA ⊢e₂ x s) = ⊥-elim (t-inf-open-false ⊢e opnA)
subsumption {Σ' = [ e ]↝ Σ'} (⊢sub ⊢e ne gc s₁) (≊S newΣ) s = ?
-- ⊢sub ⊢e ne-app gc (s-trans s₁ s (≊S newΣ))
subsumption {Σ' = [ e ]↝ Σ'} {A' = A′} (⊢tapp ⊢e st) (≊S newΣ) s
  with s-tapp s' (↑tyᶜ-e up-e upᶜ) ← ⊢to≤ ⊢e
  with ⟨ Σ″ , upΣ' ⟩ ← ↑tyᶜ0-total Σ'
  with ⟨ A″ , upA′ ⟩ ← ↑ty0-total A′
  with reg-S= regΓ regA ← s-env-in s'
  = let upA' = (st-↑ty (⊢r-¬ε (s-⊢r s') Z) st)
    in ⊢tapp (subsumption ⊢e (≊⓪ (≊S newΣ)) (s-tapp (s-weaken=0 s upA' (↑tyᶜ-e up-e upΣ') upA′ regA) (↑tyᶜ-e up-e upΣ'))) (↑ty-st upA′)

subsumption {Σ' = A ⓪↝ Σ'} (⊢app ⊢e) (≊⓪ newΣ) s with ⊢to≤ ⊢e
... | s-term-c cloA ap ⊢e₁ r = ⊢app (subsumption ⊢e (≊S (≊⓪ newΣ)) (s-term-c cloA ap ⊢e₁ s))
... | s-term-o opnA ⊢e₁ ss r = ⊥-elim (t-inf-open-false ⊢e₁ opnA)
subsumption {Σ' = A ⓪↝ Σ'} (⊢sub ⊢e ne gc s₁) newΣ s = ⊢sub ⊢e ne-tapp gc ?
-- (s-trans s₁ s newΣ)
subsumption {Σ' = A ⓪↝ Σ'} {A' = A′} (⊢tapp ⊢e st) (≊⓪ newΣ) s
  with s-tapp s' (↑tyᶜ-⓪ up-e upᶜ) ← ⊢to≤ ⊢e
  with ⟨ Σ″ , upΣ' ⟩ ← ↑tyᶜ0-total Σ'
  with ⟨ A″ , upA′ ⟩ ← ↑ty0-total A′
  with reg-S= regΓ regA ← s-env-in s'
  = let upA' = (st-↑ty (⊢r-¬ε (s-⊢r s') Z) st)
    in ⊢tapp (subsumption ⊢e (≊⓪ (≊⓪ newΣ)) (s-tapp (s-weaken=0 s upA' (↑tyᶜ-⓪ up-e upΣ') upA′ regA) (↑tyᶜ-⓪ up-e upΣ'))) (↑ty-st upA′)
