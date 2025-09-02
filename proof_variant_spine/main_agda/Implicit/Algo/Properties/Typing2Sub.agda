module Implicit.Algo.Properties.Typing2Sub where

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
open import Implicit.Algo.Properties.SubIrrelevance
open import Implicit.Algo.Properties.Subsumption

⊢to≤ : Γ ⊢ Σ ⇒ e ⇒ A
     → Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ A

infs-sub' : 𝕣 Γ ⊨ Σ ⟹ A
          → SRegular Γ
          → Γ ⊢ A ≤⁺ Σ ⊣ Γ ↪ A

s-refined-p : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
            → Δ ⊢ B ≤⁺ Σ ⊣ Δ ↪ B

s-refined-p (s-empty cloΓ cloA x) = let regB = (⊢c-≫-⊢r cloΓ cloA x) in s-empty cloΓ (⊢r-⊢c regB ) (⊢r-≫-eq regB)
s-refined-p (s-type ss) = s-type (s-refl (ss-env-out ss) (ss-polarity+-out ss))
s-refined-p (s-term-c cloA ap ⊢e s) with ⊢id0 ⊢e
... | refl = let regA = ⊆-⊢r (⊢c-≫-⊢r (s-env-in s) cloA ap) (s-⊆ s)
             in s-term-c (⊢r-⊢c regA) (⊢r-≫-eq regA) (t-irrev-⊆ ⊢e (s-⊆ s)) (s-refined-p s)
s-refined-p s'@(s-term-o opnA ⊢e ss s) with subsumption0 ⊢e
... | ih = let regA = ⊆-⊢r (ss-polarity- ss) (s-⊆ s')
         in s-term-c (⊢r-⊢c regA) (⊢r-≫-eq regA) (t-irrev-⊆ ih (s-⊆ s')) (s-refined-p s)
-- s-refined-p (s-∀l s upᶜ upᵉ upC upD) = s-strengthen=0 (s-refined-p s) (↑ty-arr upC upD) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
-- s-refined-p (s-∀l-no s upᶜ upᵉ upC upD) = s-strengthen^0 (s-refined-p s) (↑ty-arr upC upD) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
-- s-strengthen=0 (s-refined-p s) (↑ty-arr upC upD) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
s-refined-p (s-tapp s upᶜ) = s-tapp (s-refined-p s) upᶜ
s-refined-p (s-svar-term inΓ s) = s-refined-p s
s-refined-p (s-svar-tapp inΓ s) = s-refined-p s
s-refined-p (s-evar-infers (infs-s ⊢e infs) inst)
  with regA ← (⊆-⊢r (⊢r-𝕣 (t-⊢r ⊢e)) (inst-⊆ inst))
  with ih ← infs-sub' infs (inst-env-in inst)
  = s-term-c (⊢r-⊢c regA) (⊢r-≫-eq regA) (t-irrev-⊆ (subsumption0 ⊢e) (inst-⊆ inst)) (s-irrev-⊆ ih (inst-⊆ inst))
s-refined-p (s-∀l-y pk upB s upᶜ upᵉ upC upD) = s-strengthen=0 (s-refined-p s) (↑ty-arr upC upD) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
s-refined-p (s-∀l-n-y s upᶜ upᵉ upC upD) = s-strengthen=0 (s-refined-p s) (↑ty-arr upC upD) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
s-refined-p (s-∀l-n-n s upᶜ upᵉ upC upD) = s-strengthen^0 (s-refined-p s) (↑ty-arr upC upD) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)


⊢to≤ (⊢lit regΓ) = s-empty (reg-Z regΓ) ⊢c-int grd-int
⊢to≤ (⊢var cloΓ x∈Γ) = let regA = ⊢r-𝕣 (∋⦂-⊢r cloΓ x∈Γ)
                       in s-empty (reg-Z cloΓ) (⊢r-⊢c regA) (⊢r-≫-eq regA)
⊢to≤ (⊢ann ⊢e) with refl ← ⊢id0 ⊢e = let regA = ⊢r-𝕣 (t-⊢r ⊢e)
                                     in s-empty (reg-Z (t-env ⊢e)) (⊢r-⊢c regA) (⊢r-≫-eq regA)
⊢to≤ (⊢app ⊢e) with ⊢to≤ ⊢e
... | s-term-c cloA ap ⊢e₁ r = r
... | s-term-o opnA ⊢e₁ x r = ⊥-elim (⊢r-⊢o-false (⊢r-𝕣 (t-⊢r ⊢e₁)) opnA)
⊢to≤ (⊢lam₁ ⊢e)
  with refl ← ⊢id0 ⊢e
  with reg-S, r regA ← t-env ⊢e
  with regB ← t-⊢r ⊢e = s-type (s-refl (reg-Z r) (⊢r-arr (⊢r-𝕣 regA) (⊢r-𝕣 (⊢r-strengthen,0 regB))))
⊢to≤ (⊢lam₂ ⊢e up-c ⊢e₁) with ⊢to≤ ⊢e₁
... | ih = let regA = ⊢r-𝕣 (t-⊢r ⊢e) in s-term-c (⊢r-⊢c regA) (⊢r-≫-eq regA) (subsumption0 ⊢e) (s-strengthen,0 ih up-c)
⊢to≤ (⊢sub ⊢e ne gc s) = s-refined-p s
⊢to≤ (⊢tabs ⊢e) with t-env ⊢e
... | reg-S∙ r = let regA = ⊢r-𝕣 (t-⊢r ⊢e) in s-empty (reg-Z r) (⊢c-∀ (⊢r-⊢c regA)) (grd-∀ (⊢r-≫-eq regA))
⊢to≤ {e = Λ e} (⊢tabs-τ x) with ⊢id0 x
... | refl = s-type (s-refl (reg-Z (t-env (⊢tabs-τ x))) (⊢r-𝕣 (⊢r-∀ (t-⊢r x))))
⊢to≤ (⊢tapp ⊢e st) with ⊢to≤ ⊢e
... | s-tapp r upᶜ = s-strengthen=0 r st st upᶜ

infs-sub' (infs-z regΓ regA) regΓ' = s-type (s-refl regΓ' (⊢r-𝕣 regA))
infs-sub' (infs-s ⊢e infs) regΓ'
  with regA ← (⊢r-𝕣 (t-⊢r ⊢e))
  = s-term-c (⊢r-⊢c regA) (⊢r-≫-eq regA) (subsumption0 ⊢e) (infs-sub' infs regΓ')
