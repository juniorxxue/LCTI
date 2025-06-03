{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}
module Implicit.Algo2Interm.Find where

open import Implicit.Language.All
open import Implicit.Language.ExtraDefs
open import Implicit.Interm.All
open import Implicit.Algo.All
open import Implicit.Algo2Interm.AlgoCounter.All
open import Implicit.Algo2Interm.Context2Counter

ss-find-l : Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ
              → Γ ∋^ k
              → Δ ∋= k
              → k ε A
ss-find-l s inΓ inΔ = ^in-=out-ε (ss+-⊆/ s) inΓ inΔ

ss-find-r : Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ
              → Γ ∋^ k
              → Δ ∋= k
              → k ε B
ss-find-r s inΓ inΔ = ^in-=out-ε (ss--⊆/ s) inΓ inΔ


s-find : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B ↡ j
       → Γ ∋^ k
       → Δ ∋= k
       → find A k j
s-find (s-empty regΓ cloA x) inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
s-find (s-type ss) inΓ inΔ = f-∞ (ss-find-l ss inΓ inΔ)
s-find (s-term-c cloA ap ⊢e s) inΓ inΔ = f-arr-𝕔 (⊢c-^∈-¬ε cloA inΓ) (s-find s inΓ inΔ)
s-find {k = k} (s-term-o {A = A} opnA ⊢e ss s) inΓ inΔ with ε-dec {k = k} {A = A}
... | inj₁ inA  = f-arr-𝕚-l inA
... | inj₂ ¬inA = f-arr-𝕚-r ¬inA (s-find s (⊆/-^in-^out (ss--⊆/ ss) ¬inA inΓ) inΔ)
s-find (s-∀l-𝕚 s upᶜ upj upᵉ upC upD) inΓ inΔ = f-∀-𝕚 (s-find s (S^ inΓ) (S= inΔ)) upj
s-find (s-∀l-𝕔 s upᶜ upj upᵉ upC upD) inΓ inΔ = f-∀-𝕔 (s-find s (S^ inΓ) (S= inΔ)) upj
s-find (s-tapp s upᶜ upj) inΓ inΔ = f-𝕥 (s-find s (S= inΓ) (S= inΔ)) upj
s-find (s-svar-term in' s) inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
s-find (s-svar-tapp in' s) inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
s-find (s-evar-infers infs inst) inΓ inΔ = {!!} -- wrong


s-find0 : Γ ,^ ⊢ A ≤⁺ [ e' ]↝ Σ' ⊣ Δ ,= B ↪ C `→ D ↡ j
              → ↑tyᵉ0 e ⇘ e'
              → ↑tyᶜ0 Σ ⇘ Σ'
              → find A #0 j
s-find0 s up1 up2 = s-find s Z Z


s-find' : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B ↡ j
       → Γ ∋^ k
       → Δ ∋= k
       → k ¬ε' A
       → find A k j
s-find' (s-empty regΓ cloA x) inΓ inΔ ninA = ⊥-elim (∋^-∋=-false inΓ inΔ)
s-find' (s-type ss) inΓ inΔ ninA = f-∞ (ss-find-l ss inΓ inΔ)
s-find' (s-term-c cloA ap ⊢e s) inΓ inΔ (¬ε'-arr-l x) = f-arr-𝕔 (⊢c-^∈-¬ε cloA inΓ) (⊥-elim {!⊢c-^∈-false!})
s-find' (s-term-c cloA ap ⊢e s) inΓ inΔ (¬ε'-arr-r x ninA) = f-arr-𝕔 (⊢c-^∈-¬ε cloA inΓ) (s-find' s inΓ inΔ ninA)
s-find' (s-term-o opnA ⊢e ss s) inΓ inΔ (¬ε'-arr-l x) = f-arr-𝕚-l x
s-find' (s-term-o opnA ⊢e ss s) inΓ inΔ (¬ε'-arr-r x ninA) = f-arr-𝕚-r x (s-find' s (⊆/-^in-^out (ss--⊆/ ss) x inΓ) inΔ ninA)
s-find' (s-∀l-𝕚 s upᶜ upj upᵉ upC upD) inΓ inΔ (¬ε'-∀ ninA) = f-∀-𝕚 (s-find' s (S^ inΓ) (S= inΔ) ninA) upj
s-find' (s-∀l-𝕔 s upᶜ upj upᵉ upC upD) inΓ inΔ (¬ε'-∀ ninA) = f-∀-𝕔 (s-find' s (S^ inΓ) (S= inΔ) ninA) upj
s-find' (s-tapp s upᶜ upj) inΓ inΔ (¬ε'-∀ ninA) = f-𝕥 (s-find' s (S= inΓ) (S= inΔ) ninA) upj
s-find' (s-svar-term x s) inΓ inΔ ninA = ⊥-elim (∋^-∋=-false inΓ inΔ)
s-find' (s-svar-tapp x s) inΓ inΔ ninA = ⊥-elim (∋^-∋=-false inΓ inΔ)
s-find' (s-evar-infers infs inst) inΓ inΔ (¬ε'-var x) = ⊥-elim (x (inst-affect-one inst inΓ inΔ))
  where postulate inst-affect-one : [ A / X ] Γ ⟹ Δ → Γ ∋^ k → Δ ∋= k → k ≡ X


s-find'0 : Γ ,^ ⊢ A ≤⁺ [ e' ]↝ Σ' ⊣ Δ ,= B ↪ C `→ D ↡ j
              → ↑tyᵉ0 e ⇘ e'
              → ↑tyᶜ0 Σ ⇘ Σ'
              → #0 ¬ε' A
              → find A #0 j
s-find'0 s up1 up2 = s-find' s Z Z
