module Implicit.Algo2Interm.Find where

open import Implicit.Language.All
open import Implicit.Interm.All
open import Implicit.Algo.All
open import Implicit.Algo2Interm.AlgoCounter.All

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
s-find (s-∀l s upᶜ upᵉ upC upD) inΓ inΔ = f-∀ (s-find s (S^ inΓ) (S= inΔ))

s-find0 : Γ ,^ ⊢ A ≤⁺ [ e' ]↝ Σ' ⊣ Δ ,= B ↪ C `→ D ↡ j
              → ↑tyᵉ0 e ⇘ e'
              → ↑tyᶜ0 Σ ⇘ Σ'
              → find A #0 j
s-find0 s up1 up2 = s-find s Z Z
