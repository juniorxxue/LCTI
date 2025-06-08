{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}
module Implicit.Algo2Interm.Find where

open import Implicit.Language.All
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
s-find (s-term-c cloA ap ⊢e s) inΓ inΔ = f-arr-𝕔 (s-find s inΓ inΔ)
-- f-arr-𝕔 (⊢c-^∈-¬ε cloA inΓ) (s-find s inΓ inΔ)
s-find {k = k} (s-term-o {B = B} opnA ⊢e ss s) inΓ inΔ with ε-dec {k = k} {A = B}
... | inj₁ inB = f-arr-𝕚-r (s-find s inΓ (⊆/-^in-=out {!!} inB inΓ))
... | inj₂ ¬inB = f-arr-𝕚-l (^in-=out-ε (ss--⊆/ ss) (⊆/-^in-^out {!!} ¬inB inΓ) inΔ) {!!}
{- with ε-dec {k = k} {A = A}
... | inj₁ inA  = f-arr-𝕚-l inA
... | inj₂ ¬inA = f-arr-𝕚-r ¬inA (s-find s (⊆/-^in-^out (ss--⊆/ ss) ¬inA inΓ) inΔ)
-}
s-find (s-∀l-𝕚 s upᶜ upj upᵉ upC upD) inΓ inΔ = f-∀-𝕚 (s-find s (S^ inΓ) (S= inΔ)) upj
s-find (s-∀l-𝕔 s upᶜ upj upᵉ upC upD) inΓ inΔ = f-∀-𝕔 (s-find s (S^ inΓ) (S= inΔ)) upj
s-find (s-tapp s upᶜ upj) inΓ inΔ = f-𝕥 (s-find s (S= inΓ) (S= inΔ)) upj
s-find (s-svar-term in' s) inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
s-find (s-svar-tapp in' s) inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
s-find (s-∀l-no-𝕚 s upᶜ upj upᵉ upC upD) inΓ inΔ = f-∀-𝕚 (s-find s (S^ inΓ) (S^ inΔ)) upj
s-find (s-∀l-no-𝕔 s upᶜ upj upᵉ upC upD) inΓ inΔ = f-∀-𝕔 (s-find s (S^ inΓ) (S^ inΔ)) upj

s-find0 : Γ ,^ ⊢ A ≤⁺ [ e' ]↝ Σ' ⊣ Δ ,= B ↪ C `→ D ↡ j
              → ↑tyᵉ0 e ⇘ e'
              → ↑tyᶜ0 Σ ⇘ Σ'
              → find A #0 j
s-find0 s up1 up2 = s-find s Z Z


ss-¬ε+ : Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ
        → Γ ∋^ k
        → Δ ∋^ k
        → k ¬ε A

ss-¬ε- : Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ
        → Γ ∋^ k
        → Δ ∋^ k
        → k ¬ε B

ss-¬ε+ (s-int regΓ) inΓ inΔ = ¬ε-int
ss-¬ε+ (s-var-∙ regΓ x) inΓ inΔ = ¬ε-var (∋∙-∋^-≢ x inΓ)
ss-¬ε+ (s-ex-l^ inst) inΓ inΔ = ¬ε-var (∋=-∋^-≢ (inst-∋= inst) inΔ)
ss-¬ε+ (s-ex-l= regΓ x-in) inΓ inΔ = ¬ε-var (∋=-∋^-≢ (∋:=to∋= x-in) inΔ)
ss-¬ε+ (s-arr s s₁) inΓ inΔ = let inΩ = ⊆-∋^-middle inΓ inΔ (ss-⊆ s₁) (ss-⊆ s)
                              in ¬ε-arr (ss-¬ε- s inΩ inΔ) (ss-¬ε+ s₁ inΓ inΩ)
ss-¬ε+ (s-∀ s) inΓ inΔ = ¬ε-∀ (ss-¬ε+ s (S∙ inΓ) (S∙ inΔ))

ss-¬ε- (s-int regΓ) inΓ inΔ = ¬ε-int
ss-¬ε- (s-var-∙ regΓ x) inΓ inΔ = ¬ε-var (∋∙-∋^-≢ x inΓ)
ss-¬ε- (s-ex-r^ inst) inΓ inΔ = ¬ε-var (∋=-∋^-≢ (inst-∋= inst) inΔ)
ss-¬ε- (s-ex-r= regΓ x-in) inΓ inΔ = ¬ε-var (∋=-∋^-≢ (∋:=to∋= x-in) inΔ)
ss-¬ε- (s-arr s s₁) inΓ inΔ = let inΩ = ⊆-∋^-middle inΓ inΔ (ss-⊆ s₁) (ss-⊆ s) in ¬ε-arr (ss-¬ε+ s inΩ inΔ) (ss-¬ε- s₁ inΓ inΩ)
ss-¬ε- (s-∀ s) inΓ inΔ = ¬ε-∀ (ss-¬ε- s (S∙ inΓ) (S∙ inΔ))

s-¬ε : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
       → Γ ∋^ k
       → Δ ∋^ k
       → k ¬ε A
s-¬ε (s-empty regΓ cloA grd) inΓ inΔ = ⊢c-^∈-¬ε cloA inΔ
s-¬ε (s-type ss) inΓ inΔ = ss-¬ε+ ss inΓ inΔ
s-¬ε (s-term-c cloA ap ⊢e s) inΓ inΔ = ¬ε-arr (⊢c-^∈-¬ε cloA inΔ) (s-¬ε s inΓ inΔ)
s-¬ε (s-term-o opnA ⊢e ss s) inΓ inΔ = let inΩ = ⊆-∋^-middle inΓ inΔ (s-⊆ s) (ss-⊆ ss) in ¬ε-arr (ss-¬ε- ss inΩ inΔ) (s-¬ε s inΓ inΩ)
s-¬ε (s-∀l s upᶜ upᵉ upC upD) inΓ inΔ = ¬ε-∀ (s-¬ε s (S^ inΓ) (S= inΔ))
s-¬ε (s-∀l-no s upᶜ upᵉ upC upD) inΓ inΔ = ¬ε-∀ (s-¬ε s (S^ inΓ) (S^ inΔ))
s-¬ε (s-tapp s upᶜ) inΓ inΔ = ¬ε-∀ (s-¬ε s (S= inΓ) (S= inΔ))
s-¬ε (s-svar-term x s) inΓ inΔ = ¬ε-var (∋=-∋^-≢ (∋:=to∋= x) inΓ)
s-¬ε (s-svar-tapp x s) inΓ inΔ = ¬ε-var (∋=-∋^-≢ (∋:=to∋= x) inΓ)
