module Implicit.Interm2Algo.Find where

open import Implicit.Language.All
open import Implicit.Interm2Algo.ExtIrrev
{-
⊆-∋^-⊢c-∋= : Γ ⊆ Δ
           → Γ ∋^ k
           → k ε B
           → Δ ⊢c B
           → Δ ∋= k
⊆-∋^-⊢c-∋= ext inΓ inB cloB with s-⊆-exsol ext inΓ
... | is-ex inΓ₁ = ⊥-elim (⊢c-^∈-false inB inΓ₁ cloB)
... | is-sol inΓ₁ = inΓ₁


⊆/c-^in-^out : Γ ⊆ Δ w/t A w/c j
             → k ¬ε A
             → Γ ∋^ k
             → Δ ∋^ k
⊆/c-^in-^out (⊆Z regΓ cloA) ninA inΓ = inΓ
⊆/c-^in-^out (⊆∞ ext) ninA inΓ = ⊆/-^in-^out ext ninA inΓ
⊆/c-^in-^out (⊆I ext ext₁) (¬ε-arr ninA ninA₁) inΓ = ⊆/c-^in-^out (⊆∞ ext) ninA (⊆/c-^in-^out ext₁ ninA₁ inΓ)
⊆/c-^in-^out (⊆C cloA ext) (¬ε-arr ninA ninA₁) inΓ = ⊆/c-^in-^out ext ninA₁ inΓ
⊆/c-^in-^out (⊆∀-I ext upj) (¬ε-∀ ninA) inΓ with ⊆/c-^in-^out ext ninA (S^ inΓ)
... | S= r = r
⊆/c-^in-^out (⊆∀-I-no ext upj) (¬ε-∀ ninA) inΓ with ⊆/c-^in-^out ext ninA (S^ inΓ)
... | S^ r = r
⊆/c-^in-^out (⊆∀-C ext upj) (¬ε-∀ ninA) inΓ with ⊆/c-^in-^out ext ninA (S^ inΓ)
... | S= r = r
⊆/c-^in-^out (⊆∀-C-no ext upj) (¬ε-∀ ninA) inΓ with ⊆/c-^in-^out ext ninA (S^ inΓ)
... | S^ r = r
⊆/c-^in-^out (⊆∀-T ext upj) (¬ε-∀ ninA) inΓ with ⊆/c-^in-^out ext ninA (S= inΓ)
... | S= r = r
⊆/c-^in-^out (⊆I-X regΓ cloX) ninA inΓ = inΓ
⊆/c-^in-^out (⊆C-X regΓ cloX) ninA inΓ = inΓ
⊆/c-^in-^out (⊆T-X regΓ cloX) ninA inΓ = inΓ


⊆/c-find : Γ ⊆ Δ w/t A w/c j
         → Γ ∋^ k
         → Δ ∋= k
         → find A k j
⊆/c-find (⊆Z regΓ cloA) in1 in2 = ⊥-elim (∋^-∋=-false in1 in2)
⊆/c-find (⊆∞ ext) in1 in2 = f-∞ (^in-=out-ε ext in1 in2)
⊆/c-find {A = A `→ B} {k = k} (⊆I ext ext₁) in1 in2 with ε-dec {k = k} {A = B}
... | inj₁ x = f-arr-𝕚-r (⊆/c-find ext₁ in1 (⊆-∋^-⊢c-∋= (⊆/c-⊆ ext₁) in1 x (⊆/c-⊢c ext₁)))
... | inj₂ y = f-arr-𝕚-l (^in-=out-ε ext (⊆/c-^in-^out ext₁ y in1) in2) y
⊆/c-find (⊆C cloA ext) in1 in2 = f-arr-𝕔 (⊆/c-find ext in1 in2)
⊆/c-find (⊆∀-I ext upj) in1 in2 = f-∀-𝕚 (⊆/c-find ext (S^ in1) (S= in2)) upj
⊆/c-find (⊆∀-I-no ext upj) in1 in2 = f-∀-𝕚 (⊆/c-find ext (S^ in1) (S^ in2)) upj
⊆/c-find (⊆∀-C ext upj) in1 in2 = f-∀-𝕔 (⊆/c-find ext (S^ in1) (S= in2)) upj
⊆/c-find (⊆∀-C-no ext upj) in1 in2 = f-∀-𝕔 (⊆/c-find ext (S^ in1) (S^ in2)) upj
⊆/c-find (⊆∀-T ext upj) in1 in2 = f-𝕥 (⊆/c-find ext (S= in1) (S= in2)) upj
⊆/c-find (⊆I-X regΓ cloX) in1 in2 = ⊥-elim (∋^-∋=-false in1 in2)
⊆/c-find (⊆C-X regΓ cloX) in1 in2 = ⊥-elim (∋^-∋=-false in1 in2)
⊆/c-find (⊆T-X regΓ cloX) in1 in2 = ⊥-elim (∋^-∋=-false in1 in2)


⊆/c-find0 : Γ ,^ ⊆ Δ ,= B w/t A w/c j
          → find A #0 j
⊆/c-find0 ext = ⊆/c-find ext Z Z


⊆/c-find-∋= : Γ ⊆ Δ w/t A w/c j
              → Γ ∋^ k
              → find A k j
              → Δ ∋= k
⊆/c-find-∋= (⊆∞ ext) inΓ (f-∞ x) = ⊆/-^in-=out ext x inΓ
⊆/c-find-∋= (⊆I ext ext₁) inΓ (f-arr-𝕚-l x ¬inB) = ⊆/-^in-=out ext x (⊆/c-^in-^out ext₁ ¬inB inΓ)
⊆/c-find-∋= (⊆I ext ext₁) inΓ (f-arr-𝕚-r fd) = ⊆-∋= (⊆/c-find-∋= ext₁ inΓ fd) (⊆/-⊆ ext)
⊆/c-find-∋= (⊆C cloA ext) inΓ (f-arr-𝕔 fd) = ⊆/c-find-∋= ext inΓ fd
⊆/c-find-∋= (⊆∀-I ext upj) inΓ (f-∀-𝕚 fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with S= r ← ⊆/c-find-∋= ext (S^ inΓ) fd = r
⊆/c-find-∋= (⊆∀-I-no ext upj) inΓ (f-∀-𝕚 fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with S^ r ← ⊆/c-find-∋= ext (S^ inΓ) fd = r
⊆/c-find-∋= (⊆∀-C ext upj) inΓ (f-∀-𝕔 fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with S= r ← ⊆/c-find-∋= ext (S^ inΓ) fd = r
⊆/c-find-∋= (⊆∀-C-no ext upj) inΓ (f-∀-𝕔 fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with S^ r ← ⊆/c-find-∋= ext (S^ inΓ) fd = r
⊆/c-find-∋= (⊆∀-T ext upj) inΓ (f-𝕥 fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with S= r ← ⊆/c-find-∋= ext (S= inΓ) fd = r
-}
