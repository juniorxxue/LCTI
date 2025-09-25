module Implicit.Interm2Algo.Find where

open import Implicit.Language.All
open import Implicit.Interm2Algo.ExtIrrev


⊆/c-find : Γ ⊆ Δ w/t A w/c j
         → Γ ∋^ k
         → Δ ∋= k
         → find A k j
⊆/c-find (⊆Z regΓ) in1 in2 = ⊥-elim (∋^-∋=-false in1 in2)
⊆/c-find (⊆∞ ext) in1 in2 = f-∞ (^in-=out-ε ext in1 in2)
⊆/c-find {A = A `→ B} {k = k} (⊆I ext ext₁) in1 in2 with ε-dec {k = k} {A}
... | inj₁ p = f-arr-𝕚-l p
... | inj₂ ¬p = f-arr-𝕚-r ¬p (⊆/c-find ext₁ (⊆/-^in-^out ext ¬p in1) in2)
⊆/c-find (⊆C cloA ext) in1 in2 = f-arr-𝕔 (⊢c-^∈-¬ε cloA in1) (⊆/c-find ext in1 in2)
⊆/c-find (⊆∀-I ext ) in1 in2 = f-∀-𝕚 (⊆/c-find ext (S^ in1) (S= in2))
⊆/c-find (⊆∀-I-no ext ) in1 in2 = f-∀-𝕚 (⊆/c-find ext (S^ in1) (S^ in2))
⊆/c-find (⊆∀-C ext ) in1 in2 = f-∀-𝕔 (⊆/c-find ext (S^ in1) (S= in2))
⊆/c-find (⊆∀-C-no ext ) in1 in2 = f-∀-𝕔 (⊆/c-find ext (S^ in1) (S^ in2))
⊆/c-find (⊆I-X regΓ cloA) in1 in2 = ⊥-elim (∋^-∋=-false in1 in2)
⊆/c-find (⊆C-X regΓ cloA) in1 in2 = ⊥-elim (∋^-∋=-false in1 in2)
⊆/c-find (⊆Inf-X extx iso) in1 in2
  with ε-var ← ^in-=out-ε (ext-var extx) in1 in2 = f-iso iso


⊆/c-find0 : Γ ,^ ⊆ Δ ,= B w/t A w/c j
          → find A #0 j
⊆/c-find0 ext = ⊆/c-find ext Z Z


⊆/c-find-∋= : Γ ⊆ Δ w/t A w/c j
              → Γ ∋^ k
              → find A k j
              → Δ ∋= k
⊆/c-find-∋= (⊆∞ ext) inΓ (f-∞ x) = ⊆/-^in-=out ext x inΓ
⊆/c-find-∋= (⊆I ext ext₁) inΓ (f-arr-𝕚-l x) = ⊆-∋= (⊆/-^in-=out ext x inΓ) (⊆/c-⊆ ext₁)
⊆/c-find-∋= (⊆I ext ext₁) inΓ (f-arr-𝕚-r ¬inA fd) = ⊆/c-find-∋= ext₁ (⊆/-^in-^out ext ¬inA inΓ) fd
⊆/c-find-∋= (⊆C cloA ext) inΓ (f-arr-𝕔 ¬inA fd) = ⊆/c-find-∋= ext inΓ fd
⊆/c-find-∋= (⊆∀-I ext ) inΓ (f-∀-𝕚 fd)
  with S= r ← ⊆/c-find-∋= ext (S^ inΓ) fd = r
⊆/c-find-∋= (⊆∀-I-no ext ) inΓ (f-∀-𝕚 fd)
  with S^ r ← ⊆/c-find-∋= ext (S^ inΓ) fd = r
⊆/c-find-∋= (⊆∀-C ext ) inΓ (f-∀-𝕔 fd)
  with S= r ← ⊆/c-find-∋= ext (S^ inΓ) fd = r
⊆/c-find-∋= (⊆∀-C-no ext ) inΓ (f-∀-𝕔 fd)
  with S^ r ← ⊆/c-find-∋= ext (S^ inΓ) fd = r
⊆/c-find-∋= (⊆I-X regΓ cloA) inΓ (f-iso iso) = ⊥-elim (⊢c-^∈-false ε-var inΓ cloA)
⊆/c-find-∋= (⊆Inf-X extx iso₁) inΓ (f-iso iso) = ⊆/x-^in-=out extx inΓ
