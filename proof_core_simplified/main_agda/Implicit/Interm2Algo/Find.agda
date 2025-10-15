module Implicit.Interm2Algo.Find where

open import Implicit.Language.All
open import Implicit.Interm2Algo.ExtIrrev


⊆/c-find : Γ ⊆ Δ w/t A w/c j
         → Γ ∋^ k
         → Δ ∋= k
         → find A k j
⊆/c-find (⊆Z regΓ) in1 in2 = ⊥-elim (∋^-∋=-false in1 in2)
⊆/c-find (⊆∞ ext) in1 in2 = f-□ (^in-=out-ε ext in1 in2)
⊆/c-find {A = A `→ B} {k = k} (⊆I ext ext₁) in1 in2 with ε-dec {k = k} {A}
... | inj₁ p = f-arr-l p
... | inj₂ ¬p = f-arr-r ¬p (⊆/c-find ext₁ (⊆/-^in-^out ext ¬p in1) in2)
⊆/c-find (⊆C cloA ext) in1 in2 = f-arr-r (⊢c-^∈-¬ε cloA in1) (⊆/c-find ext in1 in2)
⊆/c-find (⊆∀ ext ) in1 in2 = f-∀ (⊆/c-find ext (S^ in1) (S= in2))
⊆/c-find (⊆∀-no ext ) in1 in2 = f-∀ (⊆/c-find ext (S^ in1) (S^ in2))
⊆/c-find (⊆X regΓ cloA) in1 in2 = ⊥-elim (∋^-∋=-false in1 in2)
⊆/c-find (⊆Inf-X extx iso) in1 in2
  with ε-var ← ^in-=out-ε (ext-var extx) in1 in2 = f-iso iso


⊆/c-find0 : Γ ,^ ⊆ Δ ,= B w/t A w/c j
          → find A #0 j
⊆/c-find0 ext = ⊆/c-find ext Z Z


⊆/c-find-∋= : Γ ⊆ Δ w/t A w/c j
              → Γ ∋^ k
              → find A k j
              → Δ ∋= k
⊆/c-find-∋= (⊆∞ ext) inΓ (f-□ x) = ⊆/-^in-=out ext x inΓ
⊆/c-find-∋= (⊆I ext ext₁) inΓ (f-arr-l x) = ⊆-∋= (⊆/-^in-=out ext x inΓ) (⊆/c-⊆ ext₁)
⊆/c-find-∋= (⊆I ext ext₁) inΓ (f-arr-r ¬inA fd) = ⊆/c-find-∋= ext₁ (⊆/-^in-^out ext ¬inA inΓ) fd
⊆/c-find-∋= (⊆C cloA ext) inΓ (f-arr-r ¬inA fd) = ⊆/c-find-∋= ext inΓ fd
⊆/c-find-∋= (⊆∀ ext ) inΓ (f-∀ fd)
  with S= r ← ⊆/c-find-∋= ext (S^ inΓ) fd = r
⊆/c-find-∋= (⊆∀-no ext ) inΓ (f-∀ fd)
  with S^ r ← ⊆/c-find-∋= ext (S^ inΓ) fd = r
⊆/c-find-∋= (⊆X regΓ cloA) inΓ (f-iso iso) = ⊥-elim (⊢c-^∈-false ε-var inΓ cloA)
⊆/c-find-∋= (⊆Inf-X extx iso₁) inΓ (f-iso iso) = ⊆/x-^in-=out extx inΓ
