module Implicit.Interm2Algo.Find where

open import Implicit.Language.All
open import Implicit.Interm2Algo.ExtIrrev


⊆/c-¬find-∋^ : Γ ⊆ Δ w/t A w/c j
              → Γ ∋^ k
              → ¬find A k j
              → Δ ∋^ k
⊆/c-¬find-∋^ (⊆∞ ext) inΓ (f-∞ x) = ⊆/-^in-^out ext x inΓ
⊆/c-¬find-∋^ (⊆I ext ext₁) inΓ (f-arr-𝕚 x ¬fd) = ⊆/-^in-^out ext x (⊆/c-¬find-∋^ ext₁ inΓ ¬fd)
⊆/c-¬find-∋^ (⊆C cloA ext) inΓ (f-arr-𝕔 ¬fd) = ⊆/c-¬find-∋^ ext inΓ ¬fd
⊆/c-¬find-∋^ (⊆∀-I ext upj) inΓ (f-∀-𝕚 ¬fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with S= r ← ⊆/c-¬find-∋^ ext (S^ inΓ) ¬fd = r
⊆/c-¬find-∋^ (⊆∀-I-no ext upj) inΓ (f-∀-𝕚 ¬fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with S^ r ← ⊆/c-¬find-∋^ ext (S^ inΓ) ¬fd = r
⊆/c-¬find-∋^ (⊆∀-C ext upj) inΓ (f-∀-𝕔 ¬fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with S= r ← ⊆/c-¬find-∋^ ext (S^ inΓ) ¬fd = r
⊆/c-¬find-∋^ (⊆∀-C-no ext upj) inΓ (f-∀-𝕔 ¬fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with S^ r ← ⊆/c-¬find-∋^ ext (S^ inΓ) ¬fd = r
⊆/c-¬find-∋^ (⊆∀-T ext upj) inΓ (f-𝕥 ¬fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with S= r ← ⊆/c-¬find-∋^ ext (S= inΓ) ¬fd = r
⊆/c-¬find-∋^ (⊆Z regΓ) inΓ f-z = inΓ
⊆/c-¬find-∋^ (⊆I-X regΓ) inΓ f-var₁ = inΓ
⊆/c-¬find-∋^ (⊆C-X regΓ) inΓ f-var₂ = inΓ
⊆/c-¬find-∋^ (⊆T-X regΓ) inΓ f-var₃ = inΓ

data wf : Type m → Counter m → Set where
  wf-z   : wf A Z
  wf-∞ : wf A ∞
  wf-𝕚 : wf B j
         → wf (A `→ B) (𝕚 j)
  wf-𝕔 : wf B j
         → wf (A `→ B) (𝕔 j)
  wf-𝕚-∀ : wf A (𝕚 j')
       → (upj : ↑tyʲ0 j ⇘ j')
       → wf (`∀ A) (𝕚 j)
  wf-𝕔-∀ : wf A (𝕔 j')
       → (upj : ↑tyʲ0 j ⇘ j')
       → wf (`∀ A) (𝕔 j)
  wf-𝕚-var : wf (‶ X) (𝕚 j)
  wf-𝕔-var : wf (‶ X) (𝕔 j)
  wf-𝕥-var : wf (‶ X) (𝕥₍ B ₎ j)
  wf-𝕥 : wf A j'
       → (upj : ↑tyʲ0 j ⇘ j')
       → wf (`∀ A) (𝕥₍ B ₎ j)

⊆/c-wf : Γ ⊆ Δ w/t A w/c j
       → wf A j
⊆/c-wf (⊆Z regΓ) = wf-z
⊆/c-wf (⊆∞ ext) = wf-∞
⊆/c-wf (⊆I ext ext₁) = wf-𝕚 (⊆/c-wf ext₁)
⊆/c-wf (⊆C cloA ext) = wf-𝕔 (⊆/c-wf ext)
⊆/c-wf (⊆∀-I ext upj) = wf-𝕚-∀ (⊆/c-wf ext) upj
⊆/c-wf (⊆∀-I-no ext upj) = wf-𝕚-∀ (⊆/c-wf ext) upj
⊆/c-wf (⊆∀-C ext upj) = wf-𝕔-∀ (⊆/c-wf ext) upj
⊆/c-wf (⊆∀-C-no ext upj) = wf-𝕔-∀ (⊆/c-wf ext) upj
⊆/c-wf (⊆∀-T ext upj) = wf-𝕥 (⊆/c-wf ext) upj
⊆/c-wf (⊆I-X regΓ) = wf-𝕚-var
⊆/c-wf (⊆C-X regΓ) = wf-𝕔-var
⊆/c-wf (⊆T-X regΓ) = wf-𝕥-var

{-
⊆/c-find-dec : ∀ k
             → wf A j
             → (find A k j) ⊎ (¬find A k j)
⊆/c-find-dec k wf-z = inj₂ f-z
⊆/c-find-dec {A = A} k wf-∞ with ε-dec {k = k} {A = A}
... | inj₁ p = inj₁ (f-∞ p)
... | inj₂ ¬p = inj₂ (f-∞ ¬p)
⊆/c-find-dec {A = A `→ B} k (wf-𝕚 wf₁) with ⊆/c-find-dec k wf₁
... | inj₁ x = inj₁ (f-arr-𝕚-r x)
... | inj₂ y with ε-dec {k = k} {A = A}
... | inj₁ p = inj₁ (f-arr-𝕚-l p y)
... | inj₂ ¬p = inj₂ (f-arr-𝕚 ¬p y)
⊆/c-find-dec k (wf-𝕔 wf₁) with ⊆/c-find-dec k wf₁
... | inj₁ x = inj₁ (f-arr-𝕔 x)
... | inj₂ y = inj₂ (f-arr-𝕔 y)
⊆/c-find-dec k (wf-𝕚-∀ wf₁ upj) with ⊆/c-find-dec (#S k) wf₁
... | inj₁ x = inj₁ (f-∀-𝕚 x upj)
... | inj₂ y = inj₂ (f-∀-𝕚 y upj)
⊆/c-find-dec k (wf-𝕔-∀ wf₁ upj) with ⊆/c-find-dec (#S k) wf₁
... | inj₁ x = inj₁ (f-∀-𝕔 x upj)
... | inj₂ y = inj₂ (f-∀-𝕔 y upj)
⊆/c-find-dec k wf-𝕚-var = inj₂ f-var₁
⊆/c-find-dec k wf-𝕔-var = inj₂ f-var₂
⊆/c-find-dec k wf-𝕥-var = inj₂ f-var₃
⊆/c-find-dec k (wf-𝕥 wf₁ upj) with ⊆/c-find-dec (#S k) wf₁
... | inj₁ x = inj₁ (f-𝕥 x upj)
... | inj₂ y = inj₂ (f-𝕥 y upj)
-}


⊆/c-find : Γ ⊆ Δ w/t A w/c j
         → Γ ∋^ k
         → Δ ∋= k
         → find A k j
⊆/c-find (⊆Z regΓ) in1 in2 = ⊥-elim (∋^-∋=-false in1 in2)
⊆/c-find (⊆∞ ext) in1 in2 = f-∞ (^in-=out-ε ext in1 in2)
⊆/c-find {A = A `→ B} {k = k} (⊆I ext ext₁) in1 in2 with ⊆/c-find-dec k (⊆/c-wf ext₁)
... | inj₁ p = f-arr-𝕚-r p
... | inj₂ ¬p = f-arr-𝕚-l (^in-=out-ε ext (⊆/c-¬find-∋^ ext₁ in1 ¬p) in2) ¬p
⊆/c-find (⊆C cloA ext) in1 in2 = f-arr-𝕔 (⊆/c-find ext in1 in2)
⊆/c-find (⊆∀-I ext upj) in1 in2 = f-∀-𝕚 (⊆/c-find ext (S^ in1) (S= in2)) upj
⊆/c-find (⊆∀-I-no ext upj) in1 in2 = f-∀-𝕚 (⊆/c-find ext (S^ in1) (S^ in2)) upj
⊆/c-find (⊆∀-C ext upj) in1 in2 = f-∀-𝕔 (⊆/c-find ext (S^ in1) (S= in2)) upj
⊆/c-find (⊆∀-C-no ext upj) in1 in2 = f-∀-𝕔 (⊆/c-find ext (S^ in1) (S^ in2)) upj
⊆/c-find (⊆∀-T ext upj) in1 in2 = f-𝕥 (⊆/c-find ext (S= in1) (S= in2)) upj
⊆/c-find (⊆I-X regΓ) in1 in2 = ⊥-elim (∋^-∋=-false in1 in2)
⊆/c-find (⊆C-X regΓ) in1 in2 = ⊥-elim (∋^-∋=-false in1 in2)
⊆/c-find (⊆T-X regΓ) in1 in2 = ⊥-elim (∋^-∋=-false in1 in2)


⊆/c-find0 : Γ ,^ ⊆ Δ ,= B w/t A w/c j
          → find A #0 j
⊆/c-find0 ext = ⊆/c-find ext Z Z


⊆/c-find-∋= : Γ ⊆ Δ w/t A w/c j
              → Γ ∋^ k
              → find A k j
              → Δ ∋= k
⊆/c-find-∋= (⊆∞ ext) inΓ (f-∞ x) = ⊆/-^in-=out ext x inΓ
⊆/c-find-∋= (⊆I ext ext₁) inΓ (f-arr-𝕚-l x ¬fd) = ⊆/-^in-=out ext x (⊆/c-¬find-∋^ ext₁ inΓ ¬fd)
-- ⊆-∋= (⊆/-^in-=out ext x inΓ) (⊆/c-⊆ ext₁)
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
