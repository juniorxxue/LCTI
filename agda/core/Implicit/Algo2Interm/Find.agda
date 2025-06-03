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




data Match : Type m → Type m → Counter m → Set where

  mt-∞ : Match A A ∞
  mt-𝕚 : Match A C j
       → Match A (B `→ C) (𝕚 j)
  mt-𝕔 : Match A C j
       → Match A (B `→ C) (𝕔 j)
  mt-𝕥 : Match A B* j
       → ⟦ C ⟧ B ⇘ B*
       → Match A (`∀ B) (𝕥₍ C ₎ j)


data Truncated (k : Fin m) (A : Type m) (j : Counter m) (C : Type m) (B : Type m) : Set where
  justrun : ∀ {j'}
          → (newj : k ε' A by j ↪ j')
          → (mt : Match C B j')
          → Truncated k A j C B
  in-type : find A k j
          → Truncated k A j C B

truncated : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B ↡ j
          → Γ ∋^ k
          → Δ ∋ k := C
          → k ε' A
          → Truncated k A j C B
truncated (s-empty regΓ cloA x) inΓ inΔ inA = ⊥-elim {!!}
truncated (s-type ss) inΓ inΔ inA = in-type (f-∞ {!!}) -- ok
truncated (s-term-c cloA ap ⊢e s) inΓ inΔ (ε-arr x inA) with truncated s inΓ inΔ inA
... | justrun newj mt = justrun (ε-arr-𝕔 x newj) (mt-𝕔 mt)
... | in-type x₁ = in-type (f-arr-𝕔 x x₁)
truncated (s-term-o opnA ⊢e ss s) inΓ inΔ (ε-arr x inA) with truncated s {!!} inΔ inA
... | justrun newj mt = justrun (ε-arr-𝕚 x newj) (mt-𝕚 mt)
... | in-type x₁ = in-type (f-arr-𝕚-r x x₁)
truncated {C = C} (s-∀l-𝕚 s upᶜ upj upᵉ upC upD) inΓ inΔ (ε-∀ inA)
  with ⟨ C' , upC ⟩ ← ↑ty0-total C
  with truncated s (S^ inΓ) (S= inΔ upC) inA
... | justrun newj mt = justrun (ε-∀-𝕚 newj upj {!!}) {!!} -- 90% ok
... | in-type x = in-type (f-∀-𝕚 x upj)
truncated (s-∀l-𝕔 s upᶜ upj upᵉ upC upD) inΓ inΔ inA = {!!} -- same as above
truncated {C = C} (s-tapp s upᶜ upj) inΓ inΔ (ε-∀ inA)
  with ⟨ C' , upC ⟩ ← ↑ty0-total C
  with truncated s (S= inΓ) (S= inΔ upC) inA
... | justrun newj mt = justrun (ε-∀-𝕥 newj upj {!!}) (mt-𝕥 {!mt!} {!!}) -- same as above
... | in-type x = in-type (f-𝕥 x upj)
truncated (s-svar-term x s) inΓ inΔ ε-var = ⊥-elim {!!}
truncated (s-svar-tapp x s) inΓ inΔ ε-var = ⊥-elim {!!}
truncated (s-evar-infers infs inst) inΓ inΔ ε-var
  with refl ← ∋:=-unique (inst-∋:= inst) inΔ = justrun (ε-var {!!}) mt-∞ -- ok
