module Implicit.Interm2Algo.Conv where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.Regularity
open import Implicit.Interm.Properties.Polarity
open import Implicit.Interm.Ground
open import Implicit.Interm2Algo.Counter2Context
open import Implicit.Interm2Algo.ExtIrrev
open import Implicit.Interm2Algo.EnvDiff
open import Implicit.Interm2Algo.OpenClose
-- open import Implicit.Interm2Algo.Find
open import Implicit.Interm2Algo.WillExport

variable
  σ σ' : Context n m

data Rebase (Γ : Env n m) (A : Type m) (Δ : Env n m)
            (B : Type m) (𝕛 : Counter m) : Set where

  justrb : ∀ {σ}
         → (newσ : Γ ⊢ ⟨ 𝕛 , B ⟩ ~s σ)
         → (new-s : Γ ⊢ A ≤⁺ σ ⊣ Δ ↪ B)
         → Rebase Γ A Δ B 𝕛

-- a wrong lemma: the forall L rule won't be triggered with transformed counter
-- but what about soundness being proved? seems ok, we state the body can be transformed,
-- such transformation won't affect other forall-L rules.
-- oops, the directional is wrong,
s-conv : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
       → k ε' A by j ↪ 𝕛
       → Γ ⊢ ⟨ j , B ⟩ ~s Σ
       → Rebase Γ A Δ B 𝕛
s-conv (s-empty regΓ cloA grd) (ε-var ()) ~Z
s-conv (s-type ss) (ε-var i∞-z) ~∞ = justrb ~∞ (s-type ss)
s-conv (s-term-c cloA ap ⊢e s) (ε-arr-𝕚 x newj) (~I ⊢e₁ newΣ) with s-conv s newj newΣ
... | justrb newσ new-s = justrb (~I ⊢e₁ newσ) (s-term-c cloA ap ⊢e new-s)
s-conv (s-term-c cloA ap ⊢e s) (ε-arr-𝕔 x newj) (~C ⊢e₁ newΣ) with s-conv s newj newΣ
... | justrb newσ new-s = justrb (~C ⊢e₁ newσ) (s-term-c cloA ap ⊢e₁ new-s)
s-conv (s-term-o opnA ⊢e ss s) (ε-arr-𝕚 x newj) (~I ⊢e₁ newΣ) with s-conv s newj (~irrev newΣ (ss-⊆ ss))
... | justrb newσ new-s = justrb (~I ⊢e (~irrev' newσ (ss-⊆ ss))) (s-term-o opnA ⊢e₁ ss new-s)
s-conv (s-term-o opnA ⊢e ss s) (ε-arr-𝕔 x newj) (~C ⊢e₁ newΣ) with s-conv s newj (~irrev newΣ (ss-⊆ ss))
... | justrb newσ new-s = justrb (~C ⊢e₁ (~irrev' newσ (ss-⊆ ss))) (s-term-o opnA ⊢e ss new-s)
s-conv (s-∀l s upᶜ upᵉ upC upD) (ε-∀-𝕚 newj upj upj₁) ~j@(~I ⊢e newΣ) with s-conv s newj
  (~weaken^0 (~I ⊢e newΣ) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ) (↑tyʲ-𝕚 upj))
... | justrb ~∞ new-s = {!!}
... | justrb (~I ⊢e₁ newσ) new-s = justrb {!!} (s-∀l {!!} {!!} {!!} {!!} {!!})
... | justrb (~C ⊢e₁ newσ) new-s = justrb {!!} (s-∀l {!!} {!!} {!!} {!!} {!!})
s-conv (s-∀l s upᶜ upᵉ upC upD) (ε-∀-𝕔 newj upj upj₁) newΣ = {!!}
s-conv (s-tapp s upᶜ) newj newΣ = {!!}
s-conv (s-svar-term x s) newj newΣ = {!!}
s-conv (s-svar-tapp x s) newj newΣ = {!!}
s-conv (s-evar-infers infs inst) newj newΣ = {!!}
