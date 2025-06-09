{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}
module Implicit.Interm2Algo.Conv2 where

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


σ-exist : Γ ⊢ ⟨ j , A ⟩ ~s Σ
        → k ε' A by j ↪ 𝕛
        → ∃[ σ ](Γ ⊢ ⟨ 𝕛 , A ⟩ ~s σ)
σ-exist ~Z (ε-var {k = k} isoinf) = ⟨ τ (‶ k) , ~∞ ⟩
σ-exist ~∞ (ε-var {k = k} isoinf) = ⟨ τ (‶ k) , ~∞ ⟩
σ-exist (~I {e = e} ⊢e ~j) (ε-arr-𝕚 x newj) = ⟨ [ e ]↝ σ-exist ~j newj .proj₁ , ~I ⊢e (σ-exist ~j newj .proj₂) ⟩
σ-exist (~C {e = e} ⊢e ~j) (ε-arr-𝕔 x newj) = ⟨ [ e ]↝ σ-exist ~j newj .proj₁ , ~C ⊢e (σ-exist ~j newj .proj₂) ⟩
σ-exist (~T ~j st) (ε-∀-𝕥 newj upj upj₁) = {!σ-exist ~j!}

s-conv : Γ ⊢ A ≤⁺ σ ⊣ Δ ↪ B
       → Γ ⊢ ⟨ j , B ⟩ ~s Σ
       → Γ ⊢ ⟨ 𝕛 , B ⟩ ~s σ
       → k ε' A by j ↪ 𝕛
       → Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
s-conv s newσ new𝕛 = {!!}
