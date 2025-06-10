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


σ-exist : k ε' A by j ↪ 𝕛
        → Γ ⊢ ⟨ j , B ⟩ ~s Σ
        → ∃[ σ ](Γ ⊢ ⟨ 𝕛 , B ⟩ ~s σ)
σ-exist {B = B} (ε-var isoinf) ~j = ⟨ τ B , ~∞ ⟩
σ-exist (ε-arr-𝕚 x newj) (~I {e = e} ⊢e ~j) = ⟨ [ e ]↝ σ-exist newj ~j .proj₁ , ~I ⊢e (σ-exist newj ~j .proj₂) ⟩
σ-exist (ε-arr-𝕔 x newj) (~C {e = e} ⊢e ~j) = ⟨ [ e ]↝ σ-exist newj ~j .proj₁ , ~C ⊢e (σ-exist newj ~j .proj₂) ⟩
σ-exist (ε-∀-𝕚 newj upj upj₁) ~j = {!!}
σ-exist (ε-∀-𝕔 newj upj upj₁) ~j = {!!}
σ-exist (ε-∀-𝕥 newj upj upj₁) (~T ~j st)
  with ⟨ σ' , newσ ⟩ ← σ-exist newj (~weaken^0 ~j {!!} {!!} upj) = {!!}


ε'-z-false : k ε' A by j ↪ Z
           → ⊥
ε'-z-false (ε-∀-𝕚 newj upj ↑tyʲ-Z) = ε'-z-false newj
ε'-z-false (ε-∀-𝕔 newj upj ↑tyʲ-Z) = ε'-z-false newj


ε'-inv-∞ : k ε' A by j ↪ ∞
         → A ≡ ‶ k
ε'-inv-∞ (ε-var isoinf) = refl
ε'-inv-∞ (ε-∀-𝕚 newj upj ↑tyʲ-∞)
  with refl ← ε'-inv-∞ newj = {!!}
ε'-inv-∞ (ε-∀-𝕔 newj upj upj₁) = {!!}

s-conv : Γ ⊢ A ≤⁺ σ ⊣ Δ ↪ B
       → Γ ⊢ ⟨ j , B ⟩ ~s Σ
       → Γ ⊢ ⟨ 𝕛 , B ⟩ ~s σ
       → k ε' A by j ↪ 𝕛
       → Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
s-conv (s-empty regΓ cloA grd) newΣ ~Z new𝕛 = ⊥-elim (ε'-z-false new𝕛)
s-conv (s-type ss) newΣ ~∞ new𝕛 = {!!}
s-conv (s-term-c cloA ap ⊢e s) (~I ⊢e₂ newΣ) (~I ⊢e₁ newσ) (ε-arr-𝕚 x new𝕛) = {!!}
s-conv (s-term-c cloA ap ⊢e s) newΣ (~C ⊢e₁ newσ) new𝕛 = {!!}
s-conv (s-term-o opnA ⊢e ss s) newΣ newσ new𝕛 = {!!}
s-conv (s-∀l s upᶜ upᵉ upC upD) newΣ newσ new𝕛 = {!!}
s-conv (s-tapp s upᶜ) newΣ newσ new𝕛 = {!!}
s-conv (s-svar-term x s) newΣ newσ new𝕛 = {!!}
s-conv (s-svar-tapp x s) newΣ newσ new𝕛 = {!!}
s-conv (s-evar-infers infs inst) newΣ newσ new𝕛 = {!!}
