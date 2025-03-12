module Implicit.NewSoundInterm where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.AlgoCounter.Base
open import Implicit.Interm.Base
-- open import Implicit.Algo.Properties.NewExtension
-- open import Implicit.Algo.Properties.NewPolarity

postulate
  ⊢id0 : Γ ⊢ τ A ⇒ e ⇒ A' ↡ ∞
       → A ≡ A'

sound : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
      → Γ ⊢ j # e ⦂ A

sound-s : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B ↡ j
        → Δ ⊢ j # A ⌞ ≤ ⌝ B

sound-s (s-int cloΓ) = s-int cloΓ
sound-s (s-empty cloΓ clo) = s-refl cloΓ clo
sound-s (s-var-∙ cloΓ x) = s-var-∙ cloΓ x
sound-s (s-var-= cloΓ x) = s-var-= cloΓ x
sound-s (s-ex-l^ x-in cloA inst) = s-var-sub-l (inst-in inst) (s-refl-∞ {!!} {!!})
sound-s (s-ex-l= x-in s) = s-var-typ-l {!!} {!sound-s s!}
sound-s (s-ex-typ-l= x-in s) = {!!}
sound-s (s-ex-r^ x-in cloA inst) = s-var-sub-r (inst-in inst) (s-refl-∞ {!!} {!!})
sound-s (s-ex-r= x-in s) = {!!}
sound-s (s-ex-typ-r= x-in s) = {!!}
sound-s (s-arr s s₁) = s-arr₁ {!sound-s s!} {!!}
sound-s (s-term-c ⊢e s) with ⊢id0 ⊢e
... | refl = s-arr₃ {!!} (sound-s s)
sound-s (s-term-o opnA ⊢e s s₁) = s-arr₂ {!!} {!sound-s s!} (sound-s s₁)
sound-s (s-∀ s) = s-∀ (sound-s s)
sound-s (s-∀l s upᶜ upᵉ st₁ st₂) = s-∀l (sound-s s) {!!} {!!} st₁ st₂
