module Implicit.Interm.Properties.StrengthenShifted where

open import Implicit.Language.All
open import Implicit.Interm.Base


sregular-strengthen= : SRegular Γ
                     → Γ ◀ k =⇘ Γ'
                     → SRegular Γ'

⊢c-strengthen= : Γ ⊢c A'
               → Γ ◀ k =⇘ Γ'
               → A ↑ty k ⇘ A'
               → Γ' ⊢c A

≫-strengthen= : Γ ≫ A' ⇘ B'
              → Γ ◀ k =⇘ Γ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → Γ' ≫ A ⇘ B



↑ty-var-inv : ∀ {m} {X Y : Fin m} {re k : Fin (1 + m)}
               → ‶ X ↑ty k ⇘ ‶ re
               → re ≡ punchIn k Y
               → X ≡ Y
↑ty-var-inv {X = X} {Y = Y} {k = k} ↑ty-var eq = punchIn-injective k X Y eq

s-strengthen= : Γ ⊢ j # A' ⌞ ≤ ⌝ B'
              → k ¬εᵍ Γ
              → Γ ◀ k =⇘ Γ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → Γ' ⊢ j # A ⌞ ≤ ⌝ B
s-strengthen= (s-refl regΔ cloA grd) ¬inΓ newΓ upA upB = {!!}
s-strengthen= (s-int regΔ) ¬inΓ newΓ upA upB = {!!}
s-strengthen= (s-var-∙ regΔ inΔ) ¬inΓ newΓ upA upB = {!!}
s-strengthen= (s-arr₁ s s₁) ¬inΓ newΓ upA upB = {!!}
s-strengthen= (s-arr₂ s s₁) ¬inΓ newΓ upA upB = {!!}
s-strengthen= (s-arr₃ cloA grd s) ¬inΓ newΓ upA upB = {!!}
s-strengthen= (s-∀ s) ¬inΓ newΓ upA upB = {!!}
s-strengthen= (s-∀l s ic fd upC upD) ¬inΓ newΓ (↑ty-∀ upA) (↑ty-arr upB upB₁)
  = s-∀l (s-strengthen= s (S= ¬inΓ {!!} {!!}) (◀S= newΓ {!!}) {!!} {!!}) ic {!!} {!!} {!!}
s-strengthen= (s-svar-l x inΔ) ¬inΓ newΓ upA upB = {!!}
s-strengthen= (s-svar-r x inΔ) ¬inΓ newΓ upA upB = {!!}


s-strengthen=0 : Γ ,= T ⊢ j # A' ⌞ ≤ ⌝ B'
               → ↑ty0 A ⇘ A'
               → ↑ty0 B ⇘ B'
               → Γ ⊢ j # A  ⌞ ≤ ⌝ B
s-strengthen=0 {T = T} s upA upB
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = s-strengthen= s (Z= upT (↑ty-¬ε upT)) ◀Z upA upB
