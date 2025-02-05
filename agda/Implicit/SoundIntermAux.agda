module Implicit.SoundIntermAux where

open import Implicit.Language hiding (_≤_)

ap-∋⦂ : Γ ∋ x ⦂ A
      → Γ ≫ᵍ Γ%
      → Γ% ≫ A ⇘ A%
      → Γ% ∋ x ⦂ A%
ap-∋⦂ Z (ap-S, apΓ x) apA = {!!}
ap-∋⦂ (S, inΓ) (ap-S, apΓ apA₁) apA = S, (ap-∋⦂ inΓ apΓ {!!})
ap-∋⦂ (S∙ inΓ up) (ap-S∙ apΓ) apA = S∙ (ap-∋⦂ inΓ apΓ {!!}) {!!} -- we need a smaller apA so that we could use IH
ap-∋⦂ (S^ inΓ up) (ap-S^ apΓ) apA = S^ (ap-∋⦂ inΓ apΓ {!!}) {!!}
ap-∋⦂ (S= inΓ up) (ap-S= apΓ x) apA = S= (ap-∋⦂ inΓ apΓ {!!}) {!!}

{-
Γ% ,∙ ≫ A' ⇘ A'%
Γ% ≫ A ⇘ A%
↑ty0 A ⇘ A'
--------------
↑ty0 A% ⇘ A'%
-}

{-
a lemma like
Γ% ,∙ ≫ A' ⇘ A'%
↑ty0 A ⇘ A'
-----------------
exists A%, ↑ty0 A% ⇘ A'% and Γ% ≫ A ⇘ A%
-}
