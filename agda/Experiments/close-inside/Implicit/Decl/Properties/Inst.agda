module Implicit.Decl.Properties.Inst where

open import Implicit.Language
open import Implicit.Decl.Base
open import Implicit.Decl.Properties.Subtyping
open import Implicit.Decl.Properties.OpenClose
open import Implicit.Decl.Properties.Weaken

inst-s-l : [ A / k ] Γ ⟹ Δ ↪ B
         → Closed Γ
         → Γ ⊢c A
         → Δ ⊢ ∞ # A ≤ B

inst-s-r : [ A / k ] Γ ⟹ Δ ↪ B
         → Closed Γ
         → Γ ⊢c A
         → Δ ⊢ ∞ # B ≤ A

inst-s-l (⟹^0 up) (clo-S^ cloΓ) cloA = s-refl-∞ (clo-S= cloΓ (⊢c-strengthen^0 cloA up)) (⊢c-weaken=0 (⊢c-strengthen^0 cloA up) up)
inst-s-l (⟹^S inst up1 up2) (clo-S^ cloΓ) cloA = s-weaken^0 (inst-s-l inst cloΓ (⊢c-strengthen^0 cloA up1)) up1 up2
inst-s-l (⟹∙S inst up1 up2) (clo-S∙ cloΓ) cloA = s-weaken∙0 (inst-s-l inst cloΓ (⊢c-strengthen∙0 cloA up1)) up1 up2
inst-s-l (⟹,S inst) (clo-S, cloΓ cloA₁) cloA = s-weaken,0 (inst-s-l inst cloΓ (⊢c-strengthen,0 cloA))
inst-s-l (⟹=S inst up1 up2) (clo-S= cloΓ cloA₁) cloA = s-weaken=0 (inst-s-l inst cloΓ (⊢c-strengthen=0 cloA up1)) up1 up2

inst-s-r (⟹^0 up) (clo-S^ cloΓ) cloA = s-refl-∞ (clo-S= cloΓ (⊢c-strengthen^0 cloA up)) (⊢c-weaken=0 (⊢c-strengthen^0 cloA up) up)
inst-s-r (⟹^S inst up1 up2) (clo-S^ cloΓ) cloA = s-weaken^0 (inst-s-r inst cloΓ (⊢c-strengthen^0 cloA up1)) up2 up1
inst-s-r (⟹∙S inst up1 up2) (clo-S∙ cloΓ) cloA = s-weaken∙0 (inst-s-r inst cloΓ (⊢c-strengthen∙0 cloA up1)) up2 up1
inst-s-r (⟹,S inst) (clo-S, cloΓ cloA₁) cloA = s-weaken,0 (inst-s-r inst cloΓ (⊢c-strengthen,0 cloA))
inst-s-r (⟹=S inst up1 up2) (clo-S= cloΓ cloA₁) cloA = s-weaken=0 (inst-s-r inst cloΓ (⊢c-strengthen=0 cloA up1)) up2 up1
