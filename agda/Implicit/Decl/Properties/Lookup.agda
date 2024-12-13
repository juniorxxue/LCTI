module Implicit.Decl.Properties.Lookup where

open import Implicit.Language
open import Implicit.Decl.Base
open import Implicit.Decl.Properties.Subtyping
open import Implicit.Decl.Properties.Weaken

private variable
  Γ Δ : Env n m
  A B : Type m
  k : Fin m

inst-s-l : [ A / k ] Γ ⟹ Δ ↪ B
         → Δ ⊢ ∞ # A ≤ B

inst-s-r : [ A / k ] Γ ⟹ Δ ↪ B
         → Δ ⊢ ∞ # B ≤ A

inst-s-l (⟹^0 up) = s-refl-∞
inst-s-l (⟹^S inst up1 up2) = s-weaken^0 (inst-s-l inst) up1 up2
inst-s-l (⟹∙S inst up1 up2) = s-weaken∙0 (inst-s-l inst) up1 up2
inst-s-l (⟹,S inst) = s-weaken,0 (inst-s-l inst)
inst-s-l (⟹=S inst up1 up2) = s-weaken=0 (inst-s-l inst) up1 (↑ty-st up2)

inst-s-r (⟹^0 up) = s-refl-∞
inst-s-r (⟹^S inst up1 up2) = s-weaken^0 (inst-s-r inst) up2 up1
inst-s-r (⟹∙S inst up1 up2) = s-weaken∙0 (inst-s-r inst) up2 up1
inst-s-r (⟹,S inst) = s-weaken,0 (inst-s-r inst)
inst-s-r (⟹=S inst up1 up2) = s-weaken=0 (inst-s-r inst) (↑ty-st up2) up1
