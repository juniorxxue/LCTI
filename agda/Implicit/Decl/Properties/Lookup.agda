module Implicit.Decl.Properties.Lookup where

open import Implicit.Language
open import Implicit.Decl.Base

private variable
  Γ Δ : Env n m
  A B : Type m
  k : Fin m


inst-s-l : [ A / k ] Γ ⟹ Δ ↪ B
         → Δ ⊢ ∞ # A ≤ B

inst-s-r : [ A / k ] Γ ⟹ Δ ↪ B
         → Δ ⊢ ∞ # B ≤ A

inst-s-l (⟹^0 up) = {!!}
inst-s-l (⟹^S inst up1 up2) = {!inst-s-l inst!}
inst-s-l (⟹∙S inst up1 up2) = {!inst-s-l inst!}
inst-s-l (⟹,S inst) = {!inst-s-l inst!}
inst-s-l (⟹=S inst up1 up2) = {!inst-s-l inst!} -- subsitution lemma over decl. subtyping

inst-s-r (⟹^0 up) = {!!}
inst-s-r (⟹^S inst up1 up2) = {!!}
inst-s-r (⟹∙S inst up1 up2) = {!!}
inst-s-r (⟹,S inst) = {!!}
inst-s-r (⟹=S inst up1 up2) = {!!}
