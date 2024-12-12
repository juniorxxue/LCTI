module Implicit.Algo where

open import Implicit.Algo.Base public

open import Implicit.Algo.Properties.Extension
  using (⊆-refl; ⊆-trans; ⟹-⊆; s⁺-⊆; s⁻-⊆) public
  
open import Implicit.Algo.Properties.Id
  using (⊢id0; ≤id0) public
  
open import Implicit.Algo.Properties.Environments
  using (inst-s) public

open import Implicit.Algo.Properties.Subst
  using (↑tyᶜ-st) public

open import Implicit.Algo.Properties.OpenClose
  using (⊢c-,) public

-- open import Implicit.Algo.Properties.Find
--  using (find) public
