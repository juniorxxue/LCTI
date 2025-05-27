{-# OPTIONS --allow-unsolved-metas #-}
module Implicit.Interm2Algo.IsoInf where

open import Implicit.Language.All
open import Implicit.Interm2Algo.ExtIrrev


⊆/c-⊆/-iso : Γ ⊆ Δ w/t A w/c j
          → IsoInf j
          → Γ ⊆ Δ w/t A
⊆/c-⊆/-iso (⊆∞ ext isoinf) iso = ext
⊆/c-⊆/-iso (⊆I ext extj) (i∞-i iso) = ext-arr ext (⊆/c-⊆/-iso extj iso)
⊆/c-⊆/-iso (⊆∀-I extj upj) iso = ext-∀ {!⊆/c-⊆/-iso extj ?!}
⊆/c-⊆/-iso (⊆I-X cloA regΓ) iso = ext-var (⊆/x-refl cloA regΓ)


⊆/-⊆/c-iso : Γ ⊆ Δ w/t A
           → IsoInf j
           → Γ ⊆ Δ w/t A w/c j
⊆/-⊆/c-iso ext i∞-z = ⊆∞ ext i∞-z
⊆/-⊆/c-iso ext (i∞-i iso) = ⊆∞ ext (i∞-i iso)
