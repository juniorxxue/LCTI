{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}
module Implicit.Interm2Algo.WillExport where

open import Implicit.Language.All
open import Implicit.Language.ExtraDefs
open import Implicit.Interm.All

open import Implicit.AuxLemmas
open import Implicit.Interm2Algo.ExtIrrev


irrev-lemma : Γ ⊆ Δ w/t A w/c j
            → Γ ∋^ k
            → [ B / k ] Δ ⟹ Δ'
            → k ε' A by j ↪ j'
            → Γ ⊆ Δ' w/t A w/c j'
irrev-lemma ext inΓ inst newj = {!!}


irrev-lemma0 : Γ ,^ ⊆ Δ ,^ w/t A w/c j
             → #0 ε' A by j ↪ j'
             → Δ ⊢r B
             → Γ ,^ ⊆ Δ ,= B w/t A w/c j'
irrev-lemma0 ext inA regB = irrev-lemma ext Z (⟹^0 {!!} regB {!⊆/c-!}) inA
