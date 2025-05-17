module Implicit.Interm.Properties.PStrengthen where

open import Implicit.Language.All
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.PRegularity
open import Implicit.Interm.Properties.PPolarity

postulate
  s-strengthen, : Γ ⊢ j # A ⌞ ≤ ⌝ B
                → Γ ◀ k ,⇘ Γ'
                → Γ' ⊢ j # A ⌞ ≤ ⌝ B

postulate
  t-strengthen, : Γ ⊢ j # e' ⦂ A
                → Γ ◀ k ,⇘ Γ'
                → e ↑tm k ⇘ e'
                → Γ' ⊢ j # e ⦂ A

postulate
  t-strengthen,0 : Γ , T ⊢ j # e' ⦂ A
                 → ↑tm0 e ⇘ e'
                 → Γ ⊢ j # e ⦂ A

postulate
  s-strengthen= : Γ ⊢ j' # A' ⌞ ≤ ⌝ B'
                → Γ ◀ k =⇘ Γ'
                → A ↑ty k ⇘ A'
                → B ↑ty k ⇘ B'
                → j ↑tyʲ k ⇘ j'
                → Γ' ⊢ j # A ⌞ ≤ ⌝ B

postulate
  t-strengthen= : Γ ⊢ j' # e' ⦂ A'
                  → Γ ◀ k =⇘ Γ'
                  → e ↑tyᵉ k ⇘ e'
                  → A ↑ty k ⇘ A'
                  → j ↑tyʲ k ⇘ j'
                  → Γ' ⊢ j # e ⦂ A
