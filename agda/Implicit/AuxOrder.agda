module Implicit.AuxOrder where

open import Implicit.Language.All

postulate

  need-↑tm' : Need e' p
         → e ↑tm k ⇘ e'
         → Need e p


{-
Γ ⊢

-}
