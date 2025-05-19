module Implicit.Interm2Algo.SwapSS where

open import Implicit.Language.All
open import Implicit.Algo.All


swap-ss : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
        → Γ ⊢ B ⌞ ⋆ ≤ ⌝ A ⊣ Δ
swap-ss (s-int regΓ) = s-int regΓ
swap-ss (s-var-∙ regΓ x) = s-var-∙ regΓ x
swap-ss (s-ex-l^ inst) = s-ex-r^ inst
swap-ss (s-ex-r^ inst) = s-ex-l^ inst
swap-ss (s-ex-l= regΓ x-in) = s-ex-r= regΓ x-in
swap-ss (s-ex-r= regΓ x-in) = s-ex-l= regΓ x-in
swap-ss (s-arr ss ss₁) = s-arr (swap-ss ss) (swap-ss ss₁)
swap-ss (s-∀ ss) = s-∀ (swap-ss ss)
