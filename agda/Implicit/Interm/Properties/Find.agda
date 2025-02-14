module Implicit.Interm.Properties.Find where

open import Implicit.Language.All
open import Implicit.Interm.Base

↑ty-find : find A X j
         → A ↑ty k ⇘ A'
         → X #< k
         → find A' (inject₁ X) j

↑ty-find (f-∞ x) up x<k = f-∞ (↑ty-ε x up x<k)
↑ty-find (f-arr-𝕚-l x) (↑ty-arr up up₁) x<k = f-arr-𝕚-l (↑ty-ε x up x<k)
↑ty-find (f-arr-𝕚-r fd) (↑ty-arr up up₁) x<k = f-arr-𝕚-r (↑ty-find fd up₁ x<k)
↑ty-find (f-arr-𝕔 nin fd) (↑ty-arr up up₁) x<k = f-arr-𝕔 (↑ty-¬ε-prv nin up x<k) (↑ty-find fd up₁ x<k)
↑ty-find (f-∀ fd) (↑ty-∀ up) x<k = f-∀ (↑ty-find fd up (s≤s x<k))

↑ty-find0 : find A #0 j
          → A ↑ty (#S k) ⇘ A'
          → find A' #0 j
↑ty-find0 fd up = ↑ty-find fd up (s≤s z≤n)
