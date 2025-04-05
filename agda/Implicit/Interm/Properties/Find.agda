module Implicit.Interm.Properties.Find where

open import Implicit.Language.All
open import Implicit.Interm.Base

postulate
  ↑ty-find : find A X j
         → A ↑ty k ⇘ A'
         → j ↑tyʲ k ⇘ j'
         → X #< k
         → find A' (inject₁ X) j'
{-
↑ty-find (f-∞ x) up x<k = f-∞ (↑ty-ε x up x<k)
↑ty-find (f-arr-𝕚-l x) (↑ty-arr up up₁) x<k = f-arr-𝕚-l (↑ty-ε x up x<k)
↑ty-find (f-arr-𝕚-r nin fd) (↑ty-arr up up₁) x<k = f-arr-𝕚-r (↑ty-¬ε-prv nin up x<k) (↑ty-find fd up₁ x<k)
↑ty-find (f-arr-𝕔 nin fd) (↑ty-arr up up₁) x<k = f-arr-𝕔 (↑ty-¬ε-prv nin up x<k) (↑ty-find fd up₁ x<k)
↑ty-find (f-∀ fd) (↑ty-∀ up) x<k = f-∀ (↑ty-find fd up (s≤s x<k))
-}

  ↑ty-find0 : find A #0 j
          → A ↑ty (#S k) ⇘ A'
          → j ↑tyʲ (#S k) ⇘ j'
          → find A' #0 j'
-- ↑ty-find0 fd up = ↑ty-find fd up (s≤s z≤n)

postulate
  ↑ty-find' : find A' (inject₁ X) j'
          → X #< k
          → A ↑ty k ⇘ A'
          → j ↑tyʲ k ⇘ j'
          → find A X j
{-
↑ty-find' (f-∞ x) lt up = f-∞ (↑ty-ε' x lt up)
↑ty-find' (f-arr-𝕚-l x) lt (↑ty-arr up up₁) = f-arr-𝕚-l (↑ty-ε' x lt up)
↑ty-find' (f-arr-𝕚-r ¬inA fd) lt (↑ty-arr up up₁) = f-arr-𝕚-r (¬ε-↑ty'-inv ¬inA up lt) (↑ty-find' fd lt up₁)
↑ty-find' (f-arr-𝕔 ¬inA fd) lt (↑ty-arr up up₁) = f-arr-𝕔 (¬ε-↑ty'-inv ¬inA up lt) (↑ty-find' fd lt up₁)
↑ty-find' (f-∀ fd) lt (↑ty-∀ up) = f-∀ (↑ty-find' fd (s≤s lt) up)
-}

  ↑ty-find0' : find A' #0 j'
             → A ↑ty (#S k) ⇘ A'
             → j ↑tyʲ (#S k) ⇘ j'
             → find A #0 j
-- ↑ty-find0' fd up = ↑ty-find' fd (s≤s z≤n) up
