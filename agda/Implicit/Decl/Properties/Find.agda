module Implicit.Decl.Properties.Find where

open import Implicit.Language
open import Implicit.Decl.Base

private variable
  A A' : Type m
  j : Counter
  k k' X : Fin m

↑ty-find : find A X j
         → A ↑ty k ⇘ A'
         → X #< k
         → find A' (inject₁ X) j

↑ty-find (f-∞ x) up neq = f-∞ (↑ty-ε x up neq)
↑ty-find (f-arr-𝕚-l x) (↑ty-arr up up₁) neq = f-arr-𝕚-l (↑ty-ε x up neq)
↑ty-find (f-arr-𝕔 x fd) (↑ty-arr up up₁) neq = f-arr-𝕔 (↑ty-¬ε x up neq) (↑ty-find fd up₁ neq)
↑ty-find (f-∀ fd) (↑ty-∀ up) neq = f-∀ (↑ty-find fd up (s≤s neq))

↑ty-find0 : find A #0 j
          → A ↑ty (#S k) ⇘ A'
          → find A' #0 j
↑ty-find0 fd up = ↑ty-find fd up (s≤s z≤n)
