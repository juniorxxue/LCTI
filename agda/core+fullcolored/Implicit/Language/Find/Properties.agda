module Implicit.Language.Find.Properties where


open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Occur.All
open import Implicit.Language.Find.Base

postulate

  ↑ty-find : find2 A X j
         → A ↑ty k ⇘ A'
         → j ↑tyʲ k ⇘ j'
         → X #< k
         → find2 A' (inject₁ X) j'

↑ty-find0 : find2 A #0 j
          → A ↑ty (#S k) ⇘ A'
          → j ↑tyʲ (#S k) ⇘ j'
          → find2 A' #0 j'
↑ty-find0 fd upA upj = ↑ty-find fd upA upj (s≤s z≤n)


postulate
  ↑ty-find' : find2 A' (inject₁ X) j'
          → A ↑ty k ⇘ A'
          → j ↑tyʲ k ⇘ j'
          → X #< k
          → find2 A X j

↑ty-find0' : find2 A' #0 j'
            → A ↑ty (#S k) ⇘ A'
            → j ↑tyʲ (#S k) ⇘ j'
            → find2 A #0 j
↑ty-find0' fd upA upj = ↑ty-find' fd upA upj (s≤s z≤n)
