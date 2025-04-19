module Implicit.Language.Find.PProperties where


open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Occur.All
open import Implicit.Language.Find.Base


postulate
  ↑ty-find : find A X j
           → A ↑ty k ⇘ A'
           → j ↑tyʲ k ⇘ j'
           → X #< k
           → find A' (inject₁ X) j'

postulate
  ↑ty-find0 : find A #0 j
            → A ↑ty (#S k) ⇘ A'
            → j ↑tyʲ (#S k) ⇘ j'
            → find A' #0 j'

postulate
  ↑ty-find' : find A' (inject₁ X) j'
            → A ↑ty k ⇘ A'
            → j ↑tyʲ k ⇘ j'
            → X #< k
            → find A X j

postulate
  ↑ty-find0' : find A' #0 j'
              → A ↑ty (#S k) ⇘ A'
              → j ↑tyʲ (#S k) ⇘ j'
              → find A #0 j

