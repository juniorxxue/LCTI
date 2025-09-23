module Implicit.Language.Find.Properties where


open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Occur.All
open import Implicit.Language.Find.Base

↑ty-find : find A X j
         → A ↑ty k ⇘ A'
         → X #< k
         → find A' (inject₁ X) j
↑ty-find (f-∞ x) upA lt = f-∞ (↑ty-ε x upA lt)
↑ty-find (f-iso x) ↑ty-var lt rewrite punchIn-inject lt = f-iso x
↑ty-find (f-arr-𝕚-l x) (↑ty-arr upA upA₁) lt = f-arr-𝕚-l (↑ty-ε x upA lt)
↑ty-find (f-arr-𝕚-r ¬inA fd) (↑ty-arr upA upA₁) lt = f-arr-𝕚-r (↑ty-¬ε-prv ¬inA upA lt) (↑ty-find fd upA₁ lt)
↑ty-find (f-arr-𝕔 ¬inA fd) (↑ty-arr upA upA₁) lt = f-arr-𝕔 (↑ty-¬ε-prv ¬inA upA lt) (↑ty-find fd upA₁ lt)
↑ty-find (f-∀-𝕚 fd) (↑ty-∀ upA) lt = f-∀-𝕚 (↑ty-find fd upA (s≤s lt))
↑ty-find (f-∀-𝕔 fd) (↑ty-∀ upA) = λ z → f-∀-𝕔 (↑ty-find fd upA (s≤s z))

↑ty-find0 : find A #0 j
          → A ↑ty (#S k) ⇘ A'
          → find A' #0 j
↑ty-find0 fd upA = ↑ty-find fd upA (s≤s z≤n)


↑ty-find' : find A' (inject₁ X) j
          → A ↑ty k ⇘ A'
          → X #< k
          → find A X j
↑ty-find' (f-∞ x) upA lt = f-∞ (↑ty-ε' x lt upA)
↑ty-find' (f-iso x) upA lt rewrite punchIn-inject lt with ↑ty-var-inv-helper upA refl
... | refl = f-iso x
↑ty-find' (f-arr-𝕚-l x) (↑ty-arr upA upA₁) lt = f-arr-𝕚-l (↑ty-ε' x lt upA)
↑ty-find' (f-arr-𝕚-r ¬inA fd) (↑ty-arr upA upA₁) lt = f-arr-𝕚-r (¬ε-↑ty'-inv ¬inA upA lt) (↑ty-find' fd upA₁ lt)
↑ty-find' (f-arr-𝕔 ¬inA fd) (↑ty-arr upA upA₁) lt = f-arr-𝕔 (¬ε-↑ty'-inv ¬inA upA lt) (↑ty-find' fd upA₁ lt)
↑ty-find' (f-∀-𝕚 fd) (↑ty-∀ upA) lt = f-∀-𝕚 (↑ty-find' fd upA (s≤s lt))
↑ty-find' (f-∀-𝕔 fd) (↑ty-∀ upA) lt = f-∀-𝕔 (↑ty-find' fd upA (s≤s lt))

↑ty-find0' : find A' #0 j
            → A ↑ty (#S k) ⇘ A'
            → find A #0 j
↑ty-find0' fd upA = ↑ty-find' fd upA (s≤s z≤n)


find-ε-gen : find A k j
           → k ε A
find-ε-gen (f-∞ x) = x
find-ε-gen (f-iso iso) = ε-var
find-ε-gen (f-arr-𝕚-l x) = ε-arr-l x
find-ε-gen (f-arr-𝕚-r ¬inA fd) = ε-arr-r ¬inA (find-ε-gen fd)
find-ε-gen (f-arr-𝕔 ¬inA fd) = ε-arr-r ¬inA (find-ε-gen fd)
find-ε-gen (f-∀-𝕚 fd) = ε-∀ (find-ε-gen fd)
find-ε-gen (f-∀-𝕔 fd) = ε-∀ (find-ε-gen fd)
