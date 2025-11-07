module Implicit.Language.Find.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Occur.All
open import Implicit.Language.Find.Base

↑ty-find : find A X j
         → A ↑ty k ⇘ A'
         → X #< k
         → find A' (inject₁ X) j
↑ty-find (f-□ inA) upA lt = f-□ (↑ty-ε inA upA lt)
↑ty-find (f-iso iso) ↑ty-var lt rewrite punchIn-inject lt = f-iso iso
↑ty-find (f-arr-l inA) (↑ty-arr upA upA₁) lt = f-arr-l (↑ty-ε inA upA lt)
↑ty-find (f-arr-r ¬inA fd) (↑ty-arr upA upA₁) lt = f-arr-r (↑ty-¬ε-prv ¬inA upA lt) (↑ty-find fd upA₁ lt)
↑ty-find (f-∀ fd) (↑ty-∀ upA) lt = f-∀ (↑ty-find fd upA (s≤s lt))

↑ty-find0 : find A #0 j
          → A ↑ty (#S k) ⇘ A'
          → find A' #0 j
↑ty-find0 fd upA = ↑ty-find fd upA (s≤s z≤n)


↑ty-find' : find A' (inject₁ X) j
          → A ↑ty k ⇘ A'
          → X #< k
          → find A X j
↑ty-find' (f-□ inA) upA lt = f-□ (↑ty-ε' inA lt upA)
↑ty-find' (f-iso iso) upA lt rewrite punchIn-inject lt with ↑ty-var-inv-helper upA refl
... | refl = f-iso iso
↑ty-find' (f-arr-l inA) (↑ty-arr upA upA₁) lt = f-arr-l (↑ty-ε' inA lt upA)
↑ty-find' (f-arr-r ¬inA fd) (↑ty-arr upA upA₁) lt = f-arr-r (¬ε-↑ty'-inv ¬inA upA lt) (↑ty-find' fd upA₁ lt)
↑ty-find' (f-∀ fd) (↑ty-∀ upA) lt = f-∀ (↑ty-find' fd upA (s≤s lt))

↑ty-find0' : find A' #0 j
            → A ↑ty (#S k) ⇘ A'
            → find A #0 j
↑ty-find0' fd upA = ↑ty-find' fd upA (s≤s z≤n)


find-ε-gen : find A k j
           → k ε A
find-ε-gen (f-□ inA) = inA
find-ε-gen (f-iso iso) = ε-var
find-ε-gen (f-arr-l inA) = ε-arr-l inA
find-ε-gen (f-arr-r ¬inA fd) = ε-arr-r ¬inA (find-ε-gen fd)
find-ε-gen (f-∀ fd) = ε-∀ (find-ε-gen fd)
