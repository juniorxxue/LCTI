{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}
module Implicit.Language.Find.Properties where


open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Occur.All
open import Implicit.Language.Find.Base

¬find-¬ε : ¬find A k j
         → k ¬ε A
¬find-¬ε f-z = {!!}
¬find-¬ε (f-∞ x) = x
¬find-¬ε (f-arr-𝕚 x ¬fd) = ¬ε-arr x (¬find-¬ε ¬fd)
¬find-¬ε (f-arr-𝕔 ¬fd) = {!!}
¬find-¬ε (f-∀-𝕚 ¬fd upj) = ¬ε-∀ (¬find-¬ε ¬fd)
¬find-¬ε (f-∀-𝕔 ¬fd upj) = ¬ε-∀ (¬find-¬ε ¬fd)
¬find-¬ε (f-𝕥 ¬fd upj) = ¬ε-∀ (¬find-¬ε ¬fd)


↑ty-find : find A X j
         → A ↑ty k ⇘ A'
         → j ↑tyʲ k ⇘ j'
         → X #< k
         → find A' (inject₁ X) j'
↑ty-find (f-∞ x) upA ↑tyʲ-∞ lt = f-∞ (↑ty-ε x upA lt)
↑ty-find (f-arr-𝕚-l x ¬fd) (↑ty-arr upA upA₁) (↑tyʲ-𝕚 upj) lt = f-arr-𝕚-l (↑ty-ε x upA lt) {!!}
↑ty-find (f-arr-𝕚-r fd) (↑ty-arr upA upA₁) (↑tyʲ-𝕚 upj) lt = f-arr-𝕚-r (↑ty-find fd upA₁ upj lt)
-- f-arr-𝕚-r (↑ty-¬ε-prv ¬inA upA lt) (↑ty-find fd upA₁ upj lt)
↑ty-find (f-arr-𝕔 fd) (↑ty-arr upA upA₁) (↑tyʲ-𝕔 upj) lt = f-arr-𝕔 (↑ty-find fd upA₁ upj lt)
↑ty-find (f-∀-𝕚 fd upj₁) (↑ty-∀ upA) (↑tyʲ-𝕚 {j' = j'} upj) lt
  with ⟨ j″ , upj' ⟩ ← ↑tyʲ0-total j' = f-∀-𝕚 (↑ty-find fd upA (↑tyʲ-comm0' (↑tyʲ-𝕚 upj) (↑tyʲ-𝕚 upj') (↑tyʲ-𝕚 upj₁)) (s≤s lt)) upj'
↑ty-find (f-∀-𝕔 fd upj₁) (↑ty-∀ upA) (↑tyʲ-𝕔 {j' = j'} upj) lt
  with ⟨ j″ , upj' ⟩ ← ↑tyʲ0-total j' = f-∀-𝕔 (↑ty-find fd upA (↑tyʲ-𝕔 (↑tyʲ-comm0' upj upj' upj₁)) (s≤s lt)) upj'
↑ty-find (f-𝕥 fd upj₁) (↑ty-∀ upA) (↑tyʲ-𝕥 {j' = j'} upj upA₁) lt
  with ⟨ j″ , upj' ⟩ ← ↑tyʲ0-total j' = f-𝕥 (↑ty-find fd upA (↑tyʲ-comm0' upj upj' upj₁) (s≤s lt)) upj'

↑ty-find0 : find A #0 j
          → A ↑ty (#S k) ⇘ A'
          → j ↑tyʲ (#S k) ⇘ j'
          → find A' #0 j'
↑ty-find0 fd upA upj = ↑ty-find fd upA upj (s≤s z≤n)


↑ty-find' : find A' (inject₁ X) j'
          → A ↑ty k ⇘ A'
          → j ↑tyʲ k ⇘ j'
          → X #< k
          → find A X j
↑ty-find' (f-∞ x) upA ↑tyʲ-∞ lt = f-∞ (↑ty-ε' x lt upA)
↑ty-find' (f-arr-𝕚-l x ¬fd) (↑ty-arr upA upA₁) (↑tyʲ-𝕚 upj) lt = f-arr-𝕚-l (↑ty-ε' x lt upA) {!!}
-- f-arr-𝕚-l (↑ty-ε' x lt upA)
↑ty-find' (f-arr-𝕚-r fd) (↑ty-arr upA upA₁) (↑tyʲ-𝕚 upj) lt = f-arr-𝕚-r (↑ty-find' fd upA₁ upj lt)
-- f-arr-𝕚-r (¬ε-↑ty'-inv ¬inA upA lt) (↑ty-find' fd upA₁ upj lt)
↑ty-find' (f-arr-𝕔 fd) (↑ty-arr upA upA₁) (↑tyʲ-𝕔 upj) lt = f-arr-𝕔 (↑ty-find' fd upA₁ upj lt)
-- f-arr-𝕔 (¬ε-↑ty'-inv ¬inA upA lt) (↑ty-find' fd upA₁ upj lt)
↑ty-find' (f-∀-𝕚 fd upj₁) (↑ty-∀ upA) (↑tyʲ-𝕚 {j = j} upj) lt
  with ⟨ j' , upj' ⟩ ← ↑tyʲ0-total j = f-∀-𝕚 (↑ty-find' fd upA (↑tyʲ-𝕚 (↑tyʲ-comm0' upj upj₁ upj')) (s≤s lt)) upj'
↑ty-find' (f-∀-𝕔 fd upj₁) (↑ty-∀ upA) (↑tyʲ-𝕔 {j = j} upj) lt
  with ⟨ j' , upj' ⟩ ← ↑tyʲ0-total j = f-∀-𝕔 (↑ty-find' fd upA (↑tyʲ-𝕔 (↑tyʲ-comm0' upj upj₁ upj')) (s≤s lt)) upj'
↑ty-find' (f-𝕥 fd upj₁) (↑ty-∀ upA) (↑tyʲ-𝕥 {j = j} upj upA₁) lt
  with ⟨ j' , upj' ⟩ ← ↑tyʲ0-total j = f-𝕥 (↑ty-find' fd upA (↑tyʲ-comm0' upj upj₁ upj') (s≤s lt)) upj'

↑ty-find0' : find A' #0 j'
            → A ↑ty (#S k) ⇘ A'
            → j ↑tyʲ (#S k) ⇘ j'
            → find A #0 j
↑ty-find0' fd upA upj = ↑ty-find' fd upA upj (s≤s z≤n)


find-ε-gen : find A k j
           → k ε A
find-ε-gen (f-∞ x) = x
find-ε-gen (f-arr-𝕚-l x ¬fd) = ε-arr-l {!!} x
find-ε-gen (f-arr-𝕚-r fd) = ε-arr-r (find-ε-gen fd)
find-ε-gen (f-arr-𝕔 fd) = ε-arr-r (find-ε-gen fd)
find-ε-gen (f-∀-𝕚 fd upj) = ε-∀ (find-ε-gen fd)
find-ε-gen (f-∀-𝕔 fd upj) = ε-∀ (find-ε-gen fd)
find-ε-gen (f-𝕥 fd upj) = ε-∀ (find-ε-gen fd)
