module Implicit.Algo.Properties.Peek where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Shift

pk-ε : A ~~pk~~ B w/ k ↪ T
     → k ε A
pk-ε pk-var-l = ε-var
pk-ε (pk-arr-l pk) = ε-arr-l (pk-ε pk)
pk-ε {k = k} (pk-arr-r {A = A} pk) with ε-dec {k = k} {A = A}
... | inj₁ inA = ε-arr-l inA
... | inj₂ ¬inA = ε-arr-r ¬inA (pk-ε pk)
pk-ε (pk-∀ pk upC) = ε-∀ (pk-ε pk)



pk-var-l-helper : k₁ ≡ k₂
                → ‶ k₁ ~~pk~~ A w/ k₂ ↪ A
pk-var-l-helper refl = pk-var-l

peek-t-weaken=-lemma : A ~~pk~~ B w/ X ↪ C
                     → A ↑ty k ⇘ A'
                     → B ↑ty k ⇘ B'
                     → C ↑ty k ⇘ C'
                     → X #< k
                     → A' ~~pk~~ B' w/ (inject₁ X) ↪ C'
peek-t-weaken=-lemma pk-var-l ↑ty-var upB upC lt
  with refl ← ↑ty-unique upB upC
  with eq ← punchIn-inject lt
  = pk-var-l-helper (sym eq)
peek-t-weaken=-lemma (pk-arr-l pk) (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) upC lt = pk-arr-l (peek-t-weaken=-lemma pk upA upB upC lt)
peek-t-weaken=-lemma (pk-arr-r pk) (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) upC lt = pk-arr-r (peek-t-weaken=-lemma pk upA₁ upB₁ upC lt)
peek-t-weaken=-lemma {C' = C} (pk-∀ pk upC₁) (↑ty-∀ upA) (↑ty-∀ upB) upC lt
  with ⟨ C₁ , upC₂ ⟩ ← ↑ty0-total C
  = pk-∀ (peek-t-weaken=-lemma pk upA upB (↑ty-comm0' upC upC₂ upC₁) (s≤s lt)) upC₂


peek-weaken=-lemma : A ~pk~ Σ w/ X ↪ B
                   → Σ ↑tyᶜ k ⇘ Σ'
                   → A ↑ty k ⇘ A'
                   → B ↑ty k ⇘ B'
                   → X #< k
                   → A' ~pk~ Σ' w/ (inject₁ X) ↪ B'
peek-weaken=-lemma (pk-type x) (↑tyᶜ-τ up-t) upA upB lt = pk-type (peek-t-weaken=-lemma x upA up-t upB lt)
peek-weaken=-lemma (pk-term pk) (↑tyᶜ-e up-e upΣ) (↑ty-arr upA upA₁) upB lt = pk-term (peek-weaken=-lemma pk upΣ upA₁ upB lt)
peek-weaken=-lemma {B' = B₁} (pk-∀l pk upΣ₁ upe upC) (↑tyᶜ-e {e' = e₁} {Σ' = Σ₁} up-e upΣ) (↑ty-∀ upA) upB lt
  with ⟨ B₁' , upB₁ ⟩ ← ↑ty0-total B₁
  with ⟨ e₁' , up-e₁ ⟩ ← ↑tyᵉ0-total e₁
  with ⟨ Σ₁ , upΣ₂ ⟩ ← ↑tyᶜ0-total Σ₁
  = pk-∀l (peek-weaken=-lemma pk (↑tyᶜ-comm0' (↑tyᶜ-e up-e upΣ) (↑tyᶜ-e up-e₁ upΣ₂)
                                   (↑tyᶜ-e upe upΣ₁)) upA (↑ty-comm0' upB upB₁ upC) (s≤s lt)) upΣ₂ up-e₁ upB₁
peek-weaken=-lemma {B' = B₁} (pk-tapp pk upC upΣ₁) (↑tyᶜ-⓪ {Σ' = Σ₁} upA₁ upΣ) (↑ty-∀ upA) upB lt
  with ⟨ B₁' , upB₁ ⟩ ← ↑ty0-total B₁
  with ⟨ Σ₁ , upΣ₂ ⟩ ← ↑tyᶜ0-total Σ₁
  = pk-tapp (peek-weaken=-lemma pk (↑tyᶜ-comm0' upΣ upΣ₂ upΣ₁) upA (↑ty-comm0' upB upB₁ upC) (s≤s lt)) upB₁ upΣ₂

peek-t-strengthen=-lemma : A' ~~pk~~ B' w/ (inject₁ X) ↪ C'
                     → A ↑ty k ⇘ A'
                     → B ↑ty k ⇘ B'
                     → C ↑ty k ⇘ C'
                     → X #< k
                         → A ~~pk~~ B w/ X ↪ C
peek-t-strengthen=-lemma {X = Y} {A = ‶ X} {k = k} pk-var-l upA upB upC lt
  with refl ← ↑ty-unique-inver upB upC
  with eq1 ← ↑ty-var-inv-eq upA
  with eq2 ← punchIn-inject lt
  = pk-var-l-helper (punchIn-injective k X Y ((trans (sym eq1) eq2)))
peek-t-strengthen=-lemma (pk-arr-l pk) (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) upC lt = pk-arr-l (peek-t-strengthen=-lemma pk upA upB upC lt)
peek-t-strengthen=-lemma (pk-arr-r pk) (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) upC lt = pk-arr-r (peek-t-strengthen=-lemma pk upA₁ upB₁ upC lt)
peek-t-strengthen=-lemma {C = C} (pk-∀ pk upC₁) (↑ty-∀ upA) (↑ty-∀ upB) upC lt
  with ⟨ C' , upC₂ ⟩ ← ↑ty0-total C
  = pk-∀ (peek-t-strengthen=-lemma pk upA upB (↑ty-comm0' upC upC₁ upC₂) (s≤s lt)) upC₂

peek-strengthen=-lemma : A' ~pk~ Σ' w/ (inject₁ X) ↪ B'
                   → Σ ↑tyᶜ k ⇘ Σ'
                   → A ↑ty k ⇘ A'
                   → B ↑ty k ⇘ B'
                   → X #< k
                    → A ~pk~ Σ w/ X ↪ B
peek-strengthen=-lemma (pk-type x) (↑tyᶜ-τ up-t) upA upB lt = pk-type (peek-t-strengthen=-lemma x upA up-t upB lt)
peek-strengthen=-lemma (pk-term pk) (↑tyᶜ-e up-e upΣ) (↑ty-arr upA upA₁) upB lt = pk-term (peek-strengthen=-lemma pk upΣ upA₁ upB lt)
peek-strengthen=-lemma {B = B} (pk-∀l pk upΣ₁ upe upC) (↑tyᶜ-e {e = e} {Σ = Σ} up-e upΣ) (↑ty-∀ upA) upB lt
  with ⟨ B' , upB₁ ⟩ ← ↑ty0-total B
  with ⟨ e' , up-e' ⟩ ← ↑tyᵉ0-total e
  with ⟨ Σ' , up-Σ ⟩ ← ↑tyᶜ0-total Σ
  = pk-∀l (peek-strengthen=-lemma pk (↑tyᶜ-e (↑tyᵉ-comm0' up-e upe up-e') (↑tyᶜ-comm0' upΣ upΣ₁ up-Σ)) upA (↑ty-comm0' upB upC upB₁) (s≤s lt)) up-Σ up-e' upB₁
peek-strengthen=-lemma {B = B} (pk-tapp pk upC upΣ₁) (↑tyᶜ-⓪  {Σ = Σ} upA₁ upΣ) (↑ty-∀ upA) upB lt
  with ⟨ B' , upB₁ ⟩ ← ↑ty0-total B
  with ⟨ Σ' , up-Σ ⟩ ← ↑tyᶜ0-total Σ
  = pk-tapp (peek-strengthen=-lemma pk (↑tyᶜ-comm0' upΣ upΣ₁ up-Σ) upA (↑ty-comm0' upB upC upB₁) (s≤s lt)) upB₁ up-Σ
