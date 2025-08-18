{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}
module Implicit.Interm2Algo.NewSpine where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm.All

open import Implicit.Interm2Algo.Counter2Context
open import Implicit.Interm2Algo.ReExtension
open import Implicit.Interm2Algo.ExtIrrev
open import Implicit.Interm2Algo.EnvDiff
open import Implicit.Interm2Algo.OpenClose
open import Implicit.Interm2Algo.Find
open import Implicit.Interm2Algo.AuxLemmas

{-
data _~pk~_w/_↪_ : Type (1 + m) → Context n (1 + m) → Fin (1 + m) → Type m → Set where
  pk-type : A ~~pk~~ B w/ k ↪ C
          → A ~pk~ (Context n (1 + m) ∋⦂ τ B) w/ k ↪ C
  pk-term : B ~pk~ Σ w/ k ↪ C
          → A `→ B ~pk~ [ e ]↝ Σ w/ k ↪ C
  pk-∀l   : A ~pk~ [ e' ]↝ Σ' w/ (#S k) ↪ C'
          → (upΣ : ↑tyᶜ0 Σ ⇘ Σ')
          → (upe : ↑tyᵉ0 e ⇘ e')
          → (upC : ↑ty0 C ⇘ C')
          → `∀ A ~pk~ [ e ]↝ Σ w/ k ↪ C
  pk-tapp : A ~pk~ Σ' w/ (#S k) ↪ C'
          → (upC : ↑ty0 C ⇘ C')
          → (upΣ : ↑tyᶜ0 Σ ⇘ Σ')
          → `∀ A ~pk~ (B ⓪↝ Σ) w/ k ↪ C
-}


data peek-a : Type (1 + m) → Type (1 + m) → Fin (1 + m) → Counter (1 + m) → Type m → Set where
  pka-∞ : A ~~pk~~ B w/ k ↪ C
--        → ↑ty0 C ⇘ C'
        → peek-a A B k ∞ C
  pka-arr-𝕚 : peek-a B D k j E
            → peek-a (A `→ B) (C `→ D) k (𝕚 j) E
  pka-arr-𝕔 : peek-a B D k j E
            → peek-a (A `→ B) (C `→ D) k (𝕔 j) E
  pka-∀-𝕚 : peek-a A (C' `→ D') (#S k) (𝕚 j') E'
          → (upC : ↑ty0 C ⇘ C')
          → (upD : ↑ty0 D ⇘ D')
          → (upE : ↑ty0 E ⇘ E')
          → (upj : ↑tyʲ0 j ⇘ j')
          → peek-a (`∀ A) (C `→ D) k (𝕚 j) E
  pka-∀-𝕔 : peek-a A (C' `→ D') (#S k) (𝕔 j') E'
          → (upC : ↑ty0 C ⇘ C')
          → (upD : ↑ty0 D ⇘ D')
          → (upE : ↑ty0 E ⇘ E')
          → (upj : ↑tyʲ0 j ⇘ j')
          → peek-a (`∀ A) (C `→ D) k (𝕔 j) E
  pka-∀-𝕥 : peek-a A B (#S k) j' E'
          → (upB : ↑ty0 E ⇘ E')
          → (upj : ↑tyʲ0 j ⇘ j')
          → peek-a (`∀ A) (`∀ B) k (𝕥₍ T ₎ j) E


peek→peek-t : Γ ⊢ ∞ # A ⌞ ≤⁺ ⌝ B
            → Γ ∋ k := T
            → k ε A
            → ∃[ pT ]((A ~~pk~~ B w/ k ↪ pT) × (↑ty0 pT ⇘ T))
-- peek→peek-t (s-var-∙ regΔ inΔ) inΓ ε-var = ⟨ {!!} , ⟨ (pk-var-l {!!}) , {!!} ⟩ ⟩
-- peek→peek-t (s-arr₁ s s₁) inΓ (ε-arr-l inA) = {!!}
-- peek→peek-t (s-arr₁ s s₁) inΓ (ε-arr-r ¬inA inA) = {!!}
-- peek→peek-t (s-∀ s) inΓ inA = {!!}
-- peek→peek-t (s-svar-l x inΔ) inΓ inA = {!!}

peek→peek-a : ∀ {pT}
            → Γ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → peek A k j
            → Γ ∋ k := T
            → ↑ty0 pT ⇘ T
            → peek-a A B k j pT
-- peek→peek-a s (peek-base inA) inΓ = pka-∞ {!!} {!!}
-- peek→peek-a (s-arr₂ s s₁) (peek-arr-i pk) inΓ = pka-arr-𝕚 (peek→peek-a s₁ pk inΓ)
-- peek→peek-a (s-arr₃ cloA grd s) (peek-arr-c pk) inΓ = pka-arr-𝕔 (peek→peek-a s pk inΓ)
-- peek→peek-a (s-∀l s ic fd upC upD upj₁) (peek-∀-i pk upj) inΓ = {!!} -- ignore
-- peek→peek-a {T = T} (s-∀l-new s ic ¬pk fd upC upD (↑tyʲ-𝕚 upj₁)) (peek-∀-i pk upj) inΓ
--   with refl ← ↑tyʲ-unique upj upj₁
--   with ⟨ T' , upT ⟩ ← ↑ty0-total T
--   = pka-∀-𝕚 (peek→peek-a s pk (S= inΓ upT)) upC upD upT upj₁
-- peek→peek-a {T = T} (s-∀l-peek s ic pk₁ upC upD (↑tyʲ-𝕚 upj₁)) (peek-∀-i pk upj) inΓ = {!!}
-- peek→peek-a (s-∀l-no-appear s ic fd upC upD upj₁) (peek-∀-i pk upj) inΓ = {!!}
-- peek→peek-a s (peek-∀-c pk upj) inΓ = {!!}
-- peek→peek-a s (peek-∀-t pk upj) inΓ = {!!}


peek-a-~pk~ : peek-a A B k j C
            → Γ ⊢ ⟨ j , B ⟩ ~s Σ
            → A ~pk~ Σ w/ k ↪ C
peek-a-~pk~ (pka-∞ x) ~∞ = pk-type x
peek-a-~pk~ (pka-arr-𝕚 pka) (~I ⊢e ~j) = pk-term (peek-a-~pk~ pka ~j)
peek-a-~pk~ (pka-arr-𝕔 pka) (~C ⊢e ~j) = pk-term (peek-a-~pk~ pka ~j)
peek-a-~pk~ (pka-∀-𝕚 pka upC upD upE upj) ~j'@(~I {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , up-e ⟩ ← ↑tyᵉ0-total e
  = pk-∀l (peek-a-~pk~ pka (~weaken^0 ~j' (↑ty-arr upC upD) (↑tyᶜ-e up-e upΣ) (↑tyʲ-𝕚 upj))) upΣ up-e upE
peek-a-~pk~ (pka-∀-𝕔 pka upC upD upE upj) ~j'@(~C {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , up-e ⟩ ← ↑tyᵉ0-total e
  = pk-∀l (peek-a-~pk~ pka (~weaken^0 ~j' (↑ty-arr upC upD) (↑tyᶜ-e up-e upΣ) (↑tyʲ-𝕔 upj))) upΣ up-e upE
peek-a-~pk~ (pka-∀-𝕥 pka upB upj) (~T {Σ = Σ} ~j st)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  = pk-tapp (peek-a-~pk~ pka {!~j!}) upB upΣ
