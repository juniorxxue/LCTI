module Implicit.Algo.Properties.NewTrans where

-- not exactly like transitivity in classic subtyping
-- since we don't subsume it
-- it only describes the relation between *updates contexts*, used in subsumption lemma in ⊢sub case

open import Implicit.Language.All
open import Implicit.Algo.Base
-- open import Implicit.Algo.Properties.Id
-- open import Implicit.Algo.Properties.OpenClose
-- open import Implicit.Algo.Properties.Polarity

⊆-≫² : Γ ≫² A ⇘ A%
     → Γ ⊆ Δ
     → Δ ≫² A ⇘ A%
⊆-≫² grd-int ext = grd-int
⊆-≫² (grd-var=¹ x) ext = {!!!}
⊆-≫² (grd-var=² x) ext = grd-var=² {!!}
⊆-≫² (grd-var∙ x) ext = {!!}
⊆-≫² (grd-arr grd grd₁) ext = grd-arr (⊆-≫² grd ext) (⊆-≫² grd₁ ext)
⊆-≫² (grd-∀ grd) ext = grd-∀ (⊆-≫² grd (uvar ext))


sub-≫²-prv : Γ ⊢ A₂ ⌞ ≤⁺ ⌝ τ B ⊣ Δ ↪ A₃
     → Γ ≫² A₁ ⇘ A₂
     → Γ ⊢ A₁ ⌞ ≤⁺ ⌝ τ B ⊣ Δ ↪ A₃

sub-≫²-prv' : Γ ⊢ B ⌞ ≤⁻ ⌝ τ A₂ ⊣ Δ ↪ A₃
      → Γ ≫² A₁ ⇘ A₂
      → Γ ⊢ B ⌞ ≤⁻ ⌝ τ A₁ ⊣ Δ ↪ A₃

sub-≫²-prv {A₁ = Int} s grd-int = s
sub-≫²-prv {A₁ = ‶ X} s (grd-var=¹ x) = s
sub-≫²-prv {A₁ = ‶ X} s (grd-var=² x) = {!!}
sub-≫²-prv {A₁ = ‶ X} s (grd-var∙ x) = s
sub-≫²-prv {A₁ = A₁ `→ A₂} (s-ex-typ-r=+ x-in s) (grd-arr ap ap₁) = s-ex-typ-r=+ x-in (sub-≫²-prv s (grd-arr ap ap₁))
sub-≫²-prv {A₁ = A₁ `→ A₂} (s-arr s s₁) (grd-arr ap ap₁) = s-arr (sub-≫²-prv' s ap) (sub-≫²-prv s₁ (⊆-≫² ap₁ {!!}))
sub-≫²-prv {A₁ = `∀ A₁} (s-ex-typ-r=+ x-in s) (grd-∀ ap) = s-ex-typ-r=+ x-in (sub-≫²-prv s (grd-∀ ap))
sub-≫²-prv {A₁ = `∀ A₁} (s-∀ s) (grd-∀ ap) = s-∀ (sub-≫²-prv s ap)


sub-≫²-prv' {A₁ = Int} s grd-int = s
sub-≫²-prv' {A₁ = ‶ X} s (grd-var=¹ x) = s
sub-≫²-prv' {A₁ = ‶ X} s (grd-var=² x) = {!!}
sub-≫²-prv' {A₁ = ‶ X} s (grd-var∙ x) = s
sub-≫²-prv' {A₁ = A₁ `→ A₂} (s-ex-typ-l=- x-in s) (grd-arr ap ap₁) = s-ex-typ-l=- x-in (sub-≫²-prv' s (grd-arr ap ap₁))
sub-≫²-prv' {A₁ = A₁ `→ A₂} (s-arr s s₁) (grd-arr ap ap₁) = s-arr (sub-≫²-prv s ap) (sub-≫²-prv' s₁ (⊆-≫² ap₁ {!!}))
sub-≫²-prv' {A₁ = `∀ A₁} (s-ex-typ-l=- x-in s) (grd-∀ ap) = s-ex-typ-l=- x-in (sub-≫²-prv' s (grd-∀ ap))
sub-≫²-prv' {A₁ = `∀ A₁} (s-∀ s) (grd-∀ ap) = s-∀ (sub-≫²-prv' s ap)


-- s-trans : Γ ⊢ A₁ ⌞ ≤ ⌝ Σ ⊣ Δ ↪ A₂
--         → Δ ⊢ A₂ ⌞ ≤ ⌝ Σ' ⊣ Δ ↪ A₃ -- A₂ couldn't be open
--         → Σ ≊ Σ'
--         → Γ ⊢ A₁ ⌞ ≤ ⌝ Σ' ⊣ Δ ↪ A₃
-- s-trans (s-empty cloΓ clo x) s2 ≊Z = {!!}
-- s-trans (s-term-c cloA ap ⊢e s1) (s-term-c cloA₁ ap₁ ⊢e₁ s2) (≊S newΣ) =
--   s-term-c cloA {!!} {!⊢e!} (s-trans s1 s2 newΣ)
-- s-trans (s-term-c cloA ap ⊢e s1) (s-term-o opnA ⊢e₁ s2 s3) newΣ = {!!}
-- s-trans (s-term-o opnA ⊢e s1 s3) (s-term-c cloA ap ⊢e₁ s2) newΣ =
--   s-term-o opnA {!!} {!!} {!!}
-- s-trans (s-term-o opnA ⊢e s1 s3) (s-term-o opnA₁ ⊢e₁ s2 s4) newΣ = {!!}
-- s-trans (s-∀l s1 upᶜ upᵉ upC upD) (s-term-c cloA ap ⊢e s2) newΣ =
--   s-∀l (s-trans s1 (s-term-c {!!} {!!} {!!} {!!}) {!!}) {!!} {!!} {!!} {!!}
-- s-trans (s-∀l s1 upᶜ upᵉ upC upD) (s-term-o opnA ⊢e s2 s3) newΣ = {!!}
