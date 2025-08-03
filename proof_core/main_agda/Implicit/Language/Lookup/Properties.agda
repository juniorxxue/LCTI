module Implicit.Language.Lookup.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.Base

abstract

  ∋⦂-unique : Γ ∋ x ⦂ A
            → Γ ∋ x ⦂ B
            → A ≡ B
  ∋⦂-unique Z Z = refl
  ∋⦂-unique (S, in1) (S, in2) = ∋⦂-unique in1 in2
  ∋⦂-unique (S∙ in1 x) (S∙ in2 x₁) rewrite ∋⦂-unique in1 in2 = ↑ty-unique x x₁
  ∋⦂-unique (S^ in1 x) (S^ in2 up) rewrite ∋⦂-unique in1 in2 = ↑ty-unique x up
  ∋⦂-unique (S= in1 x) (S= in2 x₁) rewrite ∋⦂-unique in1 in2 = ↑ty-unique x x₁
  ∋⦂-unique (S⋈ in1) (S⋈ in2) rewrite ∋⦂-unique in1 in2 = refl

  ∋:=-unique : Γ ∋ k := A
             → Γ ∋ k := B
             → A ≡ B
  ∋:=-unique (Z up) (Z up₁) = ↑ty-unique up up₁
  ∋:=-unique (S∙ in1 up) (S∙ in2 up₁) with ∋:=-unique in1 in2
  ... | refl = ↑ty-unique up up₁
  ∋:=-unique (S^ in1 up) (S^ in2 up₁) with ∋:=-unique in1 in2
  ... | refl = ↑ty-unique up up₁
  ∋:=-unique (S= in1 up) (S= in2 up₁) with ∋:=-unique in1 in2
  ... | refl = ↑ty-unique up up₁
  ∋:=-unique (S, in1 ) (S, in2)  with ∋:=-unique in1 in2
  ... | refl = refl
  ∋:=-unique (S⋈ in1) (S⋈ in2) rewrite ∋:=-unique in1 in2 = refl

  ∋:=-total : Γ ∋= X
            → ∃[ A ](Γ ∋ X := A)
  ∋:=-total (Z {A = A}) with ↑ty0-total A
  ... | ⟨ A' , upA ⟩ = ⟨ A' , Z upA ⟩
  ∋:=-total (S∙ inΓ) with ∋:=-total inΓ
  ... | ⟨ A , AinΓ ⟩ = let ⟨ A' , upA ⟩ = ↑ty0-total A in ⟨ A' , S∙ AinΓ upA ⟩
  ∋:=-total (S^ inΓ) with ∋:=-total inΓ
  ... | ⟨ A , AinΓ ⟩ = let ⟨ A' , upA ⟩ = ↑ty0-total A in ⟨ A' , S^ AinΓ upA ⟩
  ∋:=-total (S= inΓ) with ∋:=-total inΓ
  ... | ⟨ A , AinΓ ⟩ = let ⟨ A' , upA ⟩ = ↑ty0-total A in ⟨ A' , S= AinΓ upA ⟩
  ∋:=-total (S, inΓ) with ∋:=-total inΓ
  ... | ⟨ A , inΓ ⟩ = ⟨ A , S, inΓ ⟩
  ∋:=-total (S⋈ inΓ) with ∋:=-total inΓ
  ... | ⟨ A , inΓ ⟩ = ⟨ A , S⋈ inΓ ⟩


  ∋:=to∋= : Γ ∋ k := A
        → Γ ∋= k
  ∋:=to∋= (Z up) = Z
  ∋:=to∋= (S^ inΓ up) = S^ (∋:=to∋= inΓ)
  ∋:=to∋= (S∙ inΓ up) = S∙ (∋:=to∋= inΓ)
  ∋:=to∋= (S= inΓ up) = S= (∋:=to∋= inΓ)
  ∋:=to∋= (S, inΓ) = S, (∋:=to∋= inΓ)
  ∋:=to∋= (S⋈ inΓ) = S⋈ (∋:=to∋= inΓ)

  ∋∙-⋈-pred : Γ ⋈ ∋∙ X
            → Γ ∋∙ X
  ∋∙-⋈-pred (S⋈ inΓ) = inΓ

----------------------------------------------------------------------
--+                       False elimination                        +--
----------------------------------------------------------------------

abstract

  ∋^-∋∙-false :
      Γ ∋^ k
    → Γ ∋∙ k
    → ⊥
  ∋^-∋∙-false (S^ ^in) (S^ ∙in) = ∋^-∋∙-false ^in ∙in
  ∋^-∋∙-false (S∙ ^in) (S∙ ∙in) = ∋^-∋∙-false ^in ∙in
  ∋^-∋∙-false (S= ^in) (S= ∙in) = ∋^-∋∙-false ^in ∙in
  ∋^-∋∙-false (S, ^in) (S, ∙in) = ∋^-∋∙-false ^in ∙in
  ∋^-∋∙-false (S⋈ ^in) (S⋈ ∙in) = ∋^-∋∙-false ^in ∙in

  ∋^-∋=-false :
      Γ ∋^ k
    → Γ ∋= k
    → ⊥
  ∋^-∋=-false (S^ in1) (S^ in2) = ∋^-∋=-false in1 in2
  ∋^-∋=-false (S∙ in1) (S∙ in2) = ∋^-∋=-false in1 in2
  ∋^-∋=-false (S= in1) (S= in2) = ∋^-∋=-false in1 in2
  ∋^-∋=-false (S, in1) (S, in2) = ∋^-∋=-false in1 in2
  ∋^-∋=-false (S⋈ in1) (S⋈ in2) = ∋^-∋=-false in1 in2

  ∋∙-∋=-false :
      Γ ∋∙ X
    → Γ ∋= X
    → ⊥
  ∋∙-∋=-false (S∙ in1) (S∙ in2) = ∋∙-∋=-false in1 in2
  ∋∙-∋=-false (S= in1) (S= in2) = ∋∙-∋=-false in1 in2
  ∋∙-∋=-false (S^ in1) (S^ in2) = ∋∙-∋=-false in1 in2
  ∋∙-∋=-false (S, in1) (S, in2) = ∋∙-∋=-false in1 in2
  ∋∙-∋=-false (S⋈ in1) (S⋈ in2) = ∋∙-∋=-false in1 in2

  ∋∙-∋:=-false :
      Γ ∋∙ X
    → Γ ∋ X := A
    → ⊥
  ∋∙-∋:=-false (S∙ inΓ) (S∙ inΓ' up) = ∋∙-∋:=-false inΓ inΓ'
  ∋∙-∋:=-false (S= inΓ) (S= inΓ' up) = ∋∙-∋:=-false inΓ inΓ'
  ∋∙-∋:=-false (S^ inΓ) (S^ inΓ' up) = ∋∙-∋:=-false inΓ inΓ'
  ∋∙-∋:=-false (S, in1) (S, in2) = ∋∙-∋:=-false in1 in2
  ∋∙-∋:=-false (S⋈ in1) (S⋈ in2) = ∋∙-∋:=-false in1 in2

  ∋∙-∋^-≢ : Γ ∋∙ k₁
          → Γ ∋^ k₂
          → k₁ ≢ k₂
  ∋∙-∋^-≢ Z (S∙ inΓ2) = λ ()
  ∋∙-∋^-≢ (S∙ inΓ1) (S∙ inΓ2) = ≢-suc (∋∙-∋^-≢ inΓ1 inΓ2)
  ∋∙-∋^-≢ (S= inΓ1) (S= inΓ2) = ≢-suc (∋∙-∋^-≢ inΓ1 inΓ2)
  ∋∙-∋^-≢ (S^ inΓ1) Z = λ ()
  ∋∙-∋^-≢ (S^ inΓ1) (S^ inΓ2) = ≢-suc (∋∙-∋^-≢ inΓ1 inΓ2)
  ∋∙-∋^-≢ (S, inΓ1) (S, inΓ2) = ∋∙-∋^-≢ inΓ1 inΓ2
  ∋∙-∋^-≢ (S⋈ inΓ1) (S⋈ inΓ2) = ∋∙-∋^-≢ inΓ1 inΓ2

  ∋=-∋^-≢ : Γ ∋= k₁
          → Γ ∋^ k₂
          → k₁ ≢ k₂
  ∋=-∋^-≢ Z (S= in2) = λ ()
  ∋=-∋^-≢ (S∙ inΓ1) (S∙ inΓ2) = ≢-suc (∋=-∋^-≢ inΓ1 inΓ2)
  ∋=-∋^-≢ (S= inΓ1) (S= inΓ2) = ≢-suc (∋=-∋^-≢ inΓ1 inΓ2)
  ∋=-∋^-≢ (S^ inΓ1) Z = λ ()
  ∋=-∋^-≢ (S^ inΓ1) (S^ inΓ2) = ≢-suc (∋=-∋^-≢ inΓ1 inΓ2)
  ∋=-∋^-≢ (S, inΓ1) (S, inΓ2) = ∋=-∋^-≢ inΓ1 inΓ2
  ∋=-∋^-≢ (S⋈ inΓ1) (S⋈ inΓ2) = ∋=-∋^-≢ inΓ1 inΓ2

  ∋∙-∋=-≢ : Γ ∋∙ k₁
          → Γ ∋= k₂
          → k₁ ≢ k₂
  ∋∙-∋=-≢ Z (S∙ in2) = λ ()
  ∋∙-∋=-≢ (S, in1) (S, in2) = ∋∙-∋=-≢ in1 in2
  ∋∙-∋=-≢ (S∙ in1) (S∙ in2) = ≢-suc (∋∙-∋=-≢ in1 in2)
  ∋∙-∋=-≢ (S= in1) Z = λ ()
  ∋∙-∋=-≢ (S= in1) (S= in2) = ≢-suc (∋∙-∋=-≢ in1 in2)
  ∋∙-∋=-≢ (S^ in1) (S^ in2) = ≢-suc (∋∙-∋=-≢ in1 in2)
  ∋∙-∋=-≢ (S⋈ in1) (S⋈ in2) = ∋∙-∋=-≢ in1 in2
