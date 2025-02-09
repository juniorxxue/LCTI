module Implicit.Language.Lookup.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.Base

∋⦂-unique : Γ ∋ x ⦂ A
          → Γ ∋ x ⦂ B
          → A ≡ B
∋⦂-unique Z Z = refl
∋⦂-unique (S, in1) (S, in2) = ∋⦂-unique in1 in2
∋⦂-unique (S∙ in1 x) (S∙ in2 x₁) rewrite ∋⦂-unique in1 in2 = ↑ty-unique x x₁
∋⦂-unique (S^ in1 x) (S^ in2 up) rewrite ∋⦂-unique in1 in2 = ↑ty-unique x up
∋⦂-unique (S= in1 x) (S= in2 x₁) rewrite ∋⦂-unique in1 in2 = ↑ty-unique x x₁

∋:=-unique : Γ ∋ k := A
           → Γ ∋ k := B
           → A ≡ B
∋:=-unique (Z up) (Z up₁) = ↑ty-unique up up₁
∋:=-unique (S, in1) (S, in2) = ∋:=-unique in1 in2
∋:=-unique (S∙ in1 up) (S∙ in2 up₁) with ∋:=-unique in1 in2
... | refl = ↑ty-unique up up₁
∋:=-unique (S^ in1 up) (S^ in2 up₁) with ∋:=-unique in1 in2
... | refl = ↑ty-unique up up₁
∋:=-unique (S= in1 up) (S= in2 up₁) with ∋:=-unique in1 in2
... | refl = ↑ty-unique up up₁


∋:=-total : Γ ∋= X
          → ∃[ A ](Γ ∋ X := A)
∋:=-total (Z {A = A}) with ↑ty0-total A
... | ⟨ A' , upA ⟩ = ⟨ A' , Z upA ⟩
∋:=-total (S, inΓ) = ⟨ ∋:=-total inΓ .proj₁ , S, (∋:=-total inΓ .proj₂) ⟩
∋:=-total (S∙ inΓ) with ∋:=-total inΓ
... | ⟨ A , AinΓ ⟩ = let ⟨ A' , upA ⟩ = ↑ty0-total A in ⟨ A' , S∙ AinΓ upA ⟩
∋:=-total (S^ inΓ) with ∋:=-total inΓ
... | ⟨ A , AinΓ ⟩ = let ⟨ A' , upA ⟩ = ↑ty0-total A in ⟨ A' , S^ AinΓ upA ⟩
∋:=-total (S= inΓ) with ∋:=-total inΓ
... | ⟨ A , AinΓ ⟩ = let ⟨ A' , upA ⟩ = ↑ty0-total A in ⟨ A' , S= AinΓ upA ⟩

∋:=to∋= : Γ ∋ k := A
      → Γ ∋= k
∋:=to∋= (Z up) = Z
∋:=to∋= (S, inΓ) = S, (∋:=to∋= inΓ)
∋:=to∋= (S^ inΓ up) = S^ (∋:=to∋= inΓ)
∋:=to∋= (S∙ inΓ up) = S∙ (∋:=to∋= inΓ)
∋:=to∋= (S= inΓ up) = S= (∋:=to∋= inΓ)


----------------------------------------------------------------------
--+                       False elimination                        +--
----------------------------------------------------------------------

∋^-∋∙-false :
    Γ ∋^ k
  → Γ ∋∙ k
  → ⊥
∋^-∋∙-false (S^ ^in) (S^ ∙in) = ∋^-∋∙-false ^in ∙in
∋^-∋∙-false (S∙ ^in) (S∙ ∙in) = ∋^-∋∙-false ^in ∙in
∋^-∋∙-false (S, ^in) (S, ∙in) = ∋^-∋∙-false ^in ∙in
∋^-∋∙-false (S= ^in) (S= ∙in) = ∋^-∋∙-false ^in ∙in

∋^-∋=-false :
    Γ ∋^ k
  → Γ ∋= k
  → ⊥
∋^-∋=-false (S^ in1) (S^ in2) = ∋^-∋=-false in1 in2
∋^-∋=-false (S∙ in1) (S∙ in2) = ∋^-∋=-false in1 in2
∋^-∋=-false (S, in1) (S, in2) = ∋^-∋=-false in1 in2
∋^-∋=-false (S= in1) (S= in2) = ∋^-∋=-false in1 in2

∋∙-∋=-false :
    Γ ∋∙ X
  → Γ ∋= X
  → ⊥
∋∙-∋=-false (S, in1) (S, in2) = ∋∙-∋=-false in1 in2
∋∙-∋=-false (S∙ in1) (S∙ in2) = ∋∙-∋=-false in1 in2
∋∙-∋=-false (S= in1) (S= in2) = ∋∙-∋=-false in1 in2
∋∙-∋=-false (S^ in1) (S^ in2) = ∋∙-∋=-false in1 in2

∋∙-∋:=-false :
    Γ ∋∙ X
  → Γ ∋ X := A
  → ⊥
∋∙-∋:=-false (S, inΓ) (S, inΓ') = ∋∙-∋:=-false inΓ inΓ'
∋∙-∋:=-false (S∙ inΓ) (S∙ inΓ' up) = ∋∙-∋:=-false inΓ inΓ'
∋∙-∋:=-false (S= inΓ) (S= inΓ' up) = ∋∙-∋:=-false inΓ inΓ'
∋∙-∋:=-false (S^ inΓ) (S^ inΓ' up) = ∋∙-∋:=-false inΓ inΓ'
