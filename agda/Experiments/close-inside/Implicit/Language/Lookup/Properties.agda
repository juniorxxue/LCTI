module Implicit.Language.Lookup.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Lookup.Base
open import Implicit.Language.Shift

∋⦂-unique : Γ ∋ x ⦂ A
          → Γ ∋ x ⦂ B
          → A ≡ B
∋⦂-unique Z Z = refl
∋⦂-unique (S, in1) (S, in2) = ∋⦂-unique in1 in2
∋⦂-unique (S∙ in1 x) (S∙ in2 x₁) rewrite ∋⦂-unique in1 in2 = ↑ty-unique x x₁
∋⦂-unique (S^ in1 x) (S^ in2 up) rewrite ∋⦂-unique in1 in2 = ↑ty-unique x up
∋⦂-unique (S= in1 x) (S= in2 x₁) rewrite ∋⦂-unique in1 in2 = ↑ty-unique x x₁



↑ty-ε : X ε A
      → A ↑ty k ⇘ A'
      → X #< k
      → inject₁ X ε A'
↑ty-ε ε-var ↑ty-var lt rewrite punchIn-inject lt = ε-var
↑ty-ε (ε-arr-l inA) (↑ty-arr up up₁) lt = ε-arr-l (↑ty-ε inA up lt)
↑ty-ε (ε-arr-r inA) (↑ty-arr up up₁) lt = ε-arr-r (↑ty-ε inA up₁ lt)
↑ty-ε (ε-∀ inA) (↑ty-∀ up) lt = ε-∀ (↑ty-ε inA up (s≤s lt))
{-
↑ty-¬ε : X ¬ε A
      → A ↑ty k ⇘ A'
      → X #< k
      → inject₁ X ¬ε A'
↑ty-¬ε ¬ε-int ↑ty-int lt = ¬ε-int
↑ty-¬ε (¬ε-var x) ↑ty-var lt = ¬ε-var (punchIn-inject-neq lt x)
↑ty-¬ε (¬ε-arr ninA ninA₁) (↑ty-arr up up₁) lt = ¬ε-arr (↑ty-¬ε ninA up lt) (↑ty-¬ε ninA₁ up₁ lt)
↑ty-¬ε (¬ε-∀ ninA) (↑ty-∀ up) lt = ¬ε-∀ (↑ty-¬ε ninA up (s≤s lt))
-}

:=to= : Γ ∋ k := A
      → Γ ∋= k
:=to= (Z up) = Z
:=to= (S, inΓ) = S, (:=to= inΓ)
:=to= (S^ inΓ up) = S^ (:=to= inΓ)
:=to= (S∙ inΓ up) = S∙ (:=to= inΓ)
:=to= (S= inΓ up) = S= (:=to= inΓ)


----------------------------------------------------------------------
--+                       False elimination                        +--
----------------------------------------------------------------------

^∈-∙∈-false :
    Γ ∋^ k
  → Γ ∋∙ k
  → ⊥
^∈-∙∈-false (S^ ^in) (S^ ∙in) = ^∈-∙∈-false ^in ∙in
^∈-∙∈-false (S∙ ^in) (S∙ ∙in) = ^∈-∙∈-false ^in ∙in
^∈-∙∈-false (S, ^in) (S, ∙in) = ^∈-∙∈-false ^in ∙in
^∈-∙∈-false (S= ^in) (S= ∙in) = ^∈-∙∈-false ^in ∙in

^∈-=∈-false :
    Γ ∋^ k
  → Γ ∋= k
  → ⊥
^∈-=∈-false (S^ in1) (S^ in2) = ^∈-=∈-false in1 in2
^∈-=∈-false (S∙ in1) (S∙ in2) = ^∈-=∈-false in1 in2
^∈-=∈-false (S, in1) (S, in2) = ^∈-=∈-false in1 in2
^∈-=∈-false (S= in1) (S= in2) = ^∈-=∈-false in1 in2

∙∈-=∈-false :
    Γ ∋∙ X
  → Γ ∋= X
  → ⊥
∙∈-=∈-false (S, in1) (S, in2) = ∙∈-=∈-false in1 in2
∙∈-=∈-false (S∙ in1) (S∙ in2) = ∙∈-=∈-false in1 in2
∙∈-=∈-false (S= in1) (S= in2) = ∙∈-=∈-false in1 in2
∙∈-=∈-false (S^ in1) (S^ in2) = ∙∈-=∈-false in1 in2
