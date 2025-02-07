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



↑ty-ε : X ε A
      → A ↑ty k ⇘ A'
      → X #< k
      → inject₁ X ε A'
↑ty-ε ε-var ↑ty-var lt rewrite punchIn-inject lt = ε-var
↑ty-ε (ε-arr-l inA) (↑ty-arr up up₁) lt = ε-arr-l (↑ty-ε inA up lt)
↑ty-ε (ε-arr-r inA) (↑ty-arr up up₁) lt = ε-arr-r (↑ty-ε inA up₁ lt)
↑ty-ε (ε-∀ inA) (↑ty-∀ up) lt = ε-∀ (↑ty-ε inA up (s≤s lt))

‶-injective : ‶ X ≡ ‶ Y
            → X ≡ Y
‶-injective refl = refl

#S-injective : #S X ≡ #S Y
             → X ≡ Y
#S-injective refl = refl

↑ty-ε-≤ : #S X ε A'
        → A ↑ty k ⇘ A'
        → k #≤ X
        → X ε A
↑ty-ε-≤ {X = X} {k = k} ε-var upA lt rewrite sym (punchIn-≤ lt) = helper lt refl upA
  where helper' : ∀ {X k Y}
                → ‶ (punchIn k X) ≡ ‶ (punchIn k Y)
                → X ≡ Y
        helper' {X = X} {k = k} {Y = Y} eq = punchIn-injective k X Y (‶-injective eq)
        helper : ∀ {varY}
               → k #≤ X
               → varY ≡ ‶ punchIn k X
               → A ↑ty k ⇘ varY
               → X ε A
        helper lt eq ↑ty-var rewrite helper' eq = ε-var
↑ty-ε-≤ (ε-arr-l inA') (↑ty-arr upA upA₁) lt = ε-arr-l (↑ty-ε-≤ inA' upA lt)
↑ty-ε-≤ (ε-arr-r inA') (↑ty-arr upA upA₁) lt = ε-arr-r (↑ty-ε-≤ inA' upA₁ lt)
↑ty-ε-≤ (ε-∀ inA') (↑ty-∀ upA) lt = ε-∀ (↑ty-ε-≤ inA' upA (s≤s lt))

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

∙∈-:=∈-false :
    Γ ∋∙ X
  → Γ ∋ X := A
  → ⊥
∙∈-:=∈-false (S, inΓ) (S, inΓ') = ∙∈-:=∈-false inΓ inΓ'
∙∈-:=∈-false (S∙ inΓ) (S∙ inΓ' up) = ∙∈-:=∈-false inΓ inΓ'
∙∈-:=∈-false (S= inΓ) (S= inΓ' up) = ∙∈-:=∈-false inΓ inΓ'
∙∈-:=∈-false (S^ inΓ) (S^ inΓ' up) = ∙∈-:=∈-false inΓ inΓ'

----------------------------------------------------------------------
--+                           in a type                            +--
----------------------------------------------------------------------

ε-shifted-false : Shifted A k
                → k ε A
                → ⊥
ε-shifted-false (sfd-var x) ε-var = x refl
ε-shifted-false (sfd-arr sd sd₁) (ε-arr-l inT) = ε-shifted-false sd inT
ε-shifted-false (sfd-arr sd sd₁) (ε-arr-r inT) = ε-shifted-false sd₁ inT
ε-shifted-false (sfd-∀ sd) (ε-∀ inT) = ε-shifted-false sd inT

↑ty-ε-false : A ↑ty k ⇘ A'
            → k ε A'
            → ⊥
↑ty-ε-false upA inA = ε-shifted-false (↑ty-shifted upA) inA

punchIn-≢ : k₁ ≢ k₂
          → punchIn k k₁ ≢ punchIn k k₂
punchIn-≢ {k₁ = k₁} {k₂} {#0} neq refl = neq refl
punchIn-≢ {k₁ = #0} {#0} {#S k} neq peq = neq refl
punchIn-≢ {k₁ = #S k₁} {#S k₂} {#S k} neq peq = punchIn-≢ (≢-pred neq) (#S-injective peq)


shifted-lt : Shifted T k₁
           → T ↑ty k₂ ⇘ T'
           → k₂ #≤ k₁
           → Shifted T' (#S k₁)
shifted-lt sfd-int ↑ty-int lt = sfd-int
shifted-lt (sfd-var x) ↑ty-var lt rewrite sym (punchIn-≤ lt) = sfd-var (punchIn-≢ x)
shifted-lt (sfd-arr sd sd₁) (↑ty-arr upT upT₁) lt = sfd-arr (shifted-lt sd upT lt) (shifted-lt sd₁ upT₁ lt)
shifted-lt (sfd-∀ sd) (↑ty-∀ upT) lt = sfd-∀ (shifted-lt sd upT (s≤s lt))

ε-var-neg : ¬ (k ε ‶ X)
          → X ≢ k
ε-var-neg noin refl = noin ε-var
