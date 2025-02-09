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



εᵍ-false : Γ ∋ X := A
         → k ε A
         → k ¬εᵍ Γ
         → ⊥
εᵍ-false (Z up) inA (Z= x x₁) with ↑ty-unique up x
... | refl = x₁ inA
εᵍ-false (Z up) inA (S= ninΓ x x₁) with ↑ty-unique up x
... | refl = x₁ inA
εᵍ-false (S, inΓ) inA (S, x ninΓ) = εᵍ-false inΓ inA ninΓ
εᵍ-false (S∙ inΓ up) inA Z∙ = ↑ty-ε-false up inA
εᵍ-false (S∙ inΓ up) inA (S∙ ninΓ) = εᵍ-false inΓ (↑ty-ε-≤ inA up z≤n) ninΓ
εᵍ-false (S^ inΓ up) inA Z^ = ↑ty-ε-false up inA
εᵍ-false (S^ inΓ up) inA (S^ ninΓ) = εᵍ-false inΓ (↑ty-ε-≤ inA up z≤n) ninΓ
εᵍ-false (S= inΓ up) inA (Z= x x₁) = ↑ty-ε-false up inA
εᵍ-false (S= inΓ up) inA (S= ninΓ x x₁) = εᵍ-false inΓ (↑ty-ε-≤ inA up z≤n) ninΓ

¬ε-shifted : ¬ (k ε A)
           → Shifted A k
¬ε-shifted {A = Int} nin = sfd-int
¬ε-shifted {A = ‶ X} nin = sfd-var (helper nin)
  where helper : ¬ (k ε ‶ X)
               →  X ≢ k
        helper nin refl = nin ε-var
¬ε-shifted {A = A `→ A₁} nin = sfd-arr (¬ε-shifted (λ z → nin (ε-arr-l z)))
                                       (¬ε-shifted (λ z → nin (ε-arr-r z)))
¬ε-shifted {A = `∀ A} nin = sfd-∀ (¬ε-shifted (λ z → nin (ε-∀ z)))

εᵍ-shifted : k ¬εᵍ Γ
           → Γ ∋ X := A
           → Shifted A k
εᵍ-shifted ninΓ inΓ = ¬ε-shifted (λ x → εᵍ-false inΓ x ninΓ)
