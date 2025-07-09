module Implicit.Language.EnvOps.RemoveEVar where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.All
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Ground.Base
open import Implicit.Language.Occur.All

open import Implicit.Language.EnvOps.Regular

-- remove exsitential variable â from k-th posititon
infix 3 _◀_^⇘_
data _◀_^⇘_ : Env n (1 + m) → Fin (1 + m) → Env n m → Set where
  ◀Z  : Γ ,^ ◀ #0 ^⇘ Γ
  ◀S, : Γ ◀ k ^⇘ Γ'
      → B ↑ty k ⇘ B'
      → Γ , B' ◀ k ^⇘ Γ' , B
  ◀S^ : Γ ◀ k ^⇘ Γ'
      → Γ ,^ ◀ #S k ^⇘ Γ' ,^
  ◀S∙ : Γ ◀ k ^⇘ Γ'
      → Γ ,∙ ◀ #S k ^⇘ Γ' ,∙
  ◀S= : Γ ◀ k ^⇘ Γ'
      → A ↑ty k ⇘ A'
      → Γ ,= A' ◀ #S k ^⇘ Γ' ,= A
  ◀S⋈ : Γ ◀ k ^⇘ Γ'
      → Γ ⋈ ◀ k ^⇘ Γ' ⋈

infix 3 _∋^'_
data _∋^'_ : Env n m → Fin m → Set where
  Z  : Δ ,^ ∋^' #0
  S∙ : Δ ∋^' k
     → Δ ,∙ ∋^' #S k
  S^ : Δ ∋^' k
     → Δ ,^ ∋^' #S k
  S= : Δ ∋^' k
     → Δ ,= B ∋^' #S k
  S, : Δ ∋^' k
     → Δ , A ∋^' k
  S⋈ : Δ ∋^' k
     → Δ ⋈ ∋^' k

◀^-∋^' : Γ ◀ k ^⇘ Γ'
      → Γ ∋^' k
◀^-∋^' ◀Z = Z
◀^-∋^' (◀S, new x) = S, (◀^-∋^' new)
◀^-∋^' (◀S^ new) = S^ (◀^-∋^' new)
◀^-∋^' (◀S∙ new) = S∙ (◀^-∋^' new)
◀^-∋^' (◀S= new x) = S= (◀^-∋^' new)
◀^-∋^' (◀S⋈ new) = S⋈ (◀^-∋^' new)


∋∙-strengthen^ : Γ ∋∙ punchIn k X
      → Γ ◀ k ^⇘ Γ'
      → Γ' ∋∙ X
∋∙-strengthen^ {k = #0} (S, inΓ) (◀S, newΓ x) = S, (∋∙-strengthen^ inΓ newΓ)
∋∙-strengthen^ {k = #0} (S^ inΓ) ◀Z = inΓ
∋∙-strengthen^ {k = #S k} {#0} Z (◀S∙ newΓ) = Z
∋∙-strengthen^ {k = #S k} {#0} (S, inΓ) (◀S, newΓ x) = S, (∋∙-strengthen^ inΓ newΓ)
∋∙-strengthen^ {k = #S k} {#S X} (S, inΓ) (◀S, newΓ x) = S, (∋∙-strengthen^ inΓ newΓ)
∋∙-strengthen^ {k = #S k} {#S X} (S∙ inΓ) (◀S∙ newΓ) = S∙ (∋∙-strengthen^ inΓ newΓ)
∋∙-strengthen^ {k = #S k} {#S X} (S= inΓ) (◀S= newΓ x) = S= (∋∙-strengthen^ inΓ newΓ)
∋∙-strengthen^ {k = #S k} {#S X} (S^ inΓ) (◀S^ newΓ) = S^ (∋∙-strengthen^ inΓ newΓ)
∋∙-strengthen^ (S⋈ inΓ) (◀S⋈ newΓ) = S⋈ (∋∙-strengthen^ inΓ newΓ)


∋^-strengthen^ : Γ ∋^ punchIn k X
      → Γ ◀ k ^⇘ Γ'
      → Γ' ∋^ X
∋^-strengthen^ {k = #0} (S, inΓ) (◀S, newΓ x) = S, (∋^-strengthen^ inΓ newΓ)
∋^-strengthen^ {k = #0} (S^ inΓ) ◀Z = inΓ
∋^-strengthen^ {k = #S k} {#0} Z (◀S^ newΓ) = Z
∋^-strengthen^ {k = #S k} {#0} (S, inΓ) (◀S, newΓ x) = S, (∋^-strengthen^ inΓ newΓ)
∋^-strengthen^ {k = #S k} {#S X} (S, inΓ) (◀S, newΓ x) = S, (∋^-strengthen^ inΓ newΓ)
∋^-strengthen^ {k = #S k} {#S X} (S∙ inΓ) (◀S∙ newΓ) = S∙ (∋^-strengthen^ inΓ newΓ)
∋^-strengthen^ {k = #S k} {#S X} (S= inΓ) (◀S= newΓ x) = S= (∋^-strengthen^ inΓ newΓ)
∋^-strengthen^ {k = #S k} {#S X} (S^ inΓ) (◀S^ newΓ) = S^ (∋^-strengthen^ inΓ newΓ)
-- ∋^-strengthen^ (S⋈ inΓ) (◀S⋈ newΓ) = S⋈ (∋^-strengthen^ inΓ newΓ)

∋=-strengthen^ : Γ ∋= punchIn k X
      → Γ ◀ k ^⇘ Γ'
      → Γ' ∋= X
∋=-strengthen^ {k = #0} (S, inΓ) (◀S, newΓ x) = S, (∋=-strengthen^ inΓ newΓ)
∋=-strengthen^ {k = #0} (S^ inΓ) ◀Z = inΓ
∋=-strengthen^ {k = #S k} {#0} Z (◀S= inΓ x) = Z
∋=-strengthen^ {k = #S k} {#0} (S, inΓ) (◀S, newΓ x) = S, (∋=-strengthen^ inΓ newΓ)
∋=-strengthen^ {k = #S k} {#S X} (S, inΓ) (◀S, newΓ x) = S, (∋=-strengthen^ inΓ newΓ)
∋=-strengthen^ {k = #S k} {#S X} (S∙ inΓ) (◀S∙ newΓ) = S∙ (∋=-strengthen^ inΓ newΓ)
∋=-strengthen^ {k = #S k} {#S X} (S= inΓ) (◀S= newΓ x) = S= (∋=-strengthen^ inΓ newΓ)
∋=-strengthen^ {k = #S k} {#S X} (S^ inΓ) (◀S^ newΓ) = S^ (∋=-strengthen^ inΓ newΓ)

⊢r-strengthen^ : Γ ⊢r A'
               → Γ ◀ k ^⇘ Γ'
               → A ↑ty k ⇘ A'
               → Γ' ⊢r A
⊢r-strengthen^ ⊢r-int new ↑ty-int = ⊢r-int
⊢r-strengthen^ ⊢r-top new ↑ty-top = ⊢r-top
⊢r-strengthen^ ⊢r-bot new ↑ty-bot = ⊢r-bot
⊢r-strengthen^ (⊢r-var-∙ inΓ) new ↑ty-var = ⊢r-var-∙ (∋∙-strengthen^ inΓ new)
⊢r-strengthen^ (⊢r-arr regA regA₁) new (↑ty-arr upA upA₁) = ⊢r-arr (⊢r-strengthen^ regA new upA)
                                                                   (⊢r-strengthen^ regA₁ new upA₁)
⊢r-strengthen^ (⊢r-∀ regA) new (↑ty-∀ upA) = ⊢r-∀ (⊢r-strengthen^ regA (◀S∙ new) upA)


⊢r-strengthen^0 : Γ ,^ ⊢r A'
                  → ↑ty0 A ⇘ A'
                  → Γ ⊢r A
⊢r-strengthen^0 regA upA = ⊢r-strengthen^ regA ◀Z upA



tregular-strengthen^ : TRegular Γ
                     → Γ ◀ k ^⇘ Γ'
                     → TRegular Γ'
tregular-strengthen^ (reg-S, regΓ regA) (◀S, new x) = reg-S, (tregular-strengthen^ regΓ new) (⊢r-strengthen^ regA new x)
tregular-strengthen^ (reg-S∙ regΓ) (◀S∙ new) = reg-S∙ (tregular-strengthen^ regΓ new)
tregular-strengthen^ (reg-S^ regΓ) ◀Z = regΓ
tregular-strengthen^ (reg-S^ regΓ) (◀S^ new) = reg-S^ (tregular-strengthen^ regΓ new)
tregular-strengthen^ (reg-S= regΓ regA) (◀S= new x) = reg-S= (tregular-strengthen^ regΓ new) (⊢r-strengthen^ regA new x)


sregular-strengthen^ : SRegular Γ
                     → Γ ◀ k ^⇘ Γ'
                     → SRegular Γ'
sregular-strengthen^ (reg-Z regΓ) (◀S⋈ new) = reg-Z (tregular-strengthen^ regΓ new)
sregular-strengthen^ (reg-S∙ regΓ) (◀S∙ new) = reg-S∙ (sregular-strengthen^ regΓ new)
sregular-strengthen^ (reg-S^ regΓ) ◀Z = regΓ
sregular-strengthen^ (reg-S^ regΓ) (◀S^ new) = reg-S^ (sregular-strengthen^ regΓ new)
sregular-strengthen^ (reg-S= regΓ regA) (◀S= new x) = reg-S= (sregular-strengthen^ regΓ new) (⊢r-strengthen^ regA new x)


∋∙-∋^'-≢ : Γ ∋^' k
         → Γ ∋∙ X
         → X ≢ k
∋∙-∋^'-≢ Z () refl
∋∙-∋^'-≢ (S∙ in1) (S∙ in2) refl = ∋∙-∋^'-≢ in1 in2 refl
∋∙-∋^'-≢ (S^ in1) (S^ in2) refl = ∋∙-∋^'-≢ in1 in2 refl
∋∙-∋^'-≢ (S= in1) (S= in2) refl = ∋∙-∋^'-≢ in1 in2 refl
∋∙-∋^'-≢ (S, in1) (S, in2) refl = ∋∙-∋^'-≢ in1 in2 refl
∋∙-∋^'-≢ (S⋈ in1) (S⋈ in2) refl = ∋∙-∋^'-≢ in1 in2 refl

⊢r-¬ε-^ : Γ ⊢r A
        → Γ ∋^' k
        → k ¬ε A
⊢r-¬ε-^ ⊢r-int inΓ = ¬ε-int
⊢r-¬ε-^ ⊢r-top inΓ = ¬ε-top
⊢r-¬ε-^ ⊢r-bot inΓ = ¬ε-bot
⊢r-¬ε-^ (⊢r-var-∙ inΓ₁) inΓ = ¬ε-var (∋∙-∋^'-≢ inΓ inΓ₁)
⊢r-¬ε-^ (⊢r-arr regA regA₁) inΓ = ¬ε-arr (⊢r-¬ε-^ regA inΓ) (⊢r-¬ε-^ regA₁ inΓ)
⊢r-¬ε-^ (⊢r-∀ regA) inΓ = ¬ε-∀ (⊢r-¬ε-^ regA (S∙ inΓ))

-- aux lemmas
⊢r-◀^-↑ty-surjective : Γ ⊢r A
                    → Γ ◀ k ^⇘ Γ'
                    → ∃[ pA ](pA ↑ty k ⇘ A)
⊢r-◀^-↑ty-surjective regA newΓ = ↑ty-surjective (⊢r-¬ε-^ regA (◀^-∋^' newΓ))


∋:=-strengthen^-reg : SRegular Γ
                    → Γ ∋ punchIn k X := A'
                    → Γ ◀ k ^⇘ Γ'
                    → A ↑ty k ⇘ A'
                    → Γ' ∋ X := A
∋:=-strengthen^-reg {k = #0} {X = #0} (reg-S^ regΓ) (S^ inΓ up) ◀Z upA with refl ← ↑ty-unique-inver up upA = inΓ
∋:=-strengthen^-reg {k = #0} {X = #S X} (reg-S^ regΓ) (S^ inΓ up) ◀Z upA with refl ← ↑ty-unique-inver up upA = inΓ
∋:=-strengthen^-reg {k = #S k} {X = #S X} (reg-S∙ regΓ) (S∙ inΓ up) (◀S∙ newΓ) upA
  with ¬inA ← ⊢r-¬ε-^ (∋:=-⊢r regΓ inΓ) (◀^-∋^' newΓ)
  with ⟨ preA , pupA ⟩ ← ↑ty-surjective ¬inA
  = S∙ (∋:=-strengthen^-reg regΓ inΓ newΓ pupA) (↑ty-comm1 upA up pupA)
∋:=-strengthen^-reg {k = #S k} {X = #S X} (reg-S^ regΓ) (S^ inΓ up) (◀S^ newΓ) upA
  with ¬inA ← ⊢r-¬ε-^ (∋:=-⊢r regΓ inΓ) (◀^-∋^' newΓ)
  with ⟨ preA , pupA ⟩ ← ↑ty-surjective ¬inA
  = S^ (∋:=-strengthen^-reg regΓ inΓ newΓ pupA) (↑ty-comm1 upA up pupA)
∋:=-strengthen^-reg {k = #S k} {X = #0} (reg-S= regΓ regA) (Z up) (◀S= newΓ x) upA = Z (↑ty-comm1 upA up x)
∋:=-strengthen^-reg {k = #S k} {X = #S X} (reg-S= regΓ regA) (S= inΓ up) (◀S= newΓ x) upA
  with ¬inA ← ⊢r-¬ε-^ (∋:=-⊢r regΓ inΓ) (◀^-∋^' newΓ)
  with ⟨ preA , pupA ⟩ ← ↑ty-surjective ¬inA
  = S= (∋:=-strengthen^-reg regΓ inΓ newΓ pupA) (↑ty-comm1 upA up pupA)


∋⦂-strengthen^ : Γ ∋ x ⦂ A'
               → TRegular Γ
               → Γ ◀ k ^⇘ Γ'
               → A ↑ty k ⇘ A'
               → Γ' ∋ x ⦂ A
∋⦂-strengthen^ Z (reg-S, regΓ regA) (◀S, new x) upA with refl ← ↑ty-unique-inver upA x = Z
∋⦂-strengthen^ (S, inΓ) (reg-S, regΓ regA) (◀S, newΓ up) upA = S, (∋⦂-strengthen^ inΓ regΓ newΓ upA)
∋⦂-strengthen^ (S∙ inΓ up) (reg-S∙ regΓ) (◀S∙ newΓ) upA
  with regA ← ∋⦂-⊢r regΓ inΓ
  with ⟨ pA , uppA ⟩ ← ⊢r-◀^-↑ty-surjective regA newΓ = S∙ (∋⦂-strengthen^ inΓ regΓ newΓ uppA) (↑ty-comm1 upA up uppA)
∋⦂-strengthen^ (S^ inΓ up) (reg-S^ regΓ) ◀Z upA with refl ← ↑ty-unique-inver upA up = inΓ
∋⦂-strengthen^ (S^ inΓ up) (reg-S^ regΓ) (◀S^ newΓ) upA
  with regA ← ∋⦂-⊢r regΓ inΓ
  with ⟨ pA , uppA ⟩ ← ⊢r-◀^-↑ty-surjective regA newΓ = S^ (∋⦂-strengthen^ inΓ regΓ newΓ uppA) (↑ty-comm1 upA up uppA)
∋⦂-strengthen^ (S= inΓ up) (reg-S= regΓ regA) (◀S= newΓ x) upA
  with regA ← ∋⦂-⊢r regΓ inΓ
  with ⟨ pA , uppA ⟩ ← ⊢r-◀^-↑ty-surjective regA newΓ = S= (∋⦂-strengthen^ inΓ regΓ newΓ uppA) (↑ty-comm1 upA up uppA)


⊢c-strengthen^ : Γ ⊢c A'
               → Γ ◀ k ^⇘ Γ'
               → A ↑ty k ⇘ A'
               → Γ' ⊢c A
⊢c-strengthen^ ⊢c-int new ↑ty-int = ⊢c-int
⊢c-strengthen^ ⊢c-top new ↑ty-top = ⊢c-top
⊢c-strengthen^ ⊢c-bot new ↑ty-bot = ⊢c-bot
⊢c-strengthen^ (⊢c-var-∙ inΔ) new ↑ty-var = ⊢c-var-∙ (∋∙-strengthen^ inΔ new)
⊢c-strengthen^ (⊢c-var-= inΔ) new ↑ty-var = ⊢c-var-= (∋=-strengthen^ inΔ new)
⊢c-strengthen^ (⊢c-arr cloA cloA₁) new (↑ty-arr upA upA₁) = ⊢c-arr (⊢c-strengthen^ cloA new upA)
                                                             (⊢c-strengthen^ cloA₁ new upA₁)
⊢c-strengthen^ (⊢c-∀ cloA) new (↑ty-∀ upA) = ⊢c-∀ (⊢c-strengthen^ cloA (◀S∙ new) upA)


⊢o-strengthen^ : Γ ⊢o A'
               → Γ ◀ k ^⇘ Γ'
               → A ↑ty k ⇘ A'
               → Γ' ⊢o A
⊢o-strengthen^ (⊢o-var-^ x) new ↑ty-var = ⊢o-var-^ (∋^-strengthen^ x new)
⊢o-strengthen^ (⊢o-arr-l opnA) new (↑ty-arr upA upA₁) = ⊢o-arr-l (⊢o-strengthen^ opnA new upA)
⊢o-strengthen^ (⊢o-arr-r opnA) new (↑ty-arr upA upA₁) = ⊢o-arr-r (⊢o-strengthen^ opnA new upA₁)
⊢o-strengthen^ (⊢o-∀ opnA) new (↑ty-∀ upA) = ⊢o-∀ (⊢o-strengthen^ opnA (◀S∙ new) upA)

≫-strengthen^ : Γ ≫ A' ⇘ B'
              → SRegular Γ
              → Γ ◀ k ^⇘ Γ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → Γ' ≫ A ⇘ B
≫-strengthen^ grd-int regΓ newΓ ↑ty-int ↑ty-int = grd-int
≫-strengthen^ grd-top regΓ newΓ ↑ty-top ↑ty-top = grd-top
≫-strengthen^ grd-bot regΓ newΓ ↑ty-bot ↑ty-bot = grd-bot
≫-strengthen^ (grd-var= x) regΓ newΓ ↑ty-var upB = grd-var= (∋:=-strengthen^-reg regΓ x newΓ upB)
≫-strengthen^ (grd-var∙ x) regΓ newΓ (↑ty-var  {X = X} {k = k}) upB with ↑ty-var-inv-helper upB refl
... | refl = grd-var∙ (∋∙-strengthen^ x newΓ)
≫-strengthen^ (grd-arr grd grd₁) regΓ newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = grd-arr (≫-strengthen^ grd regΓ newΓ upA upB)
                                                                                           (≫-strengthen^ grd₁ regΓ newΓ upA₁ upB₁)
≫-strengthen^ (grd-∀ grd) regΓ newΓ (↑ty-∀ upA) (↑ty-∀ upB) = grd-∀ (≫-strengthen^ grd (reg-S∙ regΓ) (◀S∙ newΓ) upA upB)
