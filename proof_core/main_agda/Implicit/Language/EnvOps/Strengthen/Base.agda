module Implicit.Language.EnvOps.Strengthen.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All

-- remove solution entry, without doing subst
infix 3 _◀_⇘_
data _◀_⇘_ : Env n (1 + m) → Fin (1 + m) → Env n m → Set where
  ◀Z^  : Γ ,^ ◀ #0 ⇘ Γ
  ◀Z=  : Γ ,= T ◀ #0 ⇘ Γ
  ◀Z∙  : Γ ,∙ ◀ #0 ⇘ Γ
  ◀S, : Γ ◀ k ⇘ Γ'
      → (up : B ↑ty k ⇘ B')
      → Γ , B' ◀ k ⇘ Γ' , B
  ◀S^ : Γ ◀ k ⇘ Γ'
      → Γ ,^ ◀ #S k ⇘ Γ' ,^
  ◀S∙ : Γ ◀ k ⇘ Γ'
      → Γ ,∙ ◀ #S k ⇘ Γ' ,∙
  ◀S= : Γ ◀ k ⇘ Γ'
      → A ↑ty k ⇘ A'
      → Γ ,= A' ◀ #S k ⇘ Γ' ,= A
  ◀S⋈ : Γ ◀ k ⇘ Γ'
      → Γ ⋈ ◀ k ⇘ Γ' ⋈



-- ∋:=-strengthen=' : Γ ∋ punchIn k X := A'
--         → Γ ◀ k ⇘ Γ'
--         → Γ' ∋ X := A
--         → A ↑ty k ⇘ A'
-- ∋:=-strengthen=' {k = #0} {#0} (S= (Z up₂) up) ◀Z (Z up₁) with ↑ty-unique up₁ up₂
-- ... | refl = up
-- ∋:=-strengthen=' {k = #0} {#S X} (S= inΓ up) ◀Z inΓ' with ∋:=-unique inΓ inΓ'
-- ... | refl = up
-- ∋:=-strengthen=' {k = #S k} {#0} (Z up) (◀S= newΓ x) (Z up₁) = ↑ty-comm' z≤n x up up₁
-- ∋:=-strengthen=' {k = #S k} {#S X} (S∙ inΓ up) (◀S∙ newΓ) (S∙ inΓ' up₁) = ↑ty-comm' z≤n (∋:=-strengthen=' inΓ newΓ inΓ') up up₁
-- ∋:=-strengthen=' {k = #S k} {#S X} (S^ inΓ up) (◀S^ newΓ) (S^ inΓ' up₁) = ↑ty-comm' z≤n (∋:=-strengthen=' inΓ newΓ inΓ') up up₁
-- ∋:=-strengthen=' {k = #S k} {#S X} (S= inΓ up) (◀S= newΓ x) (S= inΓ' up₁) = ↑ty-comm' z≤n (∋:=-strengthen=' inΓ newΓ inΓ') up up₁
-- ∋:=-strengthen=' {k = #0} {#0} (S= (S, x₁) up) ◀Z (S, inΓ') with refl ← ∋:=-unique x₁ inΓ' = up
-- ∋:=-strengthen=' (S, inΓ) (◀S, new up) (S, inΓ') = ∋:=-strengthen=' inΓ new inΓ'
-- ∋:=-strengthen=' (S⋈ inΓ) (◀S⋈ new) (S⋈ inΓ') = ∋:=-strengthen=' inΓ new inΓ'
-- ∋:=-strengthen=' {k = #0} {#0} {Γ' = Γ' ⋈} (S= (S⋈ x₁) up) ◀Z (S⋈ x) = ∋:=-strengthen=' (S= x₁ up) ◀Z x

-- ⊢r-¬ε : Γ ⊢r A
--         → Γ ∋= k
--         → k ¬ε A
-- ⊢r-¬ε ⊢r-int inΓ = ¬ε-int
-- ⊢r-¬ε (⊢r-var-∙ inΓ₁) inΓ = ¬ε-var (∋∙-∋=-≢ inΓ₁ inΓ)
-- ⊢r-¬ε (⊢r-arr regA regA₁) inΓ = ¬ε-arr (⊢r-¬ε regA inΓ) (⊢r-¬ε regA₁ inΓ)
-- ⊢r-¬ε (⊢r-∀ regA) inΓ = ¬ε-∀ (⊢r-¬ε regA (S∙ inΓ))

-- ∋:=-strengthen=-reg : Regular Γ
--                     → Γ ∋ punchIn k X := A'
--                     → Γ ◀ k ⇘ Γ'
--                     → A ↑ty k ⇘ A'
--                     → Γ' ∋ X := A
-- ∋:=-strengthen=-reg {k = #0} {X = #0} (reg-S= regΓ regA) (S= inΓ up) ◀Z upA with refl ← ↑ty-unique-inver up upA = inΓ
-- ∋:=-strengthen=-reg {k = #0} {X = #S X} (reg-S= regΓ regA) (S= inΓ up) ◀Z upA with refl ← ↑ty-unique-inver up upA = inΓ
-- ∋:=-strengthen=-reg {k = #S k} {X = #S X} (reg-S∙ regΓ) (S∙ inΓ up) (◀S∙ newΓ) upA
-- --  with ¬inA ← ⊢r-¬ε (∋:=-⊢r regΓ inΓ) (◀=-∋= newΓ)
-- --  with ⟨ preA , pupA ⟩ ← ↑ty-surjective ¬inA
--   = ?
--   -- S∙ (∋:=-strengthen=-reg regΓ inΓ newΓ pupA) (↑ty-comm1 upA up pupA)
-- ∋:=-strengthen=-reg {k = #S k} {X = #S X} (reg-S^ regΓ) (S^ inΓ up) (◀S^ newΓ) upA
-- --  with ¬inA ← ⊢r-¬ε (∋:=-⊢r regΓ inΓ) (◀=-∋= newΓ)
-- --  with ⟨ preA , pupA ⟩ ← ↑ty-surjective ¬inA
--   = ?
-- -- S^ (∋:=-strengthen=-reg regΓ inΓ newΓ pupA) (↑ty-comm1 upA up pupA)
-- ∋:=-strengthen=-reg {k = #S k} {X = #0} (reg-S= regΓ regA) (Z up) (◀S= newΓ x) upA = Z (↑ty-comm1 upA up x)
-- ∋:=-strengthen=-reg {k = #S k} {X = #S X} (reg-S= regΓ regA) (S= inΓ up) (◀S= newΓ x) upA
-- --  with ¬inA ← ⊢r-¬ε (∋:=-⊢r regΓ inΓ) (◀=-∋= newΓ)
-- --  with ⟨ preA , pupA ⟩ ← ↑ty-surjective ¬inA
--   = ?
-- -- S= (∋:=-strengthen=-reg regΓ inΓ newΓ pupA) (↑ty-comm1 upA up pupA)
-- ∋:=-strengthen=-reg (reg-S⋈ regΓ) (S⋈ inΓ) (◀S⋈ new) upA = S⋈ {!!}
-- ∋:=-strengthen=-reg (reg-S, regΓ regA) inΓ new upA = {!!}

-- -- this is the standard way to prove
-- ∋:=-strengthen= : Γ ∋ punchIn k X := A'
--                  → k ¬εᵍ Γ
--                  → Γ ◀ k ⇘ Γ'
--                  → A ↑ty k ⇘ A'
--                  → Γ' ∋ X := A
-- ∋:=-strengthen= {k = #0} {X = #0} (S= inΓ up) (Z= upA₁ ¬inA) ◀Z upA with refl ← ↑ty-unique-inver up upA = inΓ
-- ∋:=-strengthen= {k = #0} {X = #S X} (S= inΓ up) (Z= upA₁ ¬inA) ◀Z upA with refl ← ↑ty-unique-inver up upA = inΓ
-- ∋:=-strengthen= {k = #S k} {X = #0} (Z up) (S= ninΓ upA₁ ¬inA) (◀S= upΓ x) upA with refl ← ↑ty-unique upA₁ up = Z (↑ty-comm1 upA up x)
-- ∋:=-strengthen= {k = #S k} {X = #S X} (S∙ inΓ up) (S∙ ninΓ) (◀S∙ upΓ) upA
--   with k¬inA ← εᵍ-:=-¬ε ninΓ inΓ
--   with ⟨ preA , uptoA ⟩ ← ↑ty-surjective k¬inA = S∙ (∋:=-strengthen= inΓ ninΓ upΓ uptoA) (↑ty-comm1 upA up uptoA)
-- ∋:=-strengthen= {k = #S k} {X = #S X} (S^ inΓ up) (S^ ninΓ) (◀S^ upΓ) upA
--   with k¬inA ← εᵍ-:=-¬ε ninΓ inΓ
--   with ⟨ preA , uptoA ⟩ ← ↑ty-surjective k¬inA = S^ (∋:=-strengthen= inΓ ninΓ upΓ uptoA) (↑ty-comm1 upA up uptoA)
-- ∋:=-strengthen= {k = #S k} {X = #S X} (S= inΓ up) (S= ninΓ upA₁ ¬inA) (◀S= upΓ x) upA
--   with k¬inA ← εᵍ-:=-¬ε ninΓ inΓ
--   with ⟨ preA , uptoA ⟩ ← ↑ty-surjective k¬inA = S= (∋:=-strengthen= inΓ ninΓ upΓ uptoA) (↑ty-comm1 upA up uptoA)
-- ∋:=-strengthen= {Γ = Γ , A} {k = k} {X = X} (S, inΓ) (S, x ¬inA) (◀S, new up) upA = S, (∋:=-strengthen= inΓ ¬inA new upA)


-- ⊢r-strengthen= : Γ ⊢r A'
--                → Γ ◀ k ⇘ Γ'
--                → A ↑ty k ⇘ A'
--                → Γ' ⊢r A
-- ⊢r-strengthen= ⊢r-int newΓ ↑ty-int = ⊢r-int
-- ⊢r-strengthen= (⊢r-var-∙ inΓ) newΓ ↑ty-var = ⊢r-var-∙ (∋∙-strengthen= inΓ newΓ)
-- ⊢r-strengthen= (⊢r-arr regA regA₁) newΓ (↑ty-arr upA upA₁) = ⊢r-arr (⊢r-strengthen= regA newΓ upA)
--                                                                     (⊢r-strengthen= regA₁ newΓ upA₁)
-- ⊢r-strengthen= (⊢r-∀ regA) newΓ (↑ty-∀ upA) = ⊢r-∀ (⊢r-strengthen= regA (◀S∙ newΓ) upA)

-- ⊢r-strengthen=0 : Γ ,= T ⊢r A'
--                   → ↑ty0 A ⇘ A'
--                   → Γ ⊢r A
-- ⊢r-strengthen=0 regA upA = ⊢r-strengthen= regA ? upA


-- ⊢c-strengthen= : Γ ⊢c A'
--                → Γ ◀ k ⇘ Γ'
--                → A ↑ty k ⇘ A'
--                → Γ' ⊢c A
-- ⊢c-strengthen= ⊢c-int newΓ ↑ty-int = ⊢c-int
-- ⊢c-strengthen= (⊢c-var-∙ inΔ) newΓ ↑ty-var = ⊢c-var-∙ (∋∙-strengthen= inΔ newΓ)
-- ⊢c-strengthen= (⊢c-var-= inΔ) newΓ ↑ty-var = ⊢c-var-= (∋=-strengthen= inΔ newΓ)
-- ⊢c-strengthen= (⊢c-arr cloA cloA₁) newΓ (↑ty-arr upA upA₁) = ⊢c-arr (⊢c-strengthen= cloA newΓ upA)
--                                                                     (⊢c-strengthen= cloA₁ newΓ upA₁)
-- ⊢c-strengthen= (⊢c-∀ cloA) newΓ (↑ty-∀ upA) = ⊢c-∀ (⊢c-strengthen= cloA (◀S∙ newΓ) upA)

-- ⊢o-strengthen= : Γ ⊢o A'
--                → Γ ◀ k ⇘ Γ'
--                → A ↑ty k ⇘ A'
--                → Γ' ⊢o A
-- ⊢o-strengthen= (⊢o-var-^ x) newΓ ↑ty-var = ⊢o-var-^ (∋^-strengthen= x newΓ)
-- ⊢o-strengthen= (⊢o-arr-l opnA) newΓ (↑ty-arr upA upA₁) = ⊢o-arr-l (⊢o-strengthen= opnA newΓ upA)
-- ⊢o-strengthen= (⊢o-arr-r opnA) newΓ (↑ty-arr upA upA₁) = ⊢o-arr-r (⊢o-strengthen= opnA newΓ upA₁)
-- ⊢o-strengthen= (⊢o-∀ opnA) newΓ (↑ty-∀ upA) = ⊢o-∀ (⊢o-strengthen= opnA (◀S∙ newΓ) upA)

-- tregular-strengthen= : TRegular Γ
--                      → Γ ◀ k ⇘ Γ'
--                      → TRegular Γ'
-- tregular-strengthen= (reg-S, regΓ regA) (◀S, newΓ x) = reg-S, (tregular-strengthen= regΓ newΓ) (⊢r-strengthen= regA newΓ x)
-- tregular-strengthen= (reg-S∙ regΓ) (◀S∙ newΓ) = reg-S∙ (tregular-strengthen= regΓ newΓ)
-- tregular-strengthen= (reg-S^ regΓ) (◀S^ newΓ) = reg-S^ (tregular-strengthen= regΓ newΓ)
-- tregular-strengthen= (reg-S= regΓ regA) ◀Z = regΓ
-- tregular-strengthen= (reg-S= regΓ regA) (◀S= newΓ x) = reg-S= (tregular-strengthen= regΓ newΓ) (⊢r-strengthen= regA newΓ x)

-- sregular-strengthen= : SRegular Γ
--                      → Γ ◀ k ⇘ Γ'
--                      → SRegular Γ'
-- sregular-strengthen= (reg-Z regΓ) (◀S⋈ newΓ) = reg-Z (tregular-strengthen= regΓ newΓ)
-- sregular-strengthen= (reg-S∙ sreg) (◀S∙ newΓ) = reg-S∙ (sregular-strengthen= sreg newΓ)
-- sregular-strengthen= (reg-S^ sreg) (◀S^ newΓ) = reg-S^ (sregular-strengthen= sreg newΓ)
-- sregular-strengthen= (reg-S= sreg regA) ◀Z = sreg
-- sregular-strengthen= (reg-S= sreg regA) (◀S= newΓ x) = reg-S= (sregular-strengthen= sreg newΓ) (⊢r-strengthen= regA newΓ x)


-- ≫-strengthen= : Γ ≫ A' ⇘ B'
--               → Regular Γ
--               → Γ ◀ k ⇘ Γ'
--               → A ↑ty k ⇘ A'
--               → B ↑ty k ⇘ B'
--               → Γ' ≫ A ⇘ B
-- ≫-strengthen= grd-int regΓ newΓ ↑ty-int ↑ty-int = grd-int
-- ≫-strengthen= (grd-var= x) regΓ newΓ ↑ty-var upB = grd-var= (∋:=-strengthen=-reg regΓ x newΓ upB)
-- ≫-strengthen= (grd-var∙ x) regΓ newΓ (↑ty-var  {X = X} {k = k}) upB with ↑ty-var-inv-helper upB refl
-- ... | refl = grd-var∙ (∋∙-strengthen= x newΓ)
-- ≫-strengthen= (grd-arr grd grd₁) regΓ newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = grd-arr (≫-strengthen= grd regΓ newΓ upA upB)
--                                                                                            (≫-strengthen= grd₁ regΓ newΓ upA₁ upB₁)
-- ≫-strengthen= (grd-∀ grd) regΓ newΓ (↑ty-∀ upA) (↑ty-∀ upB) = grd-∀ (≫-strengthen= grd (reg-S∙ regΓ) (◀S∙ newΓ) upA upB)


-- ≫-strengthen=0 : Γ ,= T ≫ A' ⇘ B'
--                → Regular Γ
--                → Γ ⊢r T
--                → ↑ty0 A ⇘ A'
--                → ↑ty0 B ⇘ B'
--                → Γ ≫ A ⇘ B
-- ≫-strengthen=0 grd regΓ regT upA upB = ≫-strengthen= grd (reg-S= regΓ regT) ? upA upB


-- -- aux lemmas
-- ⊢r-◀=-↑ty-surjective : Γ ⊢r A
--                     → Γ ◀ k ⇘ Γ'
--                     → ∃[ pA ](pA ↑ty k ⇘ A)
-- ⊢r-◀=-↑ty-surjective regA newΓ = ↑ty-surjective (⊢r-¬ε regA ?)


