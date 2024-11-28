module Implicit.Decl.Properties where

open import Implicit.Language
open import Implicit.Decl.Base

⊢sub' : ∀ {Γ : Env n m} {e A B j}
  → Γ ⊢ Z # e ⦂ B
  → Γ ⊢ j # B ≤ A
  → Γ ⊢ j # e ⦂ A
⊢sub' {j = Z} ⊢e s-refl = ⊢e
⊢sub' {j = ∞} ⊢e s = ⊢sub ⊢e s nz-∞
⊢sub' {j = 𝕚 j} ⊢e s = ⊢sub ⊢e s nz-I
⊢sub' {j = 𝕔 j} ⊢e s = ⊢sub ⊢e s nz-C


-- the needed lemmas
-- will do later
postulate
  strengthen-0 : ∀ {Γ : Env n m} {j A B e}
    → Γ , A ⊢ j # ↑tm0 e ⦂ B
    → Γ ⊢ j # e ⦂ B

  -- s-strengthen-tm-0 : ∀ {Γ : Env n m} {A B C j}
  --   → Γ , A ⊢ j # B ≤ C
  --   → Γ ⊢ j # B ≤ C

----------------------------------------------------------------------
--+                           Weakening                            +--
----------------------------------------------------------------------

s-weaken : ∀ {Γ : Env (1 + n) m} {k j A B }
  → Γ /,/ k ⊢ j # A ≤ B
  → Γ ⊢ j # A ≤ B
s-weaken (s-refl) = s-refl
s-weaken s-int = s-int
s-weaken s-var = s-var
s-weaken (s-arr₁ C≤A B≤D) = s-arr₁ (s-weaken C≤A) (s-weaken B≤D)
s-weaken (s-arr₂ C≤A B≤D) = s-arr₂ (s-weaken C≤A) (s-weaken B≤D)
s-weaken (s-arr₃ B≤D) = s-arr₃ (s-weaken B≤D)
s-weaken (s-∀ A≤B) = s-∀ (s-weaken A≤B)
s-weaken (s-∀l A≤B have-i fd st1 st2) = s-∀l (s-weaken A≤B) have-i fd st1 st2
s-weaken (s-var-l x A≤B) = s-var-l (∋,-weaken-sol x) (s-weaken A≤B)
s-weaken (s-var-r x A≤B) = s-var-r (∋,-weaken-sol x) (s-weaken A≤B)

postulate
  weaken : ∀ {Γ : Env (1 + n) m} {k j e A}
    → Γ /,/ k ⊢ j # e ⦂ A
    → Γ ⊢ j # ↑tm k e ⦂ A

  s-strengthen-tm-0 : ∀ {Γ : Env n m} {A B C j}
    → Γ , A ⊢ j # B ≤ C
    → Γ ⊢ j # B ≤ C
  
weaken-0 : ∀ {Γ : Env (1 + n) m} {j e A}
  → Γ ⊢ j # e ⦂ A
  → Γ , A ⊢ j # ↑tm0 e ⦂ A
weaken-0 {Γ = Γ} {A = A} ⊢e = weaken {Γ = Γ , A} {k = #0} ⊢e

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------
{-
s-trans : ∀ {Γ : Env n m} {A B C j}
  → Γ ⊢ j # A ≤ B
  → Γ ⊢ j # B ≤ C
  → Γ ⊢ j # A ≤ C
s-trans {B = Int} (s-refl ap) s2 = {!!}
s-trans {B = Int} s-int s2 = {!!}
s-trans {B = Int} (s-∀l s1) s2 = {!!}
s-trans {B = Int} (s-∀lτ s1) s2 = {!!}
s-trans {B = Int} (s-var-l x s1) s2 = {!!}

s-trans {B = ‶ X} s1 s2 = {!!}
s-trans {B = B `→ B₁} s1 s2 = {!!}
s-trans {B = `∀ B} s1 s2 = {!!}
-}

s-refl-∞ : ∀ {Γ : Env n m} {A}
  → Γ ⊢ ∞ # A ≤ A
s-refl-∞ {A = Int} = s-int
s-refl-∞ {A = ‶ X} = s-var
s-refl-∞ {A = A `→ A₁} = s-arr₁ s-refl-∞ s-refl-∞
s-refl-∞ {A = `∀ A} = s-∀ s-refl-∞
