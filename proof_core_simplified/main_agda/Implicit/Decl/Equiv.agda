module Implicit.Decl.Equiv where

open import Implicit.Language.All
open import Implicit.Decl.Subtyping
open import Implicit.Decl.SubtypingV2
open import Implicit.Decl.AuxLemmas


⊢d→⊢d² : Γ ⊢d j # A ≤ B
      → Γ ⊢d² j # A ≤ B
⊢d→⊢d² (s-refl regΔ cloA) = s-refl regΔ cloA
⊢d→⊢d² (s-int regΔ) = s-int regΔ
⊢d→⊢d² (s-var-∙ regΔ inΔ) = s-var-∙ regΔ inΔ
⊢d→⊢d² (s-arr₁ s s₁) = s-arr₁ (⊢d→⊢d² s) (⊢d→⊢d² s₁)
⊢d→⊢d² (s-arr₂ s s₁) = s-arr₂ (⊢d→⊢d² s) (⊢d→⊢d² s₁)
⊢d→⊢d² (s-arr₃ regA s) = s-arr₃ regA (⊢d→⊢d² s)
⊢d→⊢d² (s-∀ s) = s-∀ (⊢d→⊢d² s)
⊢d→⊢d² (s-∀l {B = B} {A* = A*} {C = C} {D = D} regB st s ic fd)
  with ⟨ C' , upC ⟩ ← ↑ty0-total C
  with ⟨ D' , upD ⟩ ← ↑ty0-total D
  with ⟨ A*' , upA* ⟩ ← ↑ty0-total A*
  with regA* ← s1-⊢r-l s
  with regA ← st-⊢r'' regA* ▶Z regB st
  = s-∀l {B = B} {A% = A*'} (st-↑ty-≫0 st regA* upA* regB) regA (s2-weaken=0 (⊢d→⊢d² s) upA* (↑ty-arr upC upD) regB) ic fd upC upD
⊢d→⊢d² (s-∀l-no-appear {B = B} {A* = A*} {j = j} {C = C} {D = D} regB st s ic fd)
  with ⟨ C' , upC ⟩ ← ↑ty0-total C
  with ⟨ D' , upD ⟩ ← ↑ty0-total D
  with ⟨ A*' , upA* ⟩ ← ↑ty0-total A*
  with regA* ← s1-⊢r-l s
  with regA ← st-⊢r'' regA* ▶Z regB st
  = s-∀l-no-appear (≫-weaken^ {k = #0} (⊢r-≫-eq regA*) ▶Z (st-↑ty fd st) upA*) regA (s2-weaken^0 (⊢d→⊢d² s) upA* (↑ty-arr upC upD)) ic fd upC upD

⊢d²→⊢d : Γ ⊢d² j # A ≤ B
         → Γ ⊢d j # A ≤ B
⊢d²→⊢d (s-refl regΔ cloA) = s-refl regΔ cloA
⊢d²→⊢d (s-int regΔ) = s-int regΔ
⊢d²→⊢d (s-var-∙ regΔ inΔ) = s-var-∙ regΔ inΔ
⊢d²→⊢d (s-arr₁ s s₁) = s-arr₁ (⊢d²→⊢d s) (⊢d²→⊢d s₁)
⊢d²→⊢d (s-arr₂ s s₁) = s-arr₂ (⊢d²→⊢d s) (⊢d²→⊢d s₁)
⊢d²→⊢d (s-arr₃ regA s) = s-arr₃ regA (⊢d²→⊢d s)
⊢d²→⊢d (s-∀ s) = s-∀ (⊢d²→⊢d s)
⊢d²→⊢d (s-∀l {B = B} grd regA s ic fd upC upD)
  with reg-S= r regA₁ ← s2-sregular s
  with ⟨ preA% , upp ⟩ ← ↑ty-surjective (⊢r-¬ε (s2-⊢r-l s) Z)
  = s-∀l regA₁ (≫-↑ty-st'0 regA regA₁ grd upp) (s1-strengthen=0 (⊢d²→⊢d s) upp (↑ty-arr upC upD)) ic fd
⊢d²→⊢d (s-∀l-no-appear grd regA s ic fd upC upD)
  with reg-S^ r ← s2-sregular s
  with ⟨ preA% , upp ⟩ ← ↑ty-surjective (⊢r-¬ε-^ (s2-⊢r-l s) Z)
  with ⟨ preA , upA ⟩ ← ↑ty-surjective fd
  with refl ← ⊢r-≫-eq' (⊢r-weaken^0 (⊢r-strengthen∙0 regA upA) upA) grd
  = s-∀l-no-appear ⊢r-int (↑ty-st upp) (s1-strengthen^0 (⊢d²→⊢d s) upp (↑ty-arr upC upD)) ic fd
