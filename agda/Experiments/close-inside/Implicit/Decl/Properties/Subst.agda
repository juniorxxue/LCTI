module Implicit.Decl.Properties.Subst where

open import Implicit.Language
open import Implicit.Decl.Base
open import Implicit.Decl.Properties.OpenClose

postulate
  s-subst : Γ ⊢ j # A ≤ B
          → Γ ◀ k := T ⇘ Γ*
          → ⟦ k / T ⟧ A ⇘ A*
          → ⟦ k / T ⟧ B ⇘ B*
          → Γ* ⊢ j # A* ≤ B*

  t-subst : Γ ⊢ j # e ⦂ A
          → Γ ◀ k := T ⇘ Γ*
          → ⟦ k / T ⟧ᵉ e ⇘ e*
          → ⟦ k / T ⟧ A ⇘ A*
          → Γ* ⊢ j # e* ⦂ A*

s-subst0 : Γ ,= T ⊢ j # A ≤ B
         → ⟦ T ⟧ A ⇘ A*
         → ⟦ T ⟧ B ⇘ B*
         → Γ ⊢ j # A* ≤ B*
s-subst0 s stA stB = s-subst s ◀Z stA stB

t-subst0 : Γ ,= T ⊢ j # e ⦂ A
         → ⟦ T ⟧ᵉ e ⇘ e*
         → ⟦ T ⟧ A ⇘ A*
         → Γ ⊢ j # e* ⦂ A*
t-subst0 ⊢e st-e stA = t-subst ⊢e ◀Z st-e stA
