module Implicit.Decl.Properties.Weaken where

open import Implicit.Language
open import Implicit.Decl.Base

private variable
  Γ : Env n m
  A A' B B' A* B* T : Type m
  j : Counter

postulate

  s-weaken : ∀ {Γ : Env (1 + n) m} {k j A B }
    → Γ ∤,∤ k ⊢ j # A ≤ B
    → Γ ⊢ j # A ≤ B
  
  weaken : ∀ {Γ : Env (1 + n) m} {k j e A}
    → Γ ∤,∤ k ⊢ j # e ⦂ A
    → Γ ⊢ j # ↑tm k e ⦂ A

  s-weaken=0 : Γ ⊢ j # A* ≤ B*
             → ⟦ T ⟧ A ⇘ A*
             → ⟦ T ⟧ B ⇘ B*
             → Γ ,= T ⊢ j # A ≤ B

  s-weaken∙0 : Γ ⊢ j # A ≤ B
             → ↑ty0 A ⇘ A'
             → ↑ty0 B ⇘ B'
             → Γ ,∙ ⊢ j # A' ≤ B'
                 
  s-weaken^0 : Γ ⊢ j # A ≤ B
             → ↑ty0 A ⇘ A'
             → ↑ty0 B ⇘ B'
             → Γ ,^ ⊢ j # A' ≤ B'

s-weaken,0 : Γ ⊢ j # A ≤ B
           → Γ , T ⊢ j # A ≤ B
s-weaken,0 s = s-weaken {k = #0} s
                 
weaken-0 : ∀ {Γ : Env (1 + n) m} {j e A}
  → Γ ⊢ j # e ⦂ A
  → Γ , A ⊢ j # ↑tm0 e ⦂ A
weaken-0 {Γ = Γ} {A = A} ⊢e = weaken {Γ = Γ , A} {k = #0} ⊢e
