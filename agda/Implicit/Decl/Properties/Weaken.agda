module Implicit.Decl.Properties.Weaken where

open import Implicit.Language
open import Implicit.Decl.Base

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
  
weaken-0 : ∀ {Γ : Env (1 + n) m} {j e A}
  → Γ ⊢ j # e ⦂ A
  → Γ , A ⊢ j # ↑tm0 e ⦂ A
weaken-0 {Γ = Γ} {A = A} ⊢e = weaken {Γ = Γ , A} {k = #0} ⊢e
