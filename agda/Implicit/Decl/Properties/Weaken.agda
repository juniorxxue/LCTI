module Implicit.Decl.Properties.Weaken where

open import Implicit.Language
open import Implicit.Decl.Base
open import Implicit.Decl.Properties.Find

private variable
  Γ Γ' : Env n m
  A A' B B' A* B* C C* C' C*' T : Type m
  j : Counter
  X k : Fin m

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

▶-∋= : Γ ∋ X := A
     → Γ ▶ k ,^⇘ Γ'
     → A ↑ty k ⇘ A'
     → Γ' ∋ punchIn k X := A'
▶-∋= (Z up) ▶Z upA = S^ (Z up) upA
▶-∋= (Z up) (▶S= newΓ x) upA = Z (↑ty-comm0 up upA x)
▶-∋= (S, inΓ) ▶Z upA = S^ (S, inΓ) upA
▶-∋= (S, inΓ) (▶S, newΓ x) upA = S, (▶-∋= inΓ newΓ upA)
▶-∋= (S∙ inΓ up) ▶Z upA = S^ (S∙ inΓ up) upA
▶-∋= (S∙ {A = A} inΓ up) (▶S∙ {k = k} newΓ) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S∙ (▶-∋= inΓ newΓ upA') (↑ty-comm0 up upA upA')
▶-∋= (S^ inΓ up) ▶Z upA = S^ (S^ inΓ up) upA
▶-∋= (S^ {A = A} inΓ up) (▶S^ {k = k} newΓ) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S^ (▶-∋= inΓ newΓ upA') (↑ty-comm0 up upA upA')
▶-∋= (S= inΓ up) ▶Z upA = S^ (S= inΓ up) upA
▶-∋= (S= {A = A} inΓ up) (▶S= {k = k} newΓ x) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S= (▶-∋= inΓ newΓ upA') (↑ty-comm0 up upA upA')

s-weaken,0 : Γ ⊢ j # A ≤ B
           → Γ , T ⊢ j # A ≤ B
s-weaken,0 s = s-weaken {k = #0} s
                 
weaken-0 : ∀ {Γ : Env (1 + n) m} {j e A}
  → Γ ⊢ j # e ⦂ A
  → Γ , A ⊢ j # ↑tm0 e ⦂ A
weaken-0 {Γ = Γ} {A = A} ⊢e = weaken {Γ = Γ , A} {k = #0} ⊢e

s-weaken^ : Γ ⊢ j # A ≤ B
          → Γ ▶ k ,^⇘ Γ'
          → A ↑ty k ⇘ A'
          → B ↑ty k ⇘ B'
          → Γ' ⊢ j # A' ≤ B'
s-weaken^ s-refl upΓ upA upB rewrite ↑ty-unique upA upB = s-refl
s-weaken^ s-int upΓ ↑ty-int ↑ty-int = s-int
s-weaken^ s-var upΓ ↑ty-var ↑ty-var = s-var
s-weaken^ (s-arr₁ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₁ (s-weaken^ s upΓ upB upA) (s-weaken^ s₁ upΓ upA₁ upB₁)
s-weaken^ (s-arr₂ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₂ (s-weaken^ s upΓ upB upA) (s-weaken^ s₁ upΓ upA₁ upB₁)
s-weaken^ (s-arr₃ s) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) rewrite ↑ty-unique upA upB = s-arr₃ (s-weaken^ s upΓ upA₁ upB₁)
s-weaken^ (s-∀ s) upΓ (↑ty-∀ upA) (↑ty-∀ upB) = s-∀ (s-weaken^ s (▶S∙ upΓ) upA upB)
s-weaken^ {k = k} (s-∀l {B = B} {C = C} {D} s x fd st₁ st₂) upΓ (↑ty-∀ upA) (↑ty-arr upB upB₁)
  with ↑ty-total B k | ↑ty-total C (#S k) | ↑ty-total D (#S k)
... | ⟨ B' , upB' ⟩ | ⟨ C' , upC' ⟩ | ⟨ D' , upD' ⟩
  = s-∀l (s-weaken^ s (▶S= upΓ upB') upA (↑ty-arr upC' upD')) x (↑ty-find0 fd upA) (↑ty-st-comm0 st₁ upB' upC' upB) (↑ty-st-comm0 st₂ upB' upD' upB₁)
s-weaken^ {k = k} (s-var-l {B = B} x s) upΓ ↑ty-var upB with ↑ty-total B k
... | ⟨ B' , upB' ⟩ = s-var-l (▶-∋= x upΓ upB') (s-weaken^ s upΓ upB' upB)
s-weaken^ {k = k} (s-var-r {B = B} x s) upΓ upA ↑ty-var with ↑ty-total B k
... | ⟨ B' , upB' ⟩ = s-var-r (▶-∋= x upΓ upB') (s-weaken^ s upΓ upA upB')

s-weaken^0 : Γ ⊢ j # A ≤ B
           → ↑ty0 A ⇘ A'
           → ↑ty0 B ⇘ B'
           → Γ ,^ ⊢ j # A' ≤ B'
s-weaken^0 s upA upB = s-weaken^ s ▶Z upA upB           
