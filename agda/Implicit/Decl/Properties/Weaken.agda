module Implicit.Decl.Properties.Weaken where

open import Implicit.Language
open import Implicit.Decl.Base
open import Implicit.Decl.Properties.Find

▶-∋=-^ : Γ ∋ X := A
     → Γ ▶ k ,^⇘ Γ'
     → A ↑ty k ⇘ A'
     → Γ' ∋ punchIn k X := A'
▶-∋=-^ (Z up) ▶Z upA = S^ (Z up) upA
▶-∋=-^ (Z up) (▶S= newΓ x) upA = Z (↑ty-comm0 up upA x)
▶-∋=-^ (S, inΓ) ▶Z upA = S^ (S, inΓ) upA
▶-∋=-^ (S, inΓ) (▶S, newΓ x) upA = S, (▶-∋=-^ inΓ newΓ upA)
▶-∋=-^ (S∙ inΓ up) ▶Z upA = S^ (S∙ inΓ up) upA
▶-∋=-^ (S∙ {A = A} inΓ up) (▶S∙ {k = k} newΓ) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S∙ (▶-∋=-^ inΓ newΓ upA') (↑ty-comm0 up upA upA')
▶-∋=-^ (S^ inΓ up) ▶Z upA = S^ (S^ inΓ up) upA
▶-∋=-^ (S^ {A = A} inΓ up) (▶S^ {k = k} newΓ) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S^ (▶-∋=-^ inΓ newΓ upA') (↑ty-comm0 up upA upA')
▶-∋=-^ (S= inΓ up) ▶Z upA = S^ (S= inΓ up) upA
▶-∋=-^ (S= {A = A} inΓ up) (▶S= {k = k} newΓ x) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S= (▶-∋=-^ inΓ newΓ upA') (↑ty-comm0 up upA upA')

▶-∋=-∙ : Γ ∋ X := A
     → Γ ▶ k ,∙⇘ Γ'
     → A ↑ty k ⇘ A'
     → Γ' ∋ punchIn k X := A'
▶-∋=-∙ (Z up) ▶Z upA = S∙ (Z up) upA
▶-∋=-∙ (Z up) (▶S= newΓ x) upA = Z (↑ty-comm0 up upA x)
▶-∋=-∙ (S, inΓ) ▶Z upA = S∙ (S, inΓ) upA
▶-∋=-∙ (S, inΓ) (▶S, newΓ x) upA = S, (▶-∋=-∙ inΓ newΓ upA)
▶-∋=-∙ (S∙ inΓ up) ▶Z upA = S∙ (S∙ inΓ up) upA
▶-∋=-∙ (S∙ {A = A} inΓ up) (▶S∙ {k = k} newΓ) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S∙ (▶-∋=-∙ inΓ newΓ upA') (↑ty-comm0 up upA upA')
▶-∋=-∙ (S^ inΓ up) ▶Z upA = S∙ (S^ inΓ up) upA
▶-∋=-∙ (S^ {A = A} inΓ up) (▶S^ {k = k} newΓ) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S^ (▶-∋=-∙ inΓ newΓ upA') (↑ty-comm0 up upA upA')
▶-∋=-∙ (S= inΓ up) ▶Z upA = S∙ (S= inΓ up) upA
▶-∋=-∙ (S= {A = A} inΓ up) (▶S= {k = k} newΓ x) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S= (▶-∋=-∙ inΓ newΓ upA') (↑ty-comm0 up upA upA')

▶-∋=-= : Γ ∋ X := A
       → Γ ▶ k ,= T ⇘ Γ'
       → A ↑ty k ⇘ A'
       → Γ' ∋ punchIn k X := A'
▶-∋=-= (Z up) ▶Z upA = S= (Z up) upA
▶-∋=-= (Z up) (▶S= newΓ x x₁) upA = Z (↑ty-comm0 up upA x₁)
▶-∋=-= (S, inΓ) ▶Z upA = S= (S, inΓ) upA
▶-∋=-= (S, inΓ) (▶S, newΓ x) upA = S, (▶-∋=-= inΓ newΓ upA)
▶-∋=-= (S∙ inΓ up) ▶Z upA = S= (S∙ inΓ up) upA
▶-∋=-= (S∙ {A = A} inΓ up) (▶S∙ {k = k} newΓ x) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S∙ (▶-∋=-= inΓ newΓ upA') (↑ty-comm0 up upA upA')
▶-∋=-= (S^ inΓ up) ▶Z upA = S= (S^ inΓ up) upA
▶-∋=-= (S^ {A = A} inΓ up) (▶S^ {k = k} newΓ x) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S^ (▶-∋=-= inΓ newΓ upA') (↑ty-comm0 up upA upA')
▶-∋=-= (S= inΓ up) ▶Z upA = S= (S= inΓ up) upA
▶-∋=-= (S= {A = A} inΓ up) (▶S= {k = k} newΓ x x₁) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S= (▶-∋=-= inΓ newΓ upA') (↑ty-comm0 up upA upA')


▶-∋=-, : Γ ∋ X := A
       → Γ ▶ k , T ⇘ Γ'
       → Γ' ∋ X := A
▶-∋=-, (Z up) ▶Z = S, (Z up)
▶-∋=-, (Z up) (▶S= newΓ x) = Z up
▶-∋=-, (S, inΓ) ▶Z = S, (S, inΓ)
▶-∋=-, (S, inΓ) (▶S, newΓ) = S, (▶-∋=-, inΓ newΓ)
▶-∋=-, (S∙ inΓ up) ▶Z = S, (S∙ inΓ up)
▶-∋=-, (S∙ inΓ up) (▶S∙ newΓ x) = S∙ (▶-∋=-, inΓ newΓ) up
▶-∋=-, (S^ inΓ up) ▶Z = S, (S^ inΓ up)
▶-∋=-, (S^ inΓ up) (▶S^ newΓ x) = S^ (▶-∋=-, inΓ newΓ) up
▶-∋=-, (S= inΓ up) ▶Z = S, (S= inΓ up)
▶-∋=-, (S= inΓ up) (▶S= newΓ x) = S= (▶-∋=-, inΓ newΓ) up

----------------------------------------------------------------------
--+                  weakening for term variables                  +--
----------------------------------------------------------------------

s-weaken, : Γ ⊢ j # A ≤ B
          → Γ ▶ k , T ⇘ Γ'
          → Γ' ⊢ j # A ≤ B
s-weaken, s-refl newΓ = s-refl
s-weaken, s-int newΓ = s-int
s-weaken, s-var newΓ = s-var
s-weaken, (s-arr₁ s s₁) newΓ = s-arr₁ (s-weaken, s newΓ) (s-weaken, s₁ newΓ)
s-weaken, (s-arr₂ s s₁) newΓ = s-arr₂ (s-weaken, s newΓ) (s-weaken, s₁ newΓ)
s-weaken, (s-arr₃ s) newΓ = s-arr₃ (s-weaken, s newΓ)
s-weaken, {T = T} (s-∀ s) newΓ = s-∀ (s-weaken, s (▶S∙ newΓ (proj₂ (↑ty0-total T) )))
s-weaken, {T = T} (s-∀l s x fd st₁ st₂) newΓ = s-∀l (s-weaken, s (▶S= newΓ (proj₂ (↑ty0-total T)))) x fd st₁ st₂
s-weaken, (s-var-l x s) newΓ = s-var-l (▶-∋=-, x newΓ) (s-weaken, s newΓ)
s-weaken, (s-var-r x s) newΓ = s-var-r (▶-∋=-, x newΓ) (s-weaken, s newΓ)

s-weaken,0 : Γ ⊢ j # A ≤ B
           → Γ , T ⊢ j # A ≤ B
s-weaken,0 s = s-weaken, s ▶Z

----------------------------------------------------------------------
--+              weakening for exsitential variables               +--
----------------------------------------------------------------------

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
... | ⟨ B' , upB' ⟩ = s-var-l (▶-∋=-^ x upΓ upB') (s-weaken^ s upΓ upB' upB)
s-weaken^ {k = k} (s-var-r {B = B} x s) upΓ upA ↑ty-var with ↑ty-total B k
... | ⟨ B' , upB' ⟩ = s-var-r (▶-∋=-^ x upΓ upB') (s-weaken^ s upΓ upA upB')

s-weaken^0 : Γ ⊢ j # A ≤ B
           → ↑ty0 A ⇘ A'
           → ↑ty0 B ⇘ B'
           → Γ ,^ ⊢ j # A' ≤ B'
s-weaken^0 s upA upB = s-weaken^ s ▶Z upA upB

----------------------------------------------------------------------
--+               Weakening for universal variables                +--
----------------------------------------------------------------------

s-weaken∙ : Γ ⊢ j # A ≤ B
          → Γ ▶ k ,∙⇘ Γ'
          → A ↑ty k ⇘ A'
          → B ↑ty k ⇘ B'
          → Γ' ⊢ j # A' ≤ B'
s-weaken∙ s-refl upΓ upA upB rewrite ↑ty-unique upA upB = s-refl
s-weaken∙ s-int upΓ ↑ty-int ↑ty-int = s-int
s-weaken∙ s-var upΓ ↑ty-var ↑ty-var = s-var
s-weaken∙ (s-arr₁ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₁ (s-weaken∙ s upΓ upB upA) (s-weaken∙ s₁ upΓ upA₁ upB₁)
s-weaken∙ (s-arr₂ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₂ (s-weaken∙ s upΓ upB upA) (s-weaken∙ s₁ upΓ upA₁ upB₁)
s-weaken∙ (s-arr₃ s) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) rewrite ↑ty-unique upA upB = s-arr₃ (s-weaken∙ s upΓ upA₁ upB₁)
s-weaken∙ (s-∀ s) upΓ (↑ty-∀ upA) (↑ty-∀ upB) = s-∀ (s-weaken∙ s (▶S∙ upΓ) upA upB)
s-weaken∙ {k = k} (s-∀l {B = B} {C = C} {D} s x fd st₁ st₂) upΓ (↑ty-∀ upA) (↑ty-arr upB upB₁)
  with ↑ty-total B k | ↑ty-total C (#S k) | ↑ty-total D (#S k)
... | ⟨ B' , upB' ⟩ | ⟨ C' , upC' ⟩ | ⟨ D' , upD' ⟩
  = s-∀l (s-weaken∙ s (▶S= upΓ upB') upA (↑ty-arr upC' upD')) x (↑ty-find0 fd upA) (↑ty-st-comm0 st₁ upB' upC' upB) (↑ty-st-comm0 st₂ upB' upD' upB₁)
s-weaken∙ {k = k} (s-var-l {B = B} x s) upΓ ↑ty-var upB with ↑ty-total B k
... | ⟨ B' , upB' ⟩ = s-var-l (▶-∋=-∙ x upΓ upB') (s-weaken∙ s upΓ upB' upB)
s-weaken∙ {k = k} (s-var-r {B = B} x s) upΓ upA ↑ty-var with ↑ty-total B k
... | ⟨ B' , upB' ⟩ = s-var-r (▶-∋=-∙ x upΓ upB') (s-weaken∙ s upΓ upA upB')


s-weaken∙0 : Γ ⊢ j # A ≤ B
           → ↑ty0 A ⇘ A'
           → ↑ty0 B ⇘ B'
           → Γ ,∙ ⊢ j # A' ≤ B'
s-weaken∙0 s upA upB = s-weaken∙ s ▶Z upA upB

----------------------------------------------------------------------
--+               Weakening for solutions                          +--
----------------------------------------------------------------------

s-weaken= : Γ ⊢ j # A ≤ B
          → Γ ▶ k ,= T ⇘ Γ'
          → A ↑ty k ⇘ A'
          → B ↑ty k ⇘ B'
          → Γ' ⊢ j # A' ≤ B'
s-weaken= s-refl upΓ upA upB rewrite ↑ty-unique upA upB = s-refl
s-weaken= s-int upΓ ↑ty-int ↑ty-int = s-int
s-weaken= s-var upΓ ↑ty-var ↑ty-var = s-var
s-weaken= (s-arr₁ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₁ (s-weaken= s upΓ upB upA) (s-weaken= s₁ upΓ upA₁ upB₁)
s-weaken= (s-arr₂ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₂ (s-weaken= s upΓ upB upA) (s-weaken= s₁ upΓ upA₁ upB₁)
s-weaken= (s-arr₃ s) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) rewrite ↑ty-unique upA upB = s-arr₃ (s-weaken= s upΓ upA₁ upB₁)
s-weaken= {T = T} (s-∀ s) upΓ (↑ty-∀ upA) (↑ty-∀ upB) = s-∀ (s-weaken= s (▶S∙ upΓ (proj₂ (↑ty0-total T))) upA upB)
s-weaken= {k = k} {T = T} (s-∀l {B = B} {C = C} {D} s x fd st₁ st₂) upΓ (↑ty-∀ upA) (↑ty-arr upB upB₁)
  with ↑ty-total B k | ↑ty-total C (#S k) | ↑ty-total D (#S k)
... | ⟨ B' , upB' ⟩ | ⟨ C' , upC' ⟩ | ⟨ D' , upD' ⟩
  = s-∀l (s-weaken= s (▶S= upΓ (proj₂ (↑ty0-total T)) upB')
         upA (↑ty-arr upC' upD')) x (↑ty-find0 fd upA) (↑ty-st-comm0 st₁ upB' upC' upB) (↑ty-st-comm0 st₂ upB' upD' upB₁)
s-weaken= {k = k} (s-var-l {B = B} x s) upΓ ↑ty-var upB with ↑ty-total B k
... | ⟨ B' , upB' ⟩ = s-var-l (▶-∋=-= x upΓ upB') (s-weaken= s upΓ upB' upB)
s-weaken= {k = k} (s-var-r {B = B} x s) upΓ upA ↑ty-var with ↑ty-total B k
... | ⟨ B' , upB' ⟩ = s-var-r (▶-∋=-= x upΓ upB') (s-weaken= s upΓ upA upB')

s-weaken=0 : Γ ⊢ j # A ≤ B
           → ↑ty0 A ⇘ A'
           → ↑ty0 B ⇘ B'
           → Γ ,= T ⊢ j # A' ≤ B'
s-weaken=0 s upA upB = s-weaken= s ▶Z upA upB           
