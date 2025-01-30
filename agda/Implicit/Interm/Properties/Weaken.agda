module Implicit.Interm.Properties.Weaken where

open import Implicit.Language
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.Find

----------------------------------------------------------------------
--+                  weakening for term variables                  +--
----------------------------------------------------------------------

closed-weaken, : Closed Γ
               → Γ ▶ k , T ⇘ Γ'
               → Closed Γ'
closed-weaken, clo-Z (▶Z x) = clo-S, clo-Z x
closed-weaken, (clo-S, cloΓ cloA) (▶Z cloA₁) = clo-S, (clo-S, cloΓ cloA) cloA₁
closed-weaken, (clo-S, cloΓ cloA) (▶S, newΓ) = clo-S, (closed-weaken, cloΓ newΓ) (⊢c-weaken, cloA newΓ)
closed-weaken, (clo-S∙ cloΓ) (▶Z cloA) = clo-S, (clo-S∙ cloΓ) cloA
closed-weaken, (clo-S∙ cloΓ) (▶S∙ newΓ x) = clo-S∙ (closed-weaken, cloΓ newΓ)
closed-weaken, (clo-S^ cloΓ) (▶Z cloA) = clo-S, (clo-S^ cloΓ) cloA
closed-weaken, (clo-S^ cloΓ) (▶S^ newΓ x) = clo-S^ (closed-weaken, cloΓ newΓ)
closed-weaken, (clo-S= cloΓ cloA) (▶Z cloA₁) = clo-S, (clo-S= cloΓ cloA) cloA₁
closed-weaken, (clo-S= cloΓ cloA) (▶S= newΓ x) = clo-S= (closed-weaken, cloΓ newΓ) (⊢c-weaken, cloA newΓ)

closed-weaken∙ : Closed Γ
               → Γ ▶ k ,∙⇘ Γ'
               → Closed Γ'
closed-weaken∙ clo-Z ▶Z = clo-S∙ clo-Z
closed-weaken∙ (clo-S, cloΓ cloA) ▶Z = clo-S∙ (clo-S, cloΓ cloA)
closed-weaken∙ (clo-S, cloΓ cloA) (▶S, newΓ x) = clo-S, (closed-weaken∙ cloΓ newΓ) (⊢c-weaken∙ cloA newΓ x)
closed-weaken∙ (clo-S∙ cloΓ) ▶Z = clo-S∙ (clo-S∙ cloΓ)
closed-weaken∙ (clo-S∙ cloΓ) (▶S∙ newΓ) = clo-S∙ (closed-weaken∙ cloΓ newΓ)
closed-weaken∙ (clo-S^ cloΓ) ▶Z = clo-S∙ (clo-S^ cloΓ)
closed-weaken∙ (clo-S^ cloΓ) (▶S^ newΓ) = clo-S^ (closed-weaken∙ cloΓ newΓ)
closed-weaken∙ (clo-S= cloΓ cloA) ▶Z = clo-S∙ (clo-S= cloΓ cloA)
closed-weaken∙ (clo-S= cloΓ cloA) (▶S= newΓ x) = clo-S= (closed-weaken∙ cloΓ newΓ) (⊢c-weaken∙ cloA newΓ x)

closed-weaken^ : Closed Γ
               → Γ ▶ k ,^⇘ Γ'
               → Closed Γ'
closed-weaken^ clo-Z ▶Z = clo-S^ clo-Z
closed-weaken^ (clo-S, cloΓ cloA) ▶Z = clo-S^ (clo-S, cloΓ cloA)
closed-weaken^ (clo-S, cloΓ cloA) (▶S, newΓ x) = clo-S, (closed-weaken^ cloΓ newΓ) (⊢c-weaken^ cloA newΓ x)
closed-weaken^ (clo-S∙ cloΓ) ▶Z = clo-S^ (clo-S∙ cloΓ)
closed-weaken^ (clo-S∙ cloΓ) (▶S∙ newΓ) = clo-S∙ (closed-weaken^ cloΓ newΓ)
closed-weaken^ (clo-S^ cloΓ) ▶Z = clo-S^ (clo-S^ cloΓ)
closed-weaken^ (clo-S^ cloΓ) (▶S^ newΓ) = clo-S^ (closed-weaken^ cloΓ newΓ)
closed-weaken^ (clo-S= cloΓ cloA) ▶Z = clo-S^ (clo-S= cloΓ cloA)
closed-weaken^ (clo-S= cloΓ cloA) (▶S= newΓ x) = clo-S= (closed-weaken^ cloΓ newΓ) (⊢c-weaken^ cloA newΓ x)

closed-weaken= : Closed Γ
               → Γ ▶ k ,= T ⇘ Γ'
               → Closed Γ'
closed-weaken= clo-Z (▶Z x) = clo-S= clo-Z x
closed-weaken= (clo-S, clo cloA) (▶Z cloA₁) = clo-S= (clo-S, clo cloA) cloA₁
closed-weaken= (clo-S, clo cloA) (▶S, newΓ x) = clo-S, (closed-weaken= clo newΓ) (⊢c-weaken= cloA newΓ x)
closed-weaken= (clo-S∙ clo) (▶Z cloA) = clo-S= (clo-S∙ clo) cloA
closed-weaken= (clo-S∙ clo) (▶S∙ newΓ x) = clo-S∙ (closed-weaken= clo newΓ)
closed-weaken= (clo-S^ clo) (▶Z cloA) = clo-S= (clo-S^ clo) cloA
closed-weaken= (clo-S^ clo) (▶S^ newΓ x) = clo-S^ (closed-weaken= clo newΓ)
closed-weaken= (clo-S= clo cloA) (▶Z cloA₁) = clo-S= (clo-S= clo cloA) cloA₁
closed-weaken= (clo-S= clo cloA) (▶S= newΓ x x₁) = clo-S= (closed-weaken= clo newΓ) (⊢c-weaken= cloA newΓ x₁)


s-weaken, : Γ ⊢ j # A ≤ B
          → Γ ▶ k , T ⇘ Γ'
          → Γ' ⊢ j # A ≤ B
s-weaken, (s-refl cloΓ cloA) newΓ = s-refl (closed-weaken, cloΓ newΓ) (⊢c-weaken, cloA newΓ)
s-weaken, (s-int cloΓ) newΓ = s-int (closed-weaken, cloΓ newΓ)
s-weaken, (s-var-∙ inΓ cloΓ) newΓ = s-var-∙ (closed-weaken, inΓ newΓ) (▶,-∋∙ cloΓ newΓ)
s-weaken, (s-var-= inΓ cloΓ) newΓ = s-var-= (closed-weaken, inΓ newΓ) (▶,-∋= cloΓ newΓ)
s-weaken, (s-arr₁ s s₁) newΓ = s-arr₁ (s-weaken, s newΓ) (s-weaken, s₁ newΓ)
s-weaken, (s-arr₂ s s₁) newΓ = s-arr₂ (s-weaken, s newΓ) (s-weaken, s₁ newΓ)
s-weaken, (s-arr₃ cloA s) newΓ = s-arr₃ (⊢c-weaken, cloA newΓ) (s-weaken, s newΓ)
s-weaken, {T = T} (s-∀ s) newΓ = s-∀ (s-weaken, s (▶S∙ newΓ (proj₂ (↑ty0-total T) )))
s-weaken, {T = T} (s-∀l s x fd st₁ st₂) newΓ = s-∀l (s-weaken, s (▶S= newΓ (proj₂ (↑ty0-total T)))) x fd st₁ st₂
s-weaken, (s-var-l x s) newΓ = s-var-l (▶,-∋:= x newΓ) (s-weaken, s newΓ)
s-weaken, (s-var-r x s) newΓ = s-var-r (▶,-∋:= x newΓ) (s-weaken, s newΓ)

s-weaken,0 : Γ ⊢ j # A ≤ B
           → Γ ⊢c T
           → Γ , T ⊢ j # A ≤ B
s-weaken,0 s clo = s-weaken, s (▶Z clo)

----------------------------------------------------------------------
--+              weakening for exsitential variables               +--
----------------------------------------------------------------------

s-weaken^ : Γ ⊢ j # A ≤ B
          → Γ ▶ k ,^⇘ Γ'
          → A ↑ty k ⇘ A'
          → B ↑ty k ⇘ B'
          → Γ' ⊢ j # A' ≤ B'
s-weaken^ (s-refl cloΓ cloA) newΓ upA upB with ↑ty-unique upA upB
... | refl = s-refl (closed-weaken^ cloΓ newΓ) (⊢c-weaken^ cloA newΓ upB)
s-weaken^ (s-int cloΓ) newΓ ↑ty-int ↑ty-int = s-int (closed-weaken^ cloΓ newΓ)
s-weaken^ (s-var-∙ inΓ cloΓ) newΓ ↑ty-var ↑ty-var = s-var-∙ (closed-weaken^ inΓ newΓ) (▶^-∋∙ cloΓ newΓ)
s-weaken^ (s-var-= inΓ cloΓ) newΓ ↑ty-var ↑ty-var = s-var-= (closed-weaken^ inΓ newΓ) (▶^-∋= cloΓ newΓ)
s-weaken^ (s-arr₁ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₁ (s-weaken^ s upΓ upB upA) (s-weaken^ s₁ upΓ upA₁ upB₁)
s-weaken^ (s-arr₂ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₂ (s-weaken^ s upΓ upB upA) (s-weaken^ s₁ upΓ upA₁ upB₁)
s-weaken^ (s-arr₃ cloA s) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) with ↑ty-unique upA upB
... | refl = s-arr₃ (⊢c-weaken^ cloA upΓ upB) (s-weaken^ s upΓ upA₁ upB₁)
s-weaken^ (s-∀ s) upΓ (↑ty-∀ upA) (↑ty-∀ upB) = s-∀ (s-weaken^ s (▶S∙ upΓ) upA upB)
s-weaken^ {k = k} (s-∀l {B = B} {C = C} {D} s x fd st₁ st₂) upΓ (↑ty-∀ upA) (↑ty-arr upB upB₁)
  with ↑ty-total B k | ↑ty-total C (#S k) | ↑ty-total D (#S k)
... | ⟨ B' , upB' ⟩ | ⟨ C' , upC' ⟩ | ⟨ D' , upD' ⟩
  = s-∀l (s-weaken^ s (▶S= upΓ upB') upA (↑ty-arr upC' upD')) x (↑ty-find0 fd upA) (↑ty-st-comm0 st₁ upB' upC' upB) (↑ty-st-comm0 st₂ upB' upD' upB₁)
s-weaken^ {k = k} (s-var-l {B = B} x s) upΓ ↑ty-var upB with ↑ty-total B k
... | ⟨ B' , upB' ⟩ = s-var-l (▶^-∋:= x upΓ upB') (s-weaken^ s upΓ upB' upB)
s-weaken^ {k = k} (s-var-r {B = B} x s) upΓ upA ↑ty-var with ↑ty-total B k
... | ⟨ B' , upB' ⟩ = s-var-r (▶^-∋:= x upΓ upB') (s-weaken^ s upΓ upA upB')

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
s-weaken∙ (s-refl cloΓ cloA) newΓ upA upB with ↑ty-unique upA upB
... | refl = s-refl (closed-weaken∙ cloΓ newΓ) (⊢c-weaken∙ cloA newΓ upB)
s-weaken∙ (s-int cloΓ) newΓ ↑ty-int ↑ty-int = s-int (closed-weaken∙ cloΓ newΓ)
s-weaken∙ (s-var-∙ inΓ cloΓ) newΓ ↑ty-var ↑ty-var = s-var-∙ (closed-weaken∙ inΓ newΓ) (▶∙-∋∙ cloΓ newΓ)
s-weaken∙ (s-var-= inΓ cloΓ) newΓ ↑ty-var ↑ty-var = s-var-= (closed-weaken∙ inΓ newΓ) (▶∙-∋= cloΓ newΓ)
s-weaken∙ (s-arr₁ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₁ (s-weaken∙ s upΓ upB upA) (s-weaken∙ s₁ upΓ upA₁ upB₁)
s-weaken∙ (s-arr₂ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₂ (s-weaken∙ s upΓ upB upA) (s-weaken∙ s₁ upΓ upA₁ upB₁)
s-weaken∙ (s-arr₃ cloA s) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) rewrite ↑ty-unique upA upB = s-arr₃ (⊢c-weaken∙ cloA upΓ upB) (s-weaken∙ s upΓ upA₁ upB₁)
s-weaken∙ (s-∀ s) upΓ (↑ty-∀ upA) (↑ty-∀ upB) = s-∀ (s-weaken∙ s (▶S∙ upΓ) upA upB)
s-weaken∙ {k = k} (s-∀l {B = B} {C = C} {D} s x fd st₁ st₂) upΓ (↑ty-∀ upA) (↑ty-arr upB upB₁)
  with ↑ty-total B k | ↑ty-total C (#S k) | ↑ty-total D (#S k)
... | ⟨ B' , upB' ⟩ | ⟨ C' , upC' ⟩ | ⟨ D' , upD' ⟩
  = s-∀l (s-weaken∙ s (▶S= upΓ upB') upA (↑ty-arr upC' upD')) x (↑ty-find0 fd upA) (↑ty-st-comm0 st₁ upB' upC' upB) (↑ty-st-comm0 st₂ upB' upD' upB₁)
s-weaken∙ {k = k} (s-var-l {B = B} x s) upΓ ↑ty-var upB with ↑ty-total B k
... | ⟨ B' , upB' ⟩ = s-var-l (▶∙-∋:= x upΓ upB') (s-weaken∙ s upΓ upB' upB)
s-weaken∙ {k = k} (s-var-r {B = B} x s) upΓ upA ↑ty-var with ↑ty-total B k
... | ⟨ B' , upB' ⟩ = s-var-r (▶∙-∋:= x upΓ upB') (s-weaken∙ s upΓ upA upB')


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
s-weaken= (s-refl cloΓ cloA) newΓ upA upB with ↑ty-unique upA upB
... | refl = s-refl (closed-weaken= cloΓ newΓ) (⊢c-weaken= cloA newΓ upB)
s-weaken= (s-int cloΓ) newΓ ↑ty-int ↑ty-int = s-int (closed-weaken= cloΓ newΓ)
s-weaken= (s-var-∙ inΓ cloΓ) newΓ ↑ty-var ↑ty-var = s-var-∙ (closed-weaken= inΓ newΓ) (▶=-∋∙ cloΓ newΓ)
s-weaken= (s-var-= inΓ cloΓ) newΓ ↑ty-var ↑ty-var = s-var-= (closed-weaken= inΓ newΓ) (▶=-∋= cloΓ newΓ)
s-weaken= (s-arr₁ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₁ (s-weaken= s upΓ upB upA) (s-weaken= s₁ upΓ upA₁ upB₁)
s-weaken= (s-arr₂ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₂ (s-weaken= s upΓ upB upA) (s-weaken= s₁ upΓ upA₁ upB₁)
s-weaken= (s-arr₃ cloA s) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) rewrite ↑ty-unique upA upB = s-arr₃ (⊢c-weaken= cloA upΓ upB) (s-weaken= s upΓ upA₁ upB₁)
s-weaken= {T = T} (s-∀ s) upΓ (↑ty-∀ upA) (↑ty-∀ upB) = s-∀ (s-weaken= s (▶S∙ upΓ (proj₂ (↑ty0-total T))) upA upB)
s-weaken= {k = k} {T = T} (s-∀l {B = B} {C = C} {D} s x fd st₁ st₂) upΓ (↑ty-∀ upA) (↑ty-arr upB upB₁)
  with ↑ty-total B k | ↑ty-total C (#S k) | ↑ty-total D (#S k)
... | ⟨ B' , upB' ⟩ | ⟨ C' , upC' ⟩ | ⟨ D' , upD' ⟩
  = s-∀l (s-weaken= s (▶S= upΓ (proj₂ (↑ty0-total T)) upB')
         upA (↑ty-arr upC' upD')) x (↑ty-find0 fd upA) (↑ty-st-comm0 st₁ upB' upC' upB) (↑ty-st-comm0 st₂ upB' upD' upB₁)
s-weaken= {k = k} (s-var-l {B = B} x s) upΓ ↑ty-var upB with ↑ty-total B k
... | ⟨ B' , upB' ⟩ = s-var-l (▶=-∋:= x upΓ upB') (s-weaken= s upΓ upB' upB)
s-weaken= {k = k} (s-var-r {B = B} x s) upΓ upA ↑ty-var with ↑ty-total B k
... | ⟨ B' , upB' ⟩ = s-var-r (▶=-∋:= x upΓ upB') (s-weaken= s upΓ upA upB')

s-weaken=0 : Γ ⊢ j # A ≤ B
           → ↑ty0 A ⇘ A'
           → ↑ty0 B ⇘ B'
           → Γ ⊢c T
           → Γ ,= T ⊢ j # A' ≤ B'
s-weaken=0 s upA upB cloT = s-weaken= s (▶Z cloT) upA upB
