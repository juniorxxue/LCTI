module Implicit.Decl.Properties.Weaken where

open import Implicit.Language
open import Implicit.Decl.Base
open import Implicit.Decl.Properties.Find

----------------------------------------------------------------------
--+                  weakening for term variables                  +--
----------------------------------------------------------------------

⊢cⁿto⊢c : Γ ⊢cⁿ A by #0
        → Γ ⊢c A
⊢cⁿto⊢c (clb-Z cloA) = cloA
⊢cⁿto⊢c (clb-S∙ clo up) = ⊢c-weaken∙0 (⊢cⁿto⊢c clo) {!!}
⊢cⁿto⊢c (clb-S^ clo up) = ⊢c-weaken^0 (⊢cⁿto⊢c clo) {!!}
⊢cⁿto⊢c (clb-S= clo up) = ⊢c-weaken=0 (⊢cⁿto⊢c clo) {!!}

⊢cⁿ-strengthen, : Γ ⊢cⁿ A by k
                → Γ ◀ k' ,⇘ Γ'
                → Γ' ⊢cⁿ A by pinch k' k
⊢cⁿ-strengthen, (clb-Z cloA) newΓ = clb-Z (⊢c-strengthen, cloA newΓ)
⊢cⁿ-strengthen, (clb-S, clo) ◀Z = clo
⊢cⁿ-strengthen, (clb-S, clo) (◀S, newΓ) = clb-S, (⊢cⁿ-strengthen, clo newΓ)
⊢cⁿ-strengthen, (clb-S∙ clo up) (◀S∙ newΓ) = clb-S∙ (⊢cⁿ-strengthen, clo newΓ) up
⊢cⁿ-strengthen, (clb-S^ clo up) (◀S^ newΓ) = clb-S^ (⊢cⁿ-strengthen, clo newΓ) up
⊢cⁿ-strengthen, (clb-S= clo up) (◀S= newΓ) = clb-S= (⊢cⁿ-strengthen, clo newΓ) up

⊢cⁿ-strengthen^ : Γ ⊢cⁿ A' by k
                → Γ ◀ k' ^⇘ Γ'
                → A ↑ty k' ⇘ A'
                → Γ' ⊢cⁿ A by k
⊢cⁿ-strengthen^ (clb-Z cloA) newΓ' upA = clb-Z (⊢c-strengthen^ cloA newΓ' upA)
⊢cⁿ-strengthen^ (clb-S, clo) (◀S, newΓ' x) upA = clb-S, (⊢cⁿ-strengthen^ clo newΓ' upA)
⊢cⁿ-strengthen^ (clb-S∙ clo up) (◀S∙ newΓ') upA = clb-S∙ (⊢cⁿ-strengthen^ clo newΓ' {!!}) {!!}
⊢cⁿ-strengthen^ (clb-S^ clo up) ◀Z upA = {!!}
⊢cⁿ-strengthen^ (clb-S^ clo up) (◀S^ newΓ') upA = {!!}
⊢cⁿ-strengthen^ (clb-S= clo up) (◀S= newΓ' up₁) upA = clb-S= (⊢cⁿ-strengthen^ clo newΓ' {!!}) {!!}

⊢cⁿ-strengthen^' : Γ ⊢cⁿ A by k
                 → Γ ◀ k' ^⇘ Γ'
                 → A ↓ty k' ⇘ A'
                 → Γ' ⊢cⁿ A' by k
⊢cⁿ-strengthen^' (clb-Z cloA) newΓ don = clb-Z {!!}
⊢cⁿ-strengthen^' (clb-S, clo) (◀S, newΓ up) don = clb-S, (⊢cⁿ-strengthen^' clo newΓ don)
⊢cⁿ-strengthen^' (clb-S∙ clo up) (◀S∙ newΓ) don = clb-S∙ (⊢cⁿ-strengthen^' clo newΓ {!!}) {!!}
⊢cⁿ-strengthen^' (clb-S^ clo up) newΓ don = {!!}
⊢cⁿ-strengthen^' (clb-S= clo up) newΓ don = {!!}

closed-weaken, : Closed Γ
               → Γ ▶ k , T ⇘ Γ'
               → Γ ⊢cⁿ T by k
               → Closed Γ'
closed-weaken, clo-Z ▶Z (clb-Z cloA) = clo-S, clo-Z cloA
closed-weaken, (clo-S, cloΓ cloA) ▶Z (clb-Z cloA₁) = clo-S, (clo-S, cloΓ cloA) cloA₁
closed-weaken, (clo-S, cloΓ cloA) (▶S, newΓ) (clb-S, cloT) = clo-S, (closed-weaken, cloΓ newΓ cloT) (⊢c-weaken, cloA newΓ)
closed-weaken, (clo-S∙ cloΓ) ▶Z (clb-Z cloA) = clo-S, (clo-S∙ cloΓ) cloA
closed-weaken, (clo-S∙ cloΓ) ▶Z (clb-S∙ cloT up) = clo-S, (clo-S∙ cloΓ) {!!}
closed-weaken, (clo-S∙ cloΓ) (▶S∙ newΓ x) cloT = clo-S∙ (closed-weaken, cloΓ newΓ {!!})
closed-weaken, (clo-S^ cloΓ) newΓ cloT = {!!}
closed-weaken, (clo-S= cloΓ cloA) newΓ cloT = {!!}

s-weaken, : Γ ⊢ j # A ≤ B
          → Γ ⊢cⁿ T by k
          → Γ ▶ k , T ⇘ Γ'
          → Γ' ⊢ j # A ≤ B
s-weaken, (s-refl cloΓ cloA) cloT newΓ = s-refl {!!} (⊢c-weaken, cloA newΓ)
s-weaken, (s-int cloΓ) cloT newΓ = s-int {!!}
s-weaken, (s-var-∙ cloΓ inΓ) cloT newΓ = s-var-∙ {!!} (▶,-∋∙ inΓ newΓ)
s-weaken, (s-var-= cloΓ inΓ) cloT newΓ = s-var-= {!!} (▶,-∋= inΓ newΓ)
s-weaken, (s-arr₁ s s₁) cloT newΓ = s-arr₁ (s-weaken, s cloT newΓ) (s-weaken, s₁ cloT newΓ)
s-weaken, (s-arr₂ s s₁) cloT newΓ = s-arr₂ (s-weaken, s cloT newΓ) (s-weaken, s₁ cloT newΓ)
s-weaken, (s-arr₃ cloA s) cloT newΓ = s-arr₃ (⊢c-weaken, cloA newΓ) (s-weaken, s cloT newΓ)
s-weaken, {T = T} (s-∀ s) cloT newΓ = let ⟨ T' , upT ⟩ = ↑ty0-total T
                                      in s-∀ (s-weaken, s (clb-S∙ cloT {!!}) (▶S∙ newΓ upT))
s-weaken, {T = T} (s-∀l s ic fd st₁ st₂) cloT newΓ = let ⟨ T' , upT ⟩ = ↑ty0-total T
                                                     in s-∀l (s-weaken, s (clb-S= cloT upT) (▶S= newΓ upT)) ic fd st₁ st₂
s-weaken, (s-var-l inΓ s) cloT newΓ = s-var-l (▶,-∋:= inΓ newΓ) (s-weaken, s cloT newΓ)
s-weaken, (s-var-r inΓ s) cloT newΓ = s-var-r (▶,-∋:= inΓ newΓ) (s-weaken, s cloT newΓ)

{-
s-weaken, (s-refl cloΓ cloA) newΓ = s-refl {!!} {!!}
s-weaken, (s-int cloΓ) newΓ = s-int {!!}
s-weaken, (s-var-∙ inΓ cloΓ) newΓ = s-var-∙ {!!} {!!}
s-weaken, (s-var-= inΓ cloΓ) newΓ = {!!}
s-weaken, (s-arr₁ s s₁) newΓ = s-arr₁ (s-weaken, s newΓ) (s-weaken, s₁ newΓ)
s-weaken, (s-arr₂ s s₁) newΓ = s-arr₂ (s-weaken, s newΓ) (s-weaken, s₁ newΓ)
s-weaken, (s-arr₃ cloA s) newΓ = {!!}
s-weaken, {T = T} (s-∀ s) newΓ = s-∀ (s-weaken, s (▶S∙ newΓ (proj₂ (↑ty0-total T) )))
s-weaken, {T = T} (s-∀l s x fd st₁ st₂) newΓ = s-∀l (s-weaken, s (▶S= newΓ (proj₂ (↑ty0-total T)))) x fd st₁ st₂
s-weaken, (s-var-l x s) newΓ = s-var-l (▶,-∋:= x newΓ) (s-weaken, s newΓ)
s-weaken, (s-var-r x s) newΓ = s-var-r (▶,-∋:= x newΓ) (s-weaken, s newΓ)
-}

s-weaken,0 : Γ ⊢ j # A ≤ B
           → Γ ⊢c T
           → Γ , T ⊢ j # A ≤ B
s-weaken,0 s cloT = s-weaken, s (clb-Z cloT) ▶Z

----------------------------------------------------------------------
--+              weakening for exsitential variables               +--
----------------------------------------------------------------------

s-weaken^ : Γ ⊢ j # A ≤ B
          → Γ ▶ k ,^⇘ Γ'
          → A ↑ty k ⇘ A'
          → B ↑ty k ⇘ B'
          → Γ' ⊢ j # A' ≤ B'
s-weaken^ (s-refl cloΓ cloA) newΓ = {!!}
s-weaken^ (s-int cloΓ) newΓ = {!!}
s-weaken^ (s-var-∙ inΓ cloΓ) newΓ = {!!}
s-weaken^ (s-var-= inΓ cloΓ) newΓ = {!!}
s-weaken^ (s-arr₁ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₁ (s-weaken^ s upΓ upB upA) (s-weaken^ s₁ upΓ upA₁ upB₁)
s-weaken^ (s-arr₂ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₂ (s-weaken^ s upΓ upB upA) (s-weaken^ s₁ upΓ upA₁ upB₁)
s-weaken^ (s-arr₃ cloA s) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) rewrite ↑ty-unique upA upB = {!!}
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
s-weaken∙ (s-refl cloΓ cloA) newΓ = {!!}
s-weaken∙ (s-int cloΓ) newΓ = {!!}
s-weaken∙ (s-var-∙ inΓ cloΓ) newΓ = {!!}
s-weaken∙ (s-var-= inΓ cloΓ) newΓ = {!!}
s-weaken∙ (s-arr₁ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₁ (s-weaken∙ s upΓ upB upA) (s-weaken∙ s₁ upΓ upA₁ upB₁)
s-weaken∙ (s-arr₂ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₂ (s-weaken∙ s upΓ upB upA) (s-weaken∙ s₁ upΓ upA₁ upB₁)
s-weaken∙ (s-arr₃ cloA s) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) rewrite ↑ty-unique upA upB = s-arr₃ {!!} (s-weaken∙ s upΓ upA₁ upB₁)
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
s-weaken= (s-refl cloΓ cloA) newΓ = {!!}
s-weaken= (s-int cloΓ) newΓ = {!!}
s-weaken= (s-var-∙ inΓ cloΓ) newΓ = {!!}
s-weaken= (s-var-= inΓ cloΓ) newΓ = {!!}
s-weaken= (s-arr₁ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₁ (s-weaken= s upΓ upB upA) (s-weaken= s₁ upΓ upA₁ upB₁)
s-weaken= (s-arr₂ s s₁) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = s-arr₂ (s-weaken= s upΓ upB upA) (s-weaken= s₁ upΓ upA₁ upB₁)
s-weaken= (s-arr₃ cloA s) upΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) rewrite ↑ty-unique upA upB = s-arr₃ {!!} (s-weaken= s upΓ upA₁ upB₁)
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
           → Γ ,= T ⊢ j # A' ≤ B'
s-weaken=0 s upA upB = s-weaken= s ▶Z upA upB
