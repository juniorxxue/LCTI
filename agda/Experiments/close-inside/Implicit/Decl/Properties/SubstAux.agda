module Implicit.Decl.Properties.SubstAux where

open import Implicit.Language
open import Implicit.Decl.Base
open import Implicit.Decl.Properties.OpenClose


∋:=-subst : Γ ∋ X := A
          → Γ ◀ k := T ⇘ Γ*
          → (¬p : k ≢ X)
          → ⟦ k / T ⟧ A ⇘ A*
          → Γ* ∋ punchOut ¬p := A*
∋:=-subst {k = #0} (Z up) newΓ ¬p stA = ⊥-elim (¬p refl)
∋:=-subst {k = #S k} (Z up) (◀S= newΓ up₁ x) ¬p stA = Z (↑ty-st-comm1 z≤n x up₁ up stA)
∋:=-subst (S, inΓ) (◀S, newΓ x) ¬p stA = S, (∋:=-subst inΓ newΓ ¬p stA)
∋:=-subst (S∙ {A = B} inΓ up) (◀S∙ {k = k} {A} newΓ up₁) ¬p stA = let ⟨ B* , st ⟩ = st-total A k B
  in S∙ (∋:=-subst inΓ newΓ (≢-pred ¬p) st) (↑ty-st-comm1 z≤n st up₁ up stA)
∋:=-subst (S^ {A = B} inΓ up) (◀S^ {k = k} {A} newΓ up₁) ¬p stA = let ⟨ B* , st ⟩ = st-total A k B
  in S^ (∋:=-subst inΓ newΓ (≢-pred ¬p) st) (↑ty-st-comm1 z≤n st up₁ up stA)
∋:=-subst (S= inΓ up) ◀Z ¬p stA with ↑ty-st-eq up stA
... | refl = inΓ
∋:=-subst (S= {A = B} inΓ up) (◀S= {k = k} {A} newΓ up₁ x) ¬p stA = let ⟨ B* , st ⟩ = st-total A k B
  in S= (∋:=-subst inΓ newΓ (≢-pred ¬p) st) (↑ty-st-comm1 z≤n st up₁ up stA)

punchOut-≤-inject : (¬p : k₂ ≢ inject₁ k₁)
                  → k₁ #< k₂
                  → punchOut ¬p ≡ k₁
punchOut-≤-inject {k₂ = #S k₂} {k₁ = #0} ¬p lt = refl
punchOut-≤-inject {k₂ = #S k₂} {k₁ = #S k₁} ¬p (s≤s lt) = cong #S (punchOut-≤-inject (λ x → ¬p (cong #S x)) lt)

ε-st : inject₁ k₁ ε A
     → k₁ #< k₂
     → ⟦ k₂ / T ⟧ A ⇘ A*
     → k₁ ε A*
ε-st ε-var lt (st-var stx-eq) = ⊥-elim (helper lt)
  where helper : k₁ #< inject₁ k₁ → ⊥
        helper {k₁ = #0} = λ ()
        helper {k₁ = #S k₁} (s≤s lt) = helper lt
ε-st ε-var lt (st-var (stx-neq ¬p)) rewrite punchOut-≤-inject ¬p lt = ε-var
ε-st (ε-arr-l inA) lt (st-arr st st₁) = ε-arr-l (ε-st inA lt st)
ε-st (ε-arr-r inA) lt (st-arr st st₁) = ε-arr-r (ε-st inA lt st₁)
ε-st (ε-∀ inA) lt (st-∀ up st) = ε-∀ (ε-st inA (s≤s lt) st)

{-
helper : ¬ (inject₁ k₁ ε A)
       → ⟦ k₂ / T ⟧ A ⇘ A*
       → k₁ #< k₂
       → ¬ (k₁ ε A*)
helper ninA (st-var stx-eq) lt ε-var = {!!}
helper ninA (st-var (stx-neq ¬p)) lt ε-var = {!!}
helper ninA st lt (ε-arr-l inA*) = {!!}
helper ninA st lt (ε-arr-r inA*) = {!!}
helper ninA st lt (ε-∀ inA*) = {!!}
-}

{-

shifted-lt : Shifted T k₁
           → T ↑ty k₂ ⇘ T'
           → k₂ #≤ k₁
           → Shifted T' (#S k₁)

find-st : ∀ {A : Type (2 + m)} {k₁ k₂ j A* T}
        → find A (inject₁ k₁) j
        → k₁ #< k₂
        → Shifted T k₁
        → ⟦ k₂ / T ⟧ A ⇘ A*
        → find A* k₁ j
find-st (f-∞ x) lt upT st = f-∞ (ε-st x lt st)
find-st (f-arr-𝕚-l x) lt upT (st-arr st st₁) = f-arr-𝕚-l (ε-st x lt st)
find-st (f-arr-𝕚-r fd) lt upT (st-arr st st₁) = f-arr-𝕚-r (find-st fd lt upT st₁)
find-st (f-arr-𝕔 ¬inA fd) lt upT (st-arr st st₁) = {!!}
find-st (f-∀ fd) lt upT (st-∀ up st) = f-∀ (find-st fd (s≤s lt) {!!} st)
-}


{-
find-st (f-∞ x) lt st = f-∞ (ε-st x lt st)
find-st (f-arr-𝕚-l x) lt (st-arr st st₁) = f-arr-𝕚-l (ε-st x lt st)
find-st (f-arr-𝕚-r fd) lt (st-arr st st₁) = f-arr-𝕚-r (find-st fd lt st₁)
find-st (f-arr-𝕔 ¬inA fd) lt (st-arr st st₁) = f-arr-𝕔 {!!} (find-st fd lt st₁)
find-st (f-∀ fd) lt (st-∀ up st) = f-∀ (find-st fd (s≤s lt) st)
-}
