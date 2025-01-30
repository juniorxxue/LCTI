module Implicit.Interm.Properties.SubstAux where

open import Implicit.Language
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.OpenClose


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

∋⦂-subst : Γ ∋ x ⦂ A
         → Γ ◀ k := T ⇘ Γ*
         → ⟦ k / T ⟧ A ⇘ A*
         → Γ* ∋ x ⦂ A*
∋⦂-subst Z (◀S, newΓ x) st with st-unique st x
... | refl = Z
∋⦂-subst (S, inΓ) (◀S, newΓ x) st = S, (∋⦂-subst inΓ newΓ st)
∋⦂-subst (S∙ {A = A'} inΓ up) (◀S∙ {k = k} {A} newΓ up₁) st with st-total A k A'
... | ⟨ A'* , stA' ⟩ = S∙ (∋⦂-subst inΓ newΓ stA') (↑ty-st-comm1 z≤n stA' up₁ up st)
∋⦂-subst (S^ {A = A'} inΓ up) (◀S^ {k = k} {A} newΓ up₁) st with st-total A k A'
... | ⟨ A'* , stA' ⟩ = S^ (∋⦂-subst inΓ newΓ stA') (↑ty-st-comm1 z≤n stA' up₁ up st)
∋⦂-subst (S= inΓ up) ◀Z st rewrite ↑ty-st-eq up st = inΓ
∋⦂-subst (S= {A = A'} inΓ up) (◀S= {k = k} {A} newΓ up₁ x) st with st-total A k A'
... | ⟨ A'* , stA' ⟩ = S= (∋⦂-subst inΓ newΓ stA') (↑ty-st-comm1 z≤n stA' up₁ up st)


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

ε-shifted-false : Shifted A k
                → k ε A
                → ⊥
ε-shifted-false (sfd-var x) ε-var = x refl
ε-shifted-false (sfd-arr sd sd₁) (ε-arr-l inT) = ε-shifted-false sd inT
ε-shifted-false (sfd-arr sd sd₁) (ε-arr-r inT) = ε-shifted-false sd₁ inT
ε-shifted-false (sfd-∀ sd) (ε-∀ inT) = ε-shifted-false sd inT

#S-injective : #S k₁ ≡ #S k₂
             → k₁ ≡ k₂
#S-injective refl = refl

punchIn-≢ : k₁ ≢ k₂
          → punchIn k k₁ ≢ punchIn k k₂
punchIn-≢ {k₁ = k₁} {k₂} {#0} neq refl = neq refl
punchIn-≢ {k₁ = #0} {#0} {#S k} neq peq = neq refl
punchIn-≢ {k₁ = #S k₁} {#S k₂} {#S k} neq peq = punchIn-≢ (≢-pred neq) (#S-injective peq)


shifted-lt : Shifted T k₁
           → T ↑ty k₂ ⇘ T'
           → k₂ #≤ k₁
           → Shifted T' (#S k₁)
shifted-lt sfd-int ↑ty-int lt = sfd-int
shifted-lt (sfd-var x) ↑ty-var lt rewrite sym (punchIn-≤ lt) = sfd-var (punchIn-≢ x)
shifted-lt (sfd-arr sd sd₁) (↑ty-arr upT upT₁) lt = sfd-arr (shifted-lt sd upT lt) (shifted-lt sd₁ upT₁ lt)
shifted-lt (sfd-∀ sd) (↑ty-∀ upT) lt = sfd-∀ (shifted-lt sd upT (s≤s lt))

ε-var-neg : ¬ (k ε ‶ X)
          → X ≢ k
ε-var-neg noin refl = noin ε-var


find-¬ε : ¬ (inject₁ k₁ ε A)
       → ⟦ k₂ / T ⟧ A ⇘ A*
       → Shifted T k₁
       → k₁ #< k₂
       → ¬ (k₁ ε A*)
find-¬ε ninA (st-var stx-eq) sd lt inA* = ε-shifted-false sd inA*
find-¬ε ninA (st-var (stx-neq ¬p)) sd lt ε-var = helper ¬p (ε-var-neg ninA) lt
  where helper : ∀ {k : Fin (1 + m)} {X}
                → (¬p : k ≢ X)
                → X ≢ inject₁ (punchOut ¬p)
                → punchOut ¬p #< k
                → ⊥
        helper {m = suc m} {k = #S k} {X = #0} ¬p neq lt = neq refl
        helper {suc m} {k = #S k} {X = #S X} ¬p neq (s≤s lt) = helper {m} {k} {X} (≢-pred ¬p) (≢-pred neq) lt
find-¬ε ninA (st-arr st st₁) sd lt (ε-arr-l inA*) = find-¬ε (λ z → ninA (ε-arr-l z)) st sd lt inA*
find-¬ε ninA (st-arr st st₁) sd lt (ε-arr-r inA*) = find-¬ε (λ z → ninA (ε-arr-r z)) st₁ sd lt inA*
find-¬ε ninA (st-∀ up st) sd lt (ε-∀ inA*) = find-¬ε (λ z → ninA (ε-∀ z)) st (shifted-lt sd up z≤n) (s≤s lt) inA*


find-st : ∀ {A : Type (2 + m)} {k₁ k₂ j A* T}
        → find A (inject₁ k₁) j
        → k₁ #< k₂
        → Shifted T k₁
        → ⟦ k₂ / T ⟧ A ⇘ A*
        → find A* k₁ j
find-st (f-∞ x) lt upT st = f-∞ (ε-st x lt st)
find-st (f-arr-𝕚-l x) lt upT (st-arr st st₁) = f-arr-𝕚-l (ε-st x lt st)
find-st (f-arr-𝕚-r fd) lt upT (st-arr st st₁) = f-arr-𝕚-r (find-st fd lt upT st₁)
find-st (f-arr-𝕔 ¬inA fd) lt upT (st-arr st st₁) = f-arr-𝕔 (find-¬ε ¬inA st upT lt) (find-st fd lt upT st₁)
find-st (f-∀ fd) lt upT (st-∀ up st) = f-∀ (find-st fd (s≤s lt) (shifted-lt upT up z≤n) st)

find-st0 : find A #0 j
         → ↑ty0 T ⇘ T'
         → ⟦ #S k / T' ⟧ A ⇘ A*
         → find A* #0 j
find-st0 fd up st = find-st fd (s≤s z≤n) (↑ty-shifted up) st
