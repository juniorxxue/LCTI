module Implicit.SoundIntermAux2 where

open import Implicit.Language hiding (_≤_)

infix 3 _¬εᵍ_
data _¬εᵍ_ : Fin m → Env n m → Set where
  Z : k ¬εᵍ ∅
  Z^ : #0 ¬εᵍ Γ ,^
  Z∙ : #0 ¬εᵍ Γ ,∙
  Z= : ↑ty0 A ⇘ A'
     → ¬ (#0 ε A')
     → #0 ¬εᵍ Γ ,= A
  S, : ¬ (k ε A)
       → k ¬εᵍ Γ
       → k ¬εᵍ Γ , A
  S∙ : k ¬εᵍ Γ
     → #S k ¬εᵍ Γ ,∙
  S^ : k ¬εᵍ Γ
     → #S k ¬εᵍ Γ ,^
  S= : k ¬εᵍ Γ
     → ↑ty0 A ⇘ A'
     → ¬ (#S k ε A')
     → #S k ¬εᵍ Γ ,= A

----------------------------------------------------------------------
--+                     replacement properties                     +--
----------------------------------------------------------------------

∙⟹-:=-eq : Γ ∋ X := A₁
          → [ B / k ] Γ ∙⟹ Γ'
          → Γ' ∋ X := A₂
          → A₁ ≡ A₂
∙⟹-:=-eq (Z up) (∙⟹=S newΓ up1) (Z up₁) = ↑ty-unique up up₁
∙⟹-:=-eq (S, in1) (∙⟹,S newΓ) (S, in2) = ∙⟹-:=-eq in1 newΓ in2
∙⟹-:=-eq (S∙ in1 up) (∙⟹^0 up₁) (S= in2 up₂) with ∋:=-unique in1 in2
... | refl = ↑ty-unique up up₂
∙⟹-:=-eq (S∙ in1 up) (∙⟹∙S newΓ up1) (S∙ in2 up₁) with ∙⟹-:=-eq in1 newΓ in2
... | refl = ↑ty-unique up up₁
∙⟹-:=-eq (S^ in1 up) (∙⟹^S newΓ up1) (S^ in2 up₁) with ∙⟹-:=-eq in1 newΓ in2
... | refl = ↑ty-unique up up₁
∙⟹-:=-eq (S= in1 up) (∙⟹=S newΓ up1) (S= in2 up₁) with ∙⟹-:=-eq in1 newΓ in2
... | refl = ↑ty-unique up up₁

∙⟹-:=-∙-false : Γ ∋ X := A
               → [ B / k ] Γ ∙⟹ Γ'
               → Γ' ∋∙ X
               → ⊥
∙⟹-:=-∙-false (Z up) (∙⟹=S newΓ' up1) ()
∙⟹-:=-∙-false (S, inΓ) (∙⟹,S newΓ') (S, inΓ') = ∙⟹-:=-∙-false inΓ newΓ' inΓ'
∙⟹-:=-∙-false (S∙ inΓ up) (∙⟹^0 up₁) (S= inΓ') = ∙∈-:=∈-false inΓ' inΓ
∙⟹-:=-∙-false (S∙ inΓ up) (∙⟹∙S newΓ' up1) (S∙ inΓ') = ∙⟹-:=-∙-false inΓ newΓ' inΓ'
∙⟹-:=-∙-false (S^ inΓ up) (∙⟹^S newΓ' up1) (S^ inΓ') = ∙⟹-:=-∙-false inΓ newΓ' inΓ'
∙⟹-:=-∙-false (S= inΓ up) (∙⟹=S newΓ' up1) (S= inΓ') = ∙⟹-:=-∙-false inΓ newΓ' inΓ'

∙⟹-∙-:=-eq : Γ ∋∙ k
            → [ B / k ] Γ ∙⟹ Γ'
            → Γ' ∋ k := A
            → A ≡ B
∙⟹-∙-:=-eq Z (∙⟹^0 up) (Z up₁) = ↑ty-unique up₁ up
∙⟹-∙-:=-eq (S, inΓ) (∙⟹,S newΓ) (S, inΓ') = ∙⟹-∙-:=-eq inΓ newΓ inΓ'
∙⟹-∙-:=-eq (S∙ inΓ) (∙⟹∙S newΓ up1) (S∙ inΓ' up) with ∙⟹-∙-:=-eq inΓ newΓ inΓ'
... | refl = ↑ty-unique up up1
∙⟹-∙-:=-eq (S= inΓ) (∙⟹=S newΓ up1) (S= inΓ' up) with ∙⟹-∙-:=-eq inΓ newΓ inΓ'
... | refl = ↑ty-unique up up1
∙⟹-∙-:=-eq (S^ inΓ) (∙⟹^S newΓ up1) (S^ inΓ' up) with ∙⟹-∙-:=-eq inΓ newΓ inΓ'
... | refl = ↑ty-unique up up1

∙⟹-∙-:=-neq-false : Γ ∋∙ X
                   → [ B / k ] Γ ∙⟹ Γ'
                   → Γ' ∋ X := A
                   → k ≢ X
                   → ⊥
∙⟹-∙-:=-neq-false Z (∙⟹^0 up) inΓ' neq = neq refl
∙⟹-∙-:=-neq-false (S, inΓ) (∙⟹,S newΓ) (S, inΓ') neq = ∙⟹-∙-:=-neq-false inΓ newΓ inΓ' neq
∙⟹-∙-:=-neq-false (S∙ inΓ) (∙⟹^0 up) (S= inΓ' up₁) neq = ∙∈-:=∈-false inΓ inΓ'
∙⟹-∙-:=-neq-false (S∙ inΓ) (∙⟹∙S newΓ up1) (S∙ inΓ' up) neq = ∙⟹-∙-:=-neq-false inΓ newΓ inΓ' (≢-pred neq)
∙⟹-∙-:=-neq-false (S= inΓ) (∙⟹=S newΓ up1) (S= inΓ' up) neq = ∙⟹-∙-:=-neq-false inΓ newΓ inΓ' (≢-pred neq)
∙⟹-∙-:=-neq-false (S^ inΓ) (∙⟹^S newΓ up1) (S^ inΓ' up) neq = ∙⟹-∙-:=-neq-false inΓ newΓ inΓ' (≢-pred neq)

∙⟹-∙-eq-false : Γ ∋∙ k
               → [ A / k ] Γ ∙⟹ Γ'
               → Γ' ∋∙ k
               → ⊥
∙⟹-∙-eq-false Z (∙⟹^0 up) ()
∙⟹-∙-eq-false (S, inΓ) (∙⟹,S newΓ) (S, inΓ') = ∙⟹-∙-eq-false inΓ newΓ inΓ'
∙⟹-∙-eq-false (S∙ inΓ) (∙⟹∙S newΓ up1) (S∙ inΓ') = ∙⟹-∙-eq-false inΓ newΓ inΓ'
∙⟹-∙-eq-false (S= inΓ) (∙⟹=S newΓ up1) (S= inΓ') = ∙⟹-∙-eq-false inΓ newΓ inΓ'
∙⟹-∙-eq-false (S^ inΓ) (∙⟹^S newΓ up1) (S^ inΓ') = ∙⟹-∙-eq-false inΓ newΓ inΓ'

----------------------------------------------------------------------
--+                       shift and shifted                        +--
----------------------------------------------------------------------

↑ty-punchOut : (¬p : k ≢ X)
             → ‶ punchOut ¬p ↑ty k ⇘ ‶ X
↑ty-punchOut ¬p = helper ¬p (sym (punchIn-punchOut ¬p))
  where helper : (¬p : k ≢ X)
               → X ≡ punchIn k (punchOut ¬p)
               → ‶ punchOut ¬p ↑ty k ⇘ ‶ X
        helper ¬p eq with punchOut ¬p
        helper ¬p refl | Y = ↑ty-var

shifted-st-↑ty : Shifted A k
               → ⟦ k / B ⟧ A ⇘ A*
               → A* ↑ty k ⇘ A
shifted-st-↑ty sfd-int st-int = ↑ty-int
shifted-st-↑ty (sfd-var x) (st-var stx-eq) = ⊥-elim (x refl)
shifted-st-↑ty (sfd-var x) (st-var (stx-neq ¬p)) = ↑ty-punchOut ¬p
shifted-st-↑ty (sfd-arr sd sd₁) (st-arr st st₁) = ↑ty-arr (shifted-st-↑ty sd st) (shifted-st-↑ty sd₁ st₁)
shifted-st-↑ty (sfd-∀ sd) (st-∀ up st) = ↑ty-∀ (shifted-st-↑ty sd st)

εᵍ-false : Γ ∋ X := A
         → k ε A
         → k ¬εᵍ Γ
         → ⊥
εᵍ-false (Z up) inA (Z= x x₁) with ↑ty-unique up x
... | refl = x₁ inA
εᵍ-false (Z up) inA (S= ninΓ x x₁) with ↑ty-unique up x
... | refl = x₁ inA
εᵍ-false (S, inΓ) inA (S, x ninΓ) = εᵍ-false inΓ inA ninΓ
εᵍ-false (S∙ inΓ up) inA Z∙ = ↑ty-ε-false up inA
εᵍ-false (S∙ inΓ up) inA (S∙ ninΓ) = εᵍ-false inΓ (↑ty-ε-≤ inA up z≤n) ninΓ
εᵍ-false (S^ inΓ up) inA Z^ = ↑ty-ε-false up inA
εᵍ-false (S^ inΓ up) inA (S^ ninΓ) = εᵍ-false inΓ (↑ty-ε-≤ inA up z≤n) ninΓ
εᵍ-false (S= inΓ up) inA (Z= x x₁) = ↑ty-ε-false up inA
εᵍ-false (S= inΓ up) inA (S= ninΓ x x₁) = εᵍ-false inΓ (↑ty-ε-≤ inA up z≤n) ninΓ

¬ε-shifted : ¬ (k ε A)
           → Shifted A k
¬ε-shifted {A = Int} nin = sfd-int
¬ε-shifted {A = ‶ X} nin = sfd-var (helper nin)
  where helper : ¬ (k ε ‶ X)
               →  X ≢ k
        helper nin refl = nin ε-var
¬ε-shifted {A = A `→ A₁} nin = sfd-arr (¬ε-shifted (λ z → nin (ε-arr-l z)))
                                       (¬ε-shifted (λ z → nin (ε-arr-r z)))
¬ε-shifted {A = `∀ A} nin = sfd-∀ (¬ε-shifted (λ z → nin (ε-∀ z)))

εᵍ-shifted : k ¬εᵍ Γ
           → Γ ∋ X := A
           → Shifted A k
εᵍ-shifted ninΓ inΓ = ¬ε-shifted (λ x → εᵍ-false inΓ x ninΓ)

----------------------------------------------------------------------
--+                           main lemma                           +--
----------------------------------------------------------------------

late-ap-gen' : ∀ {A%* A%*'}
             → Γ ≫ A ⇘ A%
             → k ¬εᵍ Γ -- if we model ∙⟹, as two insertions, we could have this property implicitly.
             → ⟦ k / B ⟧ A% ⇘ A%*
             → B ↑ty k ⇘ B'
             → [ B' / k ] Γ ∙⟹ Γ'
             → Γ' ≫ A ⇘ A%*'
             → A%* ↑ty k ⇘ A%*'
late-ap-gen' ap-int ninΓ st-int upB newΓ ap-int = ↑ty-int
late-ap-gen' (ap-var= x) ninΓ stA% upB newΓ (ap-var= x₁) with ∙⟹-:=-eq x newΓ x₁
... | refl = shifted-st-↑ty (εᵍ-shifted ninΓ x) stA%
late-ap-gen' (ap-var= x) ninΓ stA% upB newΓ (ap-var∙ x₁) = ⊥-elim (∙⟹-:=-∙-false x newΓ x₁)
late-ap-gen' (ap-var∙ x) ninΓ (st-var stx-eq) upB newΓ (ap-var= x₁) with ∙⟹-∙-:=-eq x newΓ x₁
... | refl = upB
late-ap-gen' (ap-var∙ x) ninΓ (st-var (stx-neq ¬p)) upB newΓ (ap-var= x₁) = ⊥-elim (∙⟹-∙-:=-neq-false x newΓ x₁ ¬p)
late-ap-gen' (ap-var∙ x) ninΓ (st-var stx-eq) upB newΓ (ap-var∙ x₁) = ⊥-elim (∙⟹-∙-eq-false x newΓ x₁)
late-ap-gen' (ap-var∙ x) ninΓ (st-var (stx-neq ¬p)) upB newΓ (ap-var∙ x₁) = ↑ty-punchOut ¬p
late-ap-gen' (ap-arr apA apA₁) ninΓ (st-arr stA% stA%₁) upB newΓ (ap-arr apA' apA'') = ↑ty-arr (late-ap-gen' apA ninΓ stA% upB newΓ apA')
                                                                                               (late-ap-gen' apA₁ ninΓ stA%₁ upB newΓ apA'')
late-ap-gen' {B' = B'} (ap-∀ apA) ninΓ (st-∀ up stA%) upB newΓ (ap-∀ apA') =
   let ⟨ B'' , upB' ⟩ = ↑ty0-total B' in ↑ty-∀ (late-ap-gen' apA (S∙ ninΓ) stA% (↑ty-comm' z≤n upB upB' up) (∙⟹∙S newΓ upB') apA')

late-ap : ∀ {A%* A%*'}
        → Γ ,∙ ≫ A ⇘ A%
        → ⟦ B ⟧ A% ⇘ A%*
        → Γ ,= B ≫ A ⇘ A%*'
        → ↑ty0 A%* ⇘ A%*'
late-ap {B = B} apA stA% apA' =
  let ⟨ B' , upB ⟩ = ↑ty0-total B
--  in late-ap-gen apA stA% upB (∙⟹^0 upB) apA'
  in late-ap-gen' apA Z∙ stA% upB (∙⟹^0 upB) apA'
