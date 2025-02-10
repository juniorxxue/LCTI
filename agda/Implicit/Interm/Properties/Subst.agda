module Implicit.Interm.Properties.Subst where

open import Implicit.Language.All
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.OpenClose
open import Implicit.Interm.Properties.Subtyping
open import Implicit.Interm.Properties.SubstAux

◀=-closedT : Γ ◀ k := T ⇘ Γ*
          → Closed Γ
          → Γ* ⊢c T
◀=-closedT ◀Z (clo-S= cloΓ cloA) = cloA
◀=-closedT (◀S, newΓ x) (clo-S, cloΓ cloA) = ⊢c-weaken,0 (◀=-closedT newΓ cloΓ) (⊢c-subst cloA newΓ (◀=-closedT newΓ cloΓ) x)
◀=-closedT (◀S^ newΓ up) (clo-S^ cloΓ) = ⊢c-weaken^0 (◀=-closedT newΓ cloΓ) up
◀=-closedT (◀S∙ newΓ up) (clo-S∙ cloΓ) = ⊢c-weaken∙0 (◀=-closedT newΓ cloΓ) up
◀=-closedT (◀S= newΓ up x) (clo-S= cloΓ cloA) = ⊢c-weaken=0 (◀=-closedT newΓ cloΓ) up (⊢c-subst cloA newΓ (◀=-closedT newΓ cloΓ) x)

◀=-closed : Closed Γ
         → Γ ◀ k := T ⇘ Γ*
         → Closed Γ*
◀=-closed (clo-S, cloΓ cloA) (◀S, newΓ x) = clo-S, (◀=-closed cloΓ newΓ) (⊢c-subst cloA newΓ (◀=-closedT newΓ cloΓ) x)
◀=-closed (clo-S∙ cloΓ) (◀S∙ newΓ up) = clo-S∙ (◀=-closed cloΓ newΓ)
◀=-closed (clo-S^ cloΓ) (◀S^ newΓ up) = clo-S^ (◀=-closed cloΓ newΓ)
◀=-closed (clo-S= cloΓ cloA) ◀Z = cloΓ
◀=-closed (clo-S= cloΓ cloA) (◀S= newΓ up x) = clo-S= (◀=-closed cloΓ newΓ) (⊢c-subst cloA newΓ (◀=-closedT newΓ cloΓ) x)

◀=-imply-∋:= : Γ ◀ k := T ⇘ Γ*
             → T ↑ty k ⇘ T'
             → Γ ∋ k := T'
◀=-imply-∋:= ◀Z up = Z up
◀=-imply-∋:= (◀S, inΓ x) up = S, (◀=-imply-∋:= inΓ up)
◀=-imply-∋:= (◀S^ {k = k} {A} inΓ up₁) up with ↑ty-total A k
... | ⟨ A' , upA ⟩ = S^ (◀=-imply-∋:= inΓ upA) (↑ty-comm z≤n up₁ up upA)
◀=-imply-∋:= (◀S∙ {k = k} {A} inΓ up₁) up with ↑ty-total A k
... | ⟨ A' , upA ⟩ = S∙ (◀=-imply-∋:= inΓ upA) (↑ty-comm z≤n up₁ up upA)
◀=-imply-∋:= (◀S= {k = k} {A} inΓ up₁ x) up with ↑ty-total A k
... | ⟨ A' , upA ⟩ = S= (◀=-imply-∋:= inΓ upA) (↑ty-comm z≤n up₁ up upA)

s-subst : Γ ⊢ j # A ≤ B
        → Γ ◀ k := T ⇘ Γ*
        → ⟦ k / T ⟧ A ⇘ A*
        → ⟦ k / T ⟧ B ⇘ B*
        → Γ* ⊢ j # A* ≤ B*
s-subst (s-refl cloΓ cloA) newΓ stA stB with st-unique stA stB
... | refl = s-refl (◀=-closed cloΓ newΓ) (⊢c-subst cloA newΓ (◀=-closedT newΓ cloΓ) stA)
s-subst (s-int cloΓ) newΓ st-int st-int = s-int (◀=-closed cloΓ newΓ)
s-subst (s-var-∙ cloΓ inΓ) newΓ (st-var stx) (st-var stx₁) with stx-unique stx stx₁
... | refl = s-refl-∞ (◀=-closed cloΓ newΓ) (⊢c-subst (⊢c-var-∙ inΓ) newΓ (◀=-closedT newΓ cloΓ) (st-var stx))
s-subst (s-var-= cloΓ inΓ) newΓ (st-var stx) (st-var stx₁) with stx-unique stx stx₁
... | refl = s-refl-∞ (◀=-closed cloΓ newΓ) (⊢c-subst (⊢c-var-= inΓ) newΓ (◀=-closedT newΓ cloΓ) (st-var stx))
s-subst (s-arr₁ s s₁) newΓ (st-arr stA stA₁) (st-arr stB stB₁) = s-arr₁ (s-subst s newΓ stB stA) (s-subst s₁ newΓ stA₁ stB₁)
s-subst (s-arr₂ s s₁) newΓ (st-arr stA stA₁) (st-arr stB stB₁) = s-arr₂ (s-subst s newΓ stB stA) (s-subst s₁ newΓ stA₁ stB₁)
s-subst (s-arr₃ cloA s) newΓ (st-arr stA stA₁) (st-arr stB stB₁) with st-unique stA stB
... | refl = s-arr₃ (⊢c-subst cloA newΓ (◀=-closedT newΓ (s-closed s)) stA) (s-subst s newΓ stA₁ stB₁)
s-subst (s-∀ s) newΓ (st-∀ up stA) (st-∀ up₁ stB) with ↑ty-unique up up₁
... | refl = s-∀ (s-subst s (◀S∙ newΓ up) stA stB)
s-subst {k = k} {T} (s-∀l {B = B} {C = C} {D = D} s ic fd st₁ st₂) newΓ (st-∀ {A' = A'} up stA) (st-arr stB stB₁)
  with st-total T k B | st-total A' (#S k) C | st-total A' (#S k) D
... | ⟨ B* , stB' ⟩ | ⟨ C* , stC ⟩ | ⟨ D* , stD ⟩ = s-∀l (s-subst s (◀S= newΓ up stB') stA (st-arr stC stD)) ic
  (find-st0 fd up stA)
  (st-st-comm z≤n st₁ stB up stC stB')
  (st-st-comm z≤n st₂ stB₁ up stD stB')
-- var-l
s-subst {k = k} {T = T} (s-var-l inΓ s) newΓ (st-var stx-eq) stB with ↑ty-total T k
... | ⟨ T' , upT ⟩ with ◀=-imply-∋:= newΓ upT
... | r rewrite ∋:=-unique r inΓ = s-subst s newΓ (↑ty-st upT) stB
s-subst {k = k} {T} (s-var-l {B = B} inΓ s) newΓ (st-var (stx-neq ¬p)) stB = let ⟨ B* , stB' ⟩ = st-total T k B
  in s-var-l (∋:=-subst inΓ newΓ ¬p stB') (s-subst s newΓ stB' stB)
-- var-r
s-subst {k = k} {T = T} (s-var-r inΓ s) newΓ stA (st-var stx-eq) with ↑ty-total T k
... | ⟨ T' , upT ⟩ with ◀=-imply-∋:= newΓ upT
... | r rewrite ∋:=-unique r inΓ = s-subst s newΓ stA (↑ty-st upT)
s-subst {k = k} {T} (s-var-r {B = B} inΓ s) newΓ stA (st-var (stx-neq ¬p)) = let ⟨ B* , stB' ⟩ = st-total T k B
  in s-var-r (∋:=-subst inΓ newΓ ¬p stB') (s-subst s newΓ stA stB')

s-subst0 : Γ ,= T ⊢ j # A ≤ B
         → ⟦ T ⟧ A ⇘ A*
         → ⟦ T ⟧ B ⇘ B*
         → Γ ⊢ j # A* ≤ B*
s-subst0 s stA stB = s-subst s ◀Z stA stB

t-subst : Γ ⊢ j # e ⦂ A
        → Γ ◀ k := T ⇘ Γ*
        → ⟦ k / T ⟧ᵉ e ⇘ e*
        → ⟦ k / T ⟧ A ⇘ A*
        → Γ* ⊢ j # e* ⦂ A*
t-subst (⊢lit cloΣ) newΓ st-lit st-int = ⊢lit (◀=-closed cloΣ newΓ)
t-subst (⊢var cloΣ x∈Γ) newΓ st-var stA = ⊢var (◀=-closed cloΣ newΓ) (∋⦂-subst x∈Γ newΓ stA)
t-subst (⊢ann ⊢e) newΓ (st-⦂ ste st) stA with st-unique st stA
... | refl = ⊢ann (t-subst ⊢e newΓ ste st)
t-subst (⊢lam₁ ⊢e) newΓ (st-ƛ ste) (st-arr stA stA₁) = ⊢lam₁ (t-subst ⊢e (◀S, newΓ stA) ste stA₁)
t-subst (⊢lam₂ ⊢e) newΓ (st-ƛ ste) (st-arr stA stA₁) = ⊢lam₂ (t-subst ⊢e (◀S, newΓ stA) ste stA₁)
t-subst {k = k} {T} (⊢app₁ {A = A} ⊢e ⊢e₁) newΓ (st-· ste ste₁) stA with st-total T k A
... | ⟨ A* , st' ⟩ = ⊢app₁ (t-subst ⊢e newΓ ste (st-arr st' stA)) (t-subst ⊢e₁ newΓ ste₁ st')
t-subst {k = k} {T} (⊢app₂ {A = A} ⊢e ⊢e₁) newΓ (st-· ste ste₁) stA with st-total T k A
... | ⟨ A* , st' ⟩ = ⊢app₂ (t-subst ⊢e newΓ ste (st-arr st' stA)) (t-subst ⊢e₁ newΓ ste₁ st')
t-subst {k = k} {T} (⊢sub {A = A} ⊢e B≤A j≢Z) newΓ ste stA with st-total T k A
... | ⟨ A* , st' ⟩ = ⊢sub (t-subst ⊢e newΓ ste st') (s-subst B≤A newΓ st' stA) j≢Z
t-subst (⊢tabs ⊢e) newΓ (st-Λ ste up') (st-∀ up stA) with ↑ty-unique up up'
... | refl = ⊢tabs (t-subst ⊢e (◀S∙ newΓ up) ste stA)

t-subst0 : Γ ,= T ⊢ j # e ⦂ A
         → ⟦ T ⟧ᵉ e ⇘ e*
         → ⟦ T ⟧ A ⇘ A*
         → Γ ⊢ j # e* ⦂ A*
t-subst0 ⊢e st-e stA = t-subst ⊢e ◀Z st-e stA
