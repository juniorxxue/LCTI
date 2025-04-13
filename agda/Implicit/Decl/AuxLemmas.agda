module Implicit.Decl.AuxLemmas where

open import Implicit.Language.All
open import Implicit.Decl.Subtyping renaming (_⊢_#_⌞_⌝_ to _⊢¹_#_⌞_⌝_)
open import Implicit.Decl.SubtypingV2 renaming (_⊢_#_⌞_⌝_ to _⊢²_#_⌞_⌝_)


infix 3 [_/_]_∙⟹_
data [_/_]_∙⟹_ : Type m → Fin m → Env n m → Env n m → Set where
  ∙⟹^0 : (up : ↑ty0 A ⇘ A')
         → (regA : Γ ⊢r A)
         → [ A' / #0 ] (Γ ,∙) ∙⟹ (Γ ,= A)

  ∙⟹^S : [ A / k ] Γ ∙⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,^) ∙⟹ Γ' ,^

  ∙⟹∙S : [ A / k ] Γ ∙⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,∙) ∙⟹ (Γ' ,∙)

  ∙⟹,S : [ A / k ] Γ ∙⟹ Γ'
       → [ A / k ] (Γ , B) ∙⟹ (Γ' , B)

  ∙⟹=S : [ A / k ] Γ ∙⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,= B) ∙⟹ (Γ' ,= B)


∙⟹-∋∙ : Γ ∋∙ X
        → X ≢ k
        → [ T / k ] Γ ∙⟹ Γ'
        → Γ' ∋∙ X
∙⟹-∋∙ Z neq (∙⟹^0 up regA) = ⊥-elim (neq refl)
∙⟹-∋∙ Z neq (∙⟹∙S new up1) = Z
∙⟹-∋∙ (S, inΓ) neq (∙⟹,S new) = S, (∙⟹-∋∙ inΓ neq new)
∙⟹-∋∙ (S∙ inΓ) neq (∙⟹^0 up regA) = S= inΓ
∙⟹-∋∙ (S∙ inΓ) neq (∙⟹∙S new up1) = S∙ (∙⟹-∋∙ inΓ (≢-pred neq) new)
∙⟹-∋∙ (S= inΓ) neq (∙⟹=S new up1) = S= (∙⟹-∋∙ inΓ (≢-pred neq) new)
∙⟹-∋∙ (S^ inΓ) neq (∙⟹^S new up1) = S^ (∙⟹-∋∙ inΓ (≢-pred neq) new)


∙⟹-⊢r : Γ ⊢r A
      → [ T / k ] Γ ∙⟹ Γ'
      → k ¬ε A
      → Γ' ⊢r A
∙⟹-⊢r ⊢r-int new ¬ε-int = ⊢r-int
∙⟹-⊢r (⊢r-var-∙ inΓ) new (¬ε-var x) = ⊢r-var-∙ (∙⟹-∋∙ inΓ x new)
∙⟹-⊢r (⊢r-arr regA regA₁) new (¬ε-arr ninA ninA₁) = ⊢r-arr (∙⟹-⊢r regA new ninA) (∙⟹-⊢r regA₁ new ninA₁)
∙⟹-⊢r {T = T} (⊢r-∀ regA) new (¬ε-∀ ninA)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢r-∀ (∙⟹-⊢r regA (∙⟹∙S new upT) ninA)


∙⟹-∋:=-prv : Γ ∋ X := A
       → [ T / k ] Γ ∙⟹ Γ'
       → Γ' ∋ X := A
∙⟹-∋:=-prv (Z up) (∙⟹=S new up1) = Z up
∙⟹-∋:=-prv (S∙ inΓ up) (∙⟹^0 up₁ regA) = S= inΓ up
∙⟹-∋:=-prv (S∙ inΓ up) (∙⟹∙S new up1) = S∙ (∙⟹-∋:=-prv inΓ new) up
∙⟹-∋:=-prv (S^ inΓ up) (∙⟹^S new up1) = S^ (∙⟹-∋:=-prv inΓ new) up
∙⟹-∋:=-prv (S= inΓ up) (∙⟹=S new up1) = S= (∙⟹-∋:=-prv inΓ new) up
∙⟹-∋:=-prv (S, inΓ) (∙⟹,S new) = S, (∙⟹-∋:=-prv inΓ new)

∙⟹-∋:= : [ T / k ] Γ ∙⟹ Γ'
         → Γ' ∋ k := T
∙⟹-∋:= (∙⟹^0 up regA) = Z up
∙⟹-∋:= (∙⟹^S new up1) = S^ (∙⟹-∋:= new) up1
∙⟹-∋:= (∙⟹∙S new up1) = S∙ (∙⟹-∋:= new) up1
∙⟹-∋:= (∙⟹,S new) = S, (∙⟹-∋:= new)
∙⟹-∋:= (∙⟹=S new up1) = S= (∙⟹-∋:= new) up1


∙⟹-∋∙-neq : Γ ∋∙ X
          → [ T' / k ] Γ ∙⟹ Γ'
          → Γ' ∋∙ X
          → k ≢ X
∙⟹-∋∙-neq Z (∙⟹∙S new up1) Z = λ ()
∙⟹-∋∙-neq (S, inΓ) (∙⟹,S new) (S, inΓ') = ∙⟹-∋∙-neq inΓ new inΓ'
∙⟹-∋∙-neq (S∙ inΓ) (∙⟹^0 up regA) (S= inΓ') = λ ()
∙⟹-∋∙-neq (S∙ inΓ) (∙⟹∙S new up1) (S∙ inΓ') = ≢-suc (∙⟹-∋∙-neq inΓ new inΓ')
∙⟹-∋∙-neq (S= inΓ) (∙⟹=S new up1) (S= inΓ') = ≢-suc (∙⟹-∋∙-neq inΓ new inΓ')
∙⟹-∋∙-neq (S^ inΓ) (∙⟹^S new up1) (S^ inΓ') = ≢-suc (∙⟹-∋∙-neq inΓ new inΓ')


∙⟹-:=-eq : Γ ∋ X := A₁
          → [ B / k ] Γ ∙⟹ Γ'
          → Γ' ∋ X := A₂
          → A₁ ≡ A₂
∙⟹-:=-eq (Z up) (∙⟹=S newΓ up1) (Z up₁) = ↑ty-unique up up₁
∙⟹-:=-eq (S, in1) (∙⟹,S newΓ) (S, in2) = ∙⟹-:=-eq in1 newΓ in2
∙⟹-:=-eq (S∙ in1 up) (∙⟹^0 reg up₁) (S= in2 up₂) with ∋:=-unique in1 in2
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
∙⟹-:=-∙-false (S∙ inΓ up) (∙⟹^0 reg up₁) (S= inΓ') = ∋∙-∋:=-false inΓ' inΓ
∙⟹-:=-∙-false (S∙ inΓ up) (∙⟹∙S newΓ' up1) (S∙ inΓ') = ∙⟹-:=-∙-false inΓ newΓ' inΓ'
∙⟹-:=-∙-false (S^ inΓ up) (∙⟹^S newΓ' up1) (S^ inΓ') = ∙⟹-:=-∙-false inΓ newΓ' inΓ'
∙⟹-:=-∙-false (S= inΓ up) (∙⟹=S newΓ' up1) (S= inΓ') = ∙⟹-:=-∙-false inΓ newΓ' inΓ'

∙⟹-∙-:=-eq : Γ ∋∙ k
            → [ B / k ] Γ ∙⟹ Γ'
            → Γ' ∋ k := A
            → A ≡ B
∙⟹-∙-:=-eq Z (∙⟹^0 reg up) (Z up₁) = ↑ty-unique up₁ reg
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
∙⟹-∙-:=-neq-false Z (∙⟹^0 up reg) inΓ' neq = neq refl
∙⟹-∙-:=-neq-false (S, inΓ) (∙⟹,S newΓ) (S, inΓ') neq = ∙⟹-∙-:=-neq-false inΓ newΓ inΓ' neq
∙⟹-∙-:=-neq-false (S∙ inΓ) (∙⟹^0 up reg) (S= inΓ' up₁) neq = ∋∙-∋:=-false inΓ inΓ'
∙⟹-∙-:=-neq-false (S∙ inΓ) (∙⟹∙S newΓ up1) (S∙ inΓ' up) neq = ∙⟹-∙-:=-neq-false inΓ newΓ inΓ' (≢-pred neq)
∙⟹-∙-:=-neq-false (S= inΓ) (∙⟹=S newΓ up1) (S= inΓ' up) neq = ∙⟹-∙-:=-neq-false inΓ newΓ inΓ' (≢-pred neq)
∙⟹-∙-:=-neq-false (S^ inΓ) (∙⟹^S newΓ up1) (S^ inΓ' up) neq = ∙⟹-∙-:=-neq-false inΓ newΓ inΓ' (≢-pred neq)

∙⟹-∙-eq-false : Γ ∋∙ k
               → [ A / k ] Γ ∙⟹ Γ'
               → Γ' ∋∙ k
               → ⊥
∙⟹-∙-eq-false Z (∙⟹^0 up reg) ()
∙⟹-∙-eq-false (S, inΓ) (∙⟹,S newΓ) (S, inΓ') = ∙⟹-∙-eq-false inΓ newΓ inΓ'
∙⟹-∙-eq-false (S∙ inΓ) (∙⟹∙S newΓ up1) (S∙ inΓ') = ∙⟹-∙-eq-false inΓ newΓ inΓ'
∙⟹-∙-eq-false (S= inΓ) (∙⟹=S newΓ up1) (S= inΓ') = ∙⟹-∙-eq-false inΓ newΓ inΓ'
∙⟹-∙-eq-false (S^ inΓ) (∙⟹^S newΓ up1) (S^ inΓ') = ∙⟹-∙-eq-false inΓ newΓ inΓ'
