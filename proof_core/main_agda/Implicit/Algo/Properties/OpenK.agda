module Implicit.Algo.Properties.OpenK where

open import Implicit.Language.All
open import Implicit.Algo.Base

infix 3 _∤_⊢oˣ_
data _∤_⊢oˣ_ : Env n m → Fin (1 + m) → Fin m → Set where

  opnx= : Γ ∋= X
        → Γ ∤ k ⊢oˣ X

  opnx∙ : Γ ∋∙ X
        → Γ ∤ k ⊢oˣ X

  opnx^ : Γ ∋^ X
        → X #< k
        → Γ ∤ k ⊢oˣ X

infix 3 _∤_⊢o_
data _∤_⊢o_ : Env n m → Fin (1 + m) → Type m → Set where

  opn-int : Γ ∤ k ⊢o Int

  opn-var : Γ ∤ k ⊢oˣ X
          → Γ ∤ k ⊢o ‶ X

  opn-arr : Γ ∤ k ⊢o A
          → Γ ∤ k ⊢o B
          → Γ ∤ k ⊢o A `→ B

  opn-∀ : Γ ,∙ ∤ #S k ⊢o A
        → Γ ∤ k ⊢o `∀ A


⊢oˣ-∋^-#< : Γ ∤ k ⊢oˣ X
          → Γ ∋^ X
          → X #< k
⊢oˣ-∋^-#< (opnx= x) inΓ = ⊥-elim (∋^-∋=-false inΓ x)
⊢oˣ-∋^-#< (opnx∙ x) inΓ = ⊥-elim (∋^-∋∙-false inΓ x)
⊢oˣ-∋^-#< (opnx^ x x₁) inΓ = x₁


⊢oˣ-⊆ : Γ ∤ k ⊢oˣ X
      → Γ ⊆ Δ
      → Δ ∤ k ⊢oˣ X
⊢oˣ-⊆ (opnx= x) ext = opnx= (⊆-∋= x ext)
⊢oˣ-⊆ (opnx∙ x) ext = opnx∙ (⊆-∋∙ x ext)
⊢oˣ-⊆ {X = X} (opnx^ {k = k} x x₁) ext with s-⊆-exsol ext x
... | is-ex inΓ = opnx^ inΓ x₁
... | is-sol inΓ = opnx= inΓ

⊢ok-⊆ : Γ ∤ k ⊢o A
      → Γ ⊆ Δ
      → Δ ∤ k ⊢o A
⊢ok-⊆ opn-int ext = opn-int
⊢ok-⊆ (opn-var x) ext = opn-var (⊢oˣ-⊆ x ext)
⊢ok-⊆ (opn-arr opnA opnA₁) ext = opn-arr (⊢ok-⊆ opnA ext) (⊢ok-⊆ opnA₁ ext)
⊢ok-⊆ (opn-∀ opnA) ext = opn-∀ (⊢ok-⊆ opnA (uvar ext))

⊢c-⊢ok : Γ ⊢c A
       → Γ ∤ k ⊢o A
⊢c-⊢ok ⊢c-int = opn-int
⊢c-⊢ok (⊢c-var-∙ inΔ) = opn-var (opnx∙ inΔ)
⊢c-⊢ok (⊢c-var-= inΔ) = opn-var (opnx= inΔ)
⊢c-⊢ok (⊢c-arr cloA cloA₁) = opn-arr (⊢c-⊢ok cloA) (⊢c-⊢ok cloA₁)
⊢c-⊢ok (⊢c-∀ cloA) = opn-∀ (⊢c-⊢ok cloA)

⊢r-⊢ok : Γ ⊢r A
       → Γ ∤ k ⊢o A
⊢r-⊢ok regA = ⊢c-⊢ok (⊢r-⊢c regA)

◈-∋∙-⊢oˣ : Γ ∋∙ X
         → Γ ◈ k' ⇘ Γ'
         → k' #< k
         → Γ' ∤ k ⊢oˣ X
◈-∋∙-⊢oˣ Z ◈Z lt = opnx^ Z lt
◈-∋∙-⊢oˣ Z (◈S∙ new) lt = opnx∙ Z
◈-∋∙-⊢oˣ (S, inΓ) (◈S, new) lt with ◈-∋∙-⊢oˣ inΓ new lt
... | opnx= x = opnx= (S, x)
... | opnx∙ x = opnx∙ (S, x)
... | opnx^ x x₁ = opnx^ (S, x) x₁
◈-∋∙-⊢oˣ (S∙ inΓ) ◈Z lt = opnx∙ (S^ inΓ)
◈-∋∙-⊢oˣ {k = #S k} (S∙ inΓ) (◈S∙ new) (s≤s lt) with ◈-∋∙-⊢oˣ inΓ new lt
... | opnx= x = opnx= (S∙ x)
... | opnx∙ x = opnx∙ (S∙ x)
... | opnx^ x x₁ = opnx^ (S∙ x) (s≤s x₁)
◈-∋∙-⊢oˣ {k = #S k} (S= inΓ) (◈S= new) (s≤s lt) with ◈-∋∙-⊢oˣ inΓ new lt
... | opnx= x = opnx= (S= x)
... | opnx∙ x = opnx∙ (S= x)
... | opnx^ x x₁ = opnx^ (S= x) (s≤s x₁)
◈-∋∙-⊢oˣ {k = #S k} (S^ inΓ) (◈S^ new) (s≤s lt) with ◈-∋∙-⊢oˣ inΓ new lt
... | opnx= x = opnx= (S^ x)
... | opnx∙ x = opnx∙ (S^ x)
... | opnx^ x x₁ = opnx^ (S^ x) (s≤s x₁)

◈-∋= : Γ ∋= X
     → Γ ◈ k' ⇘ Γ'
     → Γ' ∋= X
◈-∋= Z (◈S= new) = Z
◈-∋= (S∙ inΓ) ◈Z = S^ inΓ
◈-∋= (S∙ inΓ) (◈S∙ new) = S∙ (◈-∋= inΓ new)
◈-∋= (S^ inΓ) (◈S^ new) = S^ (◈-∋= inΓ new)
◈-∋= (S= inΓ) (◈S= new) = S= (◈-∋= inΓ new)
◈-∋= (S, inΓ) (◈S, new) = S, (◈-∋= inΓ new)

◈-∋^ : Γ ∋^ X
     → Γ ◈ k' ⇘ Γ'
     → Γ' ∋^ X
◈-∋^ Z (◈S^ new) = Z
◈-∋^ (S∙ inΓ) ◈Z = S^ inΓ
◈-∋^ (S∙ inΓ) (◈S∙ new) = S∙ (◈-∋^ inΓ new)
◈-∋^ (S= inΓ) (◈S= new) = S= (◈-∋^ inΓ new)
◈-∋^ (S^ inΓ) (◈S^ new) = S^ (◈-∋^ inΓ new)
◈-∋^ (S, inΓ) (◈S, new) = S, (◈-∋^ inΓ new)

⊢oˣ-◈ : Γ ∤ k ⊢oˣ X
      → k' #< k
      → Γ ◈ k' ⇘ Γ'
      → Γ' ∤ k ⊢oˣ X
⊢oˣ-◈ (opnx= x) lt new = opnx= (◈-∋= x new)
⊢oˣ-◈ (opnx∙ x) lt new = ◈-∋∙-⊢oˣ x new lt
⊢oˣ-◈ (opnx^ x x₁) lt new = opnx^ (◈-∋^ x new) x₁


⊢ok-◈ : Γ ∤ k ⊢o A
      → k' #< k
      → Γ ◈ k' ⇘ Γ'
      → Γ' ∤ k ⊢o A
⊢ok-◈ opn-int lt new = opn-int
⊢ok-◈ (opn-var x) lt new =  opn-var (⊢oˣ-◈ x lt new)
⊢ok-◈ (opn-arr opnA opnA₁) lt new = opn-arr (⊢ok-◈ opnA lt new) (⊢ok-◈ opnA₁ lt new)
⊢ok-◈ (opn-∀ opnA) lt new = opn-∀ (⊢ok-◈ opnA (s≤s lt) (◈S∙ new))

⊢ok-◈0 : Γ ,∙ ∤ #S k ⊢o A
       → Γ ,^ ∤ #S k ⊢o A
⊢ok-◈0 opnA = ⊢ok-◈ opnA (s≤s z≤n) ◈Z

∙⟹-∋= : Γ ∋= k
        → [ B / k' ] Γ ∙⟹ Γ'
        → Γ' ∋= k
∙⟹-∋= Z (∙⟹=S new up1) = Z
∙⟹-∋= (S∙ inΓ) (∙⟹^0 up regA) = S= inΓ
∙⟹-∋= (S∙ inΓ) (∙⟹∙S new up1) = S∙ (∙⟹-∋= inΓ new)
∙⟹-∋= (S^ inΓ) (∙⟹^S new up1) = S^ (∙⟹-∋= inΓ new)
∙⟹-∋= (S= inΓ) (∙⟹=S new up1) = S= (∙⟹-∋= inΓ new)
∙⟹-∋= (S, inΓ) (∙⟹,S new) = S, (∙⟹-∋= inΓ new)

∙⟹-∋^ : Γ ∋^ k
        → [ B / k' ] Γ ∙⟹ Γ'
        → Γ' ∋^ k
∙⟹-∋^ Z (∙⟹^S new up1) = Z
∙⟹-∋^ (S∙ inΓ) (∙⟹^0 up regA) = S= inΓ
∙⟹-∋^ (S∙ inΓ) (∙⟹∙S new up1) = S∙ (∙⟹-∋^ inΓ new)
∙⟹-∋^ (S= inΓ) (∙⟹=S new up1) = S= (∙⟹-∋^ inΓ new)
∙⟹-∋^ (S^ inΓ) (∙⟹^S new up1) = S^ (∙⟹-∋^ inΓ new)
∙⟹-∋^ (S, inΓ) (∙⟹,S new) = S, (∙⟹-∋^ inΓ new)

∙⟹-∋∙' : Γ ∋∙ k
       → [ A / k ] Γ ∙⟹ Γ'
       → Γ' ∋= k
∙⟹-∋∙' Z (∙⟹^0 up regA) = Z
∙⟹-∋∙' (S, inΓ) (∙⟹,S new) = S, (∙⟹-∋∙' inΓ new)
∙⟹-∋∙' (S∙ inΓ) (∙⟹∙S new up1) = S∙ (∙⟹-∋∙' inΓ new)
∙⟹-∋∙' (S= inΓ) (∙⟹=S new up1) = S= (∙⟹-∋∙' inΓ new)
∙⟹-∋∙' (S^ inΓ) (∙⟹^S new up1) = S^ (∙⟹-∋∙' inΓ new)


⊢ok-∙⟹ : Γ ∤ k ⊢o A
         → [ B / k' ] Γ ∙⟹ Γ'
         → Γ' ∤ k ⊢o A
⊢ok-∙⟹ opn-int new = opn-int
⊢ok-∙⟹ (opn-var (opnx= x)) new = opn-var (opnx= (∙⟹-∋= x new))
⊢ok-∙⟹ {k' = k'} (opn-var (opnx∙ {X = X} x)) new with X #≟ k'
... | yes refl = opn-var (opnx= (∙⟹-∋∙' x new))
... | no ¬p = opn-var (opnx∙ (∙⟹-∋∙ x ¬p new))
⊢ok-∙⟹ (opn-var (opnx^ x x₁)) new = opn-var (opnx^ (∙⟹-∋^ x new) x₁)
⊢ok-∙⟹ (opn-arr opnA opnA₁) new = opn-arr (⊢ok-∙⟹ opnA new) (⊢ok-∙⟹ opnA₁ new)
⊢ok-∙⟹ {B = B} (opn-∀ opnA) new = opn-∀ (⊢ok-∙⟹ opnA (∙⟹∙S new (proj₂ (↑ty0-total B))))

⊢ok-∙⟹0 : Γ ,∙ ∤ #S k ⊢o A
        → Γ ⊢r B
        → Γ ,= B ∤ #S k ⊢o A
⊢ok-∙⟹0 {B = B} opnA regB = ⊢ok-∙⟹ opnA (∙⟹^0 (proj₂ (↑ty0-total B)) regB)
