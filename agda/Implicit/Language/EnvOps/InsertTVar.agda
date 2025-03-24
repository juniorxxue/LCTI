module Implicit.Language.EnvOps.InsertTVar where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.Base
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Ground.Base
open import Implicit.Language.EnvOps.Base

infix 3 _▶_,_⇘_
data _▶_,_⇘_ : Env n m → Fin (1 + n) → Type m → Env (1 + n) m → Set where
  ▶Z  : (regA : Γ ⊢r A)
      → Γ ▶ #0 , A ⇘ Γ , A
  ▶S, : Γ ▶ k , A ⇘ Γ'
      → (Γ , B) ▶ #S k , A ⇘ Γ' , B
  ▶S^ : Γ ▶ k , A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → (Γ ,^) ▶ k , A' ⇘ Γ' ,^
  ▶S∙ : Γ ▶ k , A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → (Γ ,∙) ▶ k , A' ⇘ Γ' ,∙
  ▶S= : Γ ▶ k , A  ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → (Γ ,= B) ▶ k , A' ⇘ Γ' ,= B
  ▶S⋈ : Γ ▶ k , A  ⇘ Γ'
      → Γ ⋈ ▶ k , A ⇘ Γ' ⋈

infix 3 _⨟_▶_,_⇘_⨟_
data _⨟_▶_,_⇘_⨟_ : Env n m → Env n m → Fin (1 + n) → Type m → Env (1 + n) m → Env (1 + n) m → Set where
  ▶Z  : (regA : Γ ⊢r T)
      → Γ ⨟ Δ ▶ #0 , T ⇘ Γ , T ⨟ Δ , T
  ▶S, : Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
      → Γ , A ⨟ Δ , A ▶ #S k , T ⇘ Γ' , A ⨟ Δ' , A
  ▶S^ : Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
      → ↑ty0 T ⇘ T'
      → Γ ,^ ⨟ Δ ,^ ▶ k , T' ⇘ Γ' ,^ ⨟ Δ' ,^
  ▶S∙ : Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
      → ↑ty0 T ⇘ T'
      → Γ ,∙ ⨟ Δ ,∙ ▶ k , T' ⇘ Γ' ,∙ ⨟ Δ' ,∙
  ▶S= : Γ ⨟ Δ ▶ k , T  ⇘ Γ' ⨟ Δ'
      → ↑ty0 T ⇘ T'
      → Γ ,= A ⨟ Δ ,= A ▶ k , T' ⇘ Γ' ,= A ⨟ Δ' ,= A
  ▶S^= : Γ ⨟ Δ ▶ k , T  ⇘ Γ' ⨟ Δ'
      → ↑ty0 T ⇘ T'
      → Γ ,^ ⨟ Δ ,= A ▶ k , T' ⇘ Γ' ,^ ⨟ Δ' ,= A
  ▶S⋈ : Γ ⨟ Δ ▶ k , T  ⇘ Γ' ⨟ Δ'
      → Γ ⋈ ⨟ Δ ⋈ ▶ k , T  ⇘ Γ' ⋈ ⨟ Δ' ⋈

∋∙-weaken, : Γ ∋∙ X
           → Γ ▶ k , T ⇘ Γ'
           → Γ' ∋∙ X
∋∙-weaken, Z (▶Z regA) = S, Z
∋∙-weaken, Z (▶S∙ new x) = Z
∋∙-weaken, (S, inΓ) (▶Z regA) = S, (S, inΓ)
∋∙-weaken, (S, inΓ) (▶S, new) = S, (∋∙-weaken, inΓ new)
∋∙-weaken, (S∙ inΓ) (▶Z regA) = S, (S∙ inΓ)
∋∙-weaken, (S∙ inΓ) (▶S∙ new x) = S∙ (∋∙-weaken, inΓ new)
∋∙-weaken, (S= inΓ) (▶Z regA) = S, (S= inΓ)
∋∙-weaken, (S= inΓ) (▶S= new x) = S= (∋∙-weaken, inΓ new)
∋∙-weaken, (S^ inΓ) (▶Z regA) = S, (S^ inΓ)
∋∙-weaken, (S^ inΓ) (▶S^ new x) = S^ (∋∙-weaken, inΓ new)
∋∙-weaken, (S⋈ inΓ) (▶Z regA) = S, (S⋈ inΓ)
∋∙-weaken, (S⋈ inΓ) (▶S⋈ new) = S⋈ (∋∙-weaken, inΓ new)

∋=-weaken, : Γ ∋= X
           → Γ ▶ k , T ⇘ Γ'
           → Γ' ∋= X
∋=-weaken, Z (▶Z regA) = S, Z
∋=-weaken, Z (▶S= new x) = Z
∋=-weaken, (S∙ inΓ) (▶Z regA) = S, (S∙ inΓ)
∋=-weaken, (S∙ inΓ) (▶S∙ new x) = S∙ (∋=-weaken, inΓ new)
∋=-weaken, (S^ inΓ) (▶Z regA) = S, (S^ inΓ)
∋=-weaken, (S^ inΓ) (▶S^ new x) = S^ (∋=-weaken, inΓ new)
∋=-weaken, (S= inΓ) (▶Z regA) = S, (S= inΓ)
∋=-weaken, (S= inΓ) (▶S= new x) = S= (∋=-weaken, inΓ new)
∋=-weaken, (S, inΓ) (▶Z regA) = S, (S, inΓ)
∋=-weaken, (S, inΓ) (▶S, new) = S, (∋=-weaken, inΓ new)


∋:=-weaken, : Γ ∋ X := A
            → Γ ▶ k , T ⇘ Γ'
            → Γ' ∋ X := A
∋:=-weaken, (Z up) (▶Z regA) = S, (Z up)
∋:=-weaken, (Z up) (▶S= new x) = Z up
∋:=-weaken, (S∙ inΓ up) (▶Z regA) = S, (S∙ inΓ up)
∋:=-weaken, (S∙ inΓ up) (▶S∙ new x) = S∙ (∋:=-weaken, inΓ new) up
∋:=-weaken, (S^ inΓ up) (▶Z regA) = S, (S^ inΓ up)
∋:=-weaken, (S^ inΓ up) (▶S^ new x) = S^ (∋:=-weaken, inΓ new) up
∋:=-weaken, (S= inΓ up) (▶Z regA) = S, (S= inΓ up)
∋:=-weaken, (S= inΓ up) (▶S= new x) = S= (∋:=-weaken, inΓ new) up
∋:=-weaken, (S, inΓ) (▶Z regA) = S, (S, inΓ)
∋:=-weaken, (S, inΓ) (▶S, new) = S, (∋:=-weaken, inΓ new)


∋⦂-weaken, : Γ ∋ x ⦂ A
           → Γ ▶ k , T ⇘ Γ'
           → Γ' ∋ punchIn k x ⦂ A
∋⦂-weaken, Z (▶Z regA) = S, Z
∋⦂-weaken, Z (▶S, new) = Z
∋⦂-weaken, (S, inΓ) (▶Z regA) = S, (S, inΓ)
∋⦂-weaken, (S, inΓ) (▶S, new) = S, (∋⦂-weaken, inΓ new)
∋⦂-weaken, (S∙ inΓ up) (▶Z regA) = S, (S∙ inΓ up)
∋⦂-weaken, (S∙ inΓ up) (▶S∙ new x) = S∙ (∋⦂-weaken, inΓ new) up
∋⦂-weaken, (S^ inΓ up) (▶Z regA) = S, (S^ inΓ up)
∋⦂-weaken, (S^ inΓ up) (▶S^ new x) = S^ (∋⦂-weaken, inΓ new) up
∋⦂-weaken, (S= inΓ up) (▶Z regA) = S, (S= inΓ up)
∋⦂-weaken, (S= inΓ up) (▶S= new x) = S= (∋⦂-weaken, inΓ new) up


∋^-weaken, : Γ ∋^ X
           → Γ ▶ k , T ⇘ Γ'
           → Γ' ∋^ X
∋^-weaken, Z (▶Z regA) = S, Z
∋^-weaken, Z (▶S^ new x) = Z
∋^-weaken, (S∙ inΓ) (▶Z regA) = S, (S∙ inΓ)
∋^-weaken, (S∙ inΓ) (▶S∙ new x) = S∙ (∋^-weaken, inΓ new)
∋^-weaken, (S= inΓ) (▶Z regA) = S, (S= inΓ)
∋^-weaken, (S= inΓ) (▶S= new x) = S= (∋^-weaken, inΓ new)
∋^-weaken, (S^ inΓ) (▶Z regA) = S, (S^ inΓ)
∋^-weaken, (S^ inΓ) (▶S^ new x) = S^ (∋^-weaken, inΓ new)
∋^-weaken, (S, inΓ) (▶Z regA) = S, (S, inΓ)
∋^-weaken, (S, inΓ) (▶S, new) = S, (∋^-weaken, inΓ new)

⊢r-weaken, : Γ ⊢r A
           → Γ ▶ k , T ⇘ Γ'
           → Γ' ⊢r A
⊢r-weaken, ⊢r-int new = ⊢r-int
⊢r-weaken, (⊢r-var-∙ inΓ) new = ⊢r-var-∙ (∋∙-weaken, inΓ new)
⊢r-weaken, (⊢r-arr regA regA₁) new = ⊢r-arr (⊢r-weaken, regA new) (⊢r-weaken, regA₁ new)
⊢r-weaken, {T = T} (⊢r-∀ regA) new
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢r-∀ (⊢r-weaken, regA (▶S∙ new upT))

⊢c-weaken, : Γ ⊢c A
           → Γ ▶ k , T ⇘ Γ'
           → Γ' ⊢c A
⊢c-weaken, ⊢c-int new = ⊢c-int
⊢c-weaken, (⊢c-var-∙ inΔ) new = ⊢c-var-∙ (∋∙-weaken, inΔ new)
⊢c-weaken, (⊢c-var-= inΔ) new = ⊢c-var-= (∋=-weaken, inΔ new)
⊢c-weaken, (⊢c-arr cloA cloA₁) new = ⊢c-arr (⊢c-weaken, cloA new) (⊢c-weaken, cloA₁ new)
⊢c-weaken, {T = T} (⊢c-∀ cloA) new
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢c-∀ (⊢c-weaken, cloA (▶S∙ new upT))

⊢o-weaken, : Γ ⊢o A
           → Γ ▶ k , T ⇘ Γ'
           → Γ' ⊢o A
⊢o-weaken, (⊢o-var-^ x) new = ⊢o-var-^ (∋^-weaken, x new)
⊢o-weaken, (⊢o-arr-l opnA) new = ⊢o-arr-l (⊢o-weaken, opnA new)
⊢o-weaken, (⊢o-arr-r opnA) new = ⊢o-arr-r (⊢o-weaken, opnA new)
⊢o-weaken, {T = T} (⊢o-∀ opnA) new
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢o-∀ (⊢o-weaken, opnA (▶S∙ new upT))


tregular-weaken, : TRegular Γ
                 → Γ ▶ k , T ⇘ Γ'
                 → TRegular Γ'
tregular-weaken, reg-Z (▶Z regA) = reg-S, reg-Z regA
tregular-weaken, (reg-S, regΓ regA) (▶Z regA₁) = reg-S, (reg-S, regΓ regA) regA₁
tregular-weaken, (reg-S, regΓ regA) (▶S, new) = reg-S, (tregular-weaken, regΓ new) (⊢r-weaken, regA new)
tregular-weaken, (reg-S∙ regΓ) (▶Z regA) = reg-S, (reg-S∙ regΓ) regA
tregular-weaken, (reg-S∙ regΓ) (▶S∙ new x) = reg-S∙ (tregular-weaken, regΓ new)
tregular-weaken, (reg-S^ regΓ) (▶Z regA) = reg-S, (reg-S^ regΓ) regA
tregular-weaken, (reg-S^ regΓ) (▶S^ new x) = reg-S^ (tregular-weaken, regΓ new)
tregular-weaken, (reg-S= regΓ regA) (▶Z regA₁) = reg-S, (reg-S= regΓ regA) regA₁
tregular-weaken, (reg-S= regΓ regA) (▶S= new x) = reg-S= (tregular-weaken, regΓ new) (⊢r-weaken, regA new)


sregular-weaken, : SRegular Γ
                 → Γ ▶ k , T ⇘ Γ'
                 → SRegular Γ'
sregular-weaken, (reg-Z regΓ) (▶Z regA) = {!!}
sregular-weaken, (reg-Z regΓ) (▶S⋈ new) = {!!}
sregular-weaken, (reg-S∙ regΓ) new = {!!}
sregular-weaken, (reg-S^ regΓ) new = {!!}
sregular-weaken, (reg-S= regΓ regA) new = {!!}


≫-weaken, : Γ ≫ A ⇘ B
          → Γ ▶ k , T ⇘ Γ'
          → Γ' ≫ A ⇘ B

inst-weaken, : [ A / X ] Γ ⟹ Δ
             → Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
             → [ A / X ] Γ' ⟹ Δ'
