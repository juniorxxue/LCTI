module Implicit.Language.EnvOps.InsertSVar where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.All
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Ground.Base
open import Implicit.Language.EnvOps.Base
open import Implicit.Language.EnvOps.Inst

infix 3 _▶_,=_⇘_
data _▶_,=_⇘_ : Env n m → Fin (1 + m) → Type m → Env n (1 + m) → Set where
  ▶Z  : (regA : Γ ⊢r A)
      → Γ ▶ #0 ,= A ⇘ Γ ,= A
  ▶S, : Γ ▶ k ,= A ⇘ Γ'
      → (up : B ↑ty k ⇘ B')
      → Γ , B ▶ k ,= A ⇘ Γ' , B'
  ▶S^ : Γ ▶ k ,= A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → Γ ,^ ▶ #S k ,= A' ⇘ Γ' ,^
  ▶S∙ : Γ ▶ k ,= A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → Γ ,∙ ▶ #S k ,= A' ⇘ Γ' ,∙
  ▶S= : Γ ▶ k ,= A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → B ↑ty k ⇘ B'
      → Γ ,= B ▶ #S k ,= A' ⇘ Γ' ,= B'
  ▶S⋈ : Γ ▶ k ,= A ⇘ Γ'
      → Γ ⋈ ▶ k ,= A ⇘ Γ' ⋈

infix 3 _⨟_▶_,=_⇘_⨟_
data _⨟_▶_,=_⇘_⨟_ : Env n m → Env n m → Fin (1 + m) → Type m → Env n (1 + m) → Env n (1 + m) → Set where
  ▶Z  : (regA : Γ ⊢r A)
      → Γ ⨟ Δ ▶ #0 ,= A ⇘ Γ ,= A ⨟ Δ ,= A
  ▶S, : Γ ⨟ Δ ▶ k ,= A ⇘ Γ' ⨟ Δ'
      → (up : B ↑ty k ⇘ B')
      → Γ , B ⨟ Δ , B ▶ k ,= A ⇘ Γ' , B' ⨟ Δ' , B'
  ▶S^ : Γ ⨟ Δ ▶ k ,= A ⇘ Γ' ⨟ Δ'
      → ↑ty0 A ⇘ A'
      → Γ ,^ ⨟ Δ ,^ ▶ #S k ,= A' ⇘ Γ' ,^ ⨟ Δ' ,^
  ▶S^= : Γ ⨟ Δ ▶ k ,= A ⇘ Γ' ⨟ Δ'
       → ↑ty0 A ⇘ A'
       → B ↑ty k ⇘ B'
       → Γ ,^ ⨟ Δ ,= B ▶ #S k ,= A' ⇘ Γ' ,^ ⨟ Δ' ,= B'
  ▶S∙ : Γ ⨟ Δ ▶ k ,= A ⇘ Γ' ⨟ Δ'
      → ↑ty0 A ⇘ A'
      → Γ ,∙ ⨟ Δ ,∙ ▶ #S k ,= A' ⇘ Γ' ,∙ ⨟ Δ' ,∙
  ▶S= : Γ ⨟ Δ ▶ k ,= A ⇘ Γ' ⨟ Δ'
      → ↑ty0 A ⇘ A'
      → B ↑ty k ⇘ B'
      → Γ ,= B ⨟ Δ ,= B ▶ #S k ,= A' ⇘ Γ' ,= B' ⨟ Δ' ,= B'
  ▶S⋈ : Γ ⨟ Δ ▶ k ,= A ⇘ Γ' ⨟ Δ'
      → Γ ⋈ ⨟ Δ ⋈ ▶ k ,= A ⇘ Γ' ⋈ ⨟ Δ' ⋈


∋:=-weaken= : Γ ∋ X := A
       → Γ ▶ k ,= T ⇘ Γ'
       → A ↑ty k ⇘ A'
       → Γ' ∋ punchIn k X := A'
∋:=-weaken= (Z up) (▶Z cloA) upA = S= (Z up) upA
∋:=-weaken= (Z up) (▶S= newΓ x x₁) upA = Z (↑ty-comm0 up upA x₁)
∋:=-weaken= (S, inΓ) (▶Z cloA) upA = S= (S, inΓ) upA
∋:=-weaken= (S, inΓ) (▶S, newΓ x) upA = S, (∋:=-weaken= inΓ newΓ upA)
∋:=-weaken= (S∙ inΓ up) (▶Z cloA) upA = S= (S∙ inΓ up) upA
∋:=-weaken= (S∙ {A = A} inΓ up) (▶S∙ {k = k} newΓ x) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S∙ (∋:=-weaken= inΓ newΓ upA') (↑ty-comm0 up upA upA')
∋:=-weaken= (S^ inΓ up) (▶Z cloA) upA = S= (S^ inΓ up) upA
∋:=-weaken= (S^ {A = A} inΓ up) (▶S^ {k = k} newΓ x) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S^ (∋:=-weaken= inΓ newΓ upA') (↑ty-comm0 up upA upA')
∋:=-weaken= (S= inΓ up) (▶Z cloA) upA = S= (S= inΓ up) upA
∋:=-weaken= (S= {A = A} inΓ up) (▶S= {k = k} newΓ x x₁) upA with ↑ty-total A k
... | ⟨ A' , upA' ⟩ = S= (∋:=-weaken= inΓ newΓ upA') (↑ty-comm0 up upA upA')

∋∙-weaken= : Γ ∋∙ X
      → Γ ▶ k ,= T ⇘ Γ'
      → Γ' ∋∙ punchIn k X
∋∙-weaken= Z (▶Z cloA) = S= Z
∋∙-weaken= Z (▶S∙ newΓ x) = Z
∋∙-weaken= (S, inΓ) (▶Z cloA) = S= (S, inΓ)
∋∙-weaken= (S, inΓ) (▶S, newΓ x) = S, (∋∙-weaken= inΓ newΓ)
∋∙-weaken= (S∙ inΓ) (▶Z cloA) = S= (S∙ inΓ)
∋∙-weaken= (S∙ inΓ) (▶S∙ newΓ x) = S∙ (∋∙-weaken= inΓ newΓ)
∋∙-weaken= (S= inΓ) (▶Z cloA) = S= (S= inΓ)
∋∙-weaken= (S= inΓ) (▶S= newΓ x x₁) = S= (∋∙-weaken= inΓ newΓ)
∋∙-weaken= (S^ inΓ) (▶Z cloA) = S= (S^ inΓ)
∋∙-weaken= (S^ inΓ) (▶S^ newΓ x) = S^ (∋∙-weaken= inΓ newΓ)
∋∙-weaken= (S⋈ inΓ) (▶Z regA) = S= (S⋈ inΓ)
∋∙-weaken= (S⋈ inΓ) (▶S⋈ newΓ) = S⋈ (∋∙-weaken= inΓ newΓ)


∋=-weaken= : Γ ∋= X
      → Γ ▶ k ,= T ⇘ Γ'
      → Γ' ∋= punchIn k X
∋=-weaken= Z (▶Z cloA) = S= Z
∋=-weaken= Z (▶S= newΓ x x₁) = Z
∋=-weaken= (S, inΓ) (▶Z cloA) = S= (S, inΓ)
∋=-weaken= (S, inΓ) (▶S, newΓ x) = S, (∋=-weaken= inΓ newΓ)
∋=-weaken= (S∙ inΓ) (▶Z cloA) = S= (S∙ inΓ)
∋=-weaken= (S∙ inΓ) (▶S∙ newΓ x) = S∙ (∋=-weaken= inΓ newΓ)
∋=-weaken= (S= inΓ) (▶Z cloA) = S= (S= inΓ)
∋=-weaken= (S= inΓ) (▶S= newΓ x x₁) = S= (∋=-weaken= inΓ newΓ)
∋=-weaken= (S^ inΓ) (▶Z cloA) = S= (S^ inΓ)
∋=-weaken= (S^ inΓ) (▶S^ newΓ x) = S^ (∋=-weaken= inΓ newΓ)

∋^-weaken= : Γ ∋^ X
      → Γ ▶ k ,= T ⇘ Γ'
      → Γ' ∋^ punchIn k X
∋^-weaken= Z (▶Z cloA) = S= Z
∋^-weaken= Z (▶S^ newΓ _) = Z
∋^-weaken= (S, inΓ) (▶Z cloA) = S= (S, inΓ)
∋^-weaken= (S, inΓ) (▶S, newΓ x) = S, (∋^-weaken= inΓ newΓ)
∋^-weaken= (S∙ inΓ) (▶Z cloA) = S= (S∙ inΓ)
∋^-weaken= (S∙ inΓ) (▶S∙ newΓ x) = S∙ (∋^-weaken= inΓ newΓ)
∋^-weaken= (S= inΓ) (▶Z cloA) = S= (S= inΓ)
∋^-weaken= (S= inΓ) (▶S= newΓ x x₁) = S= (∋^-weaken= inΓ newΓ)
∋^-weaken= (S^ inΓ) (▶Z cloA) = S= (S^ inΓ)
∋^-weaken= (S^ inΓ) (▶S^ newΓ x) = S^ (∋^-weaken= inΓ newΓ)

⊢r-weaken= : Γ ⊢r A
           → Γ ▶ k ,= T ⇘ Γ'
           → A ↑ty k ⇘ A'
           → Γ' ⊢r A'
⊢r-weaken= ⊢r-int new ↑ty-int = ⊢r-int
⊢r-weaken= (⊢r-var-∙ inΓ) new ↑ty-var = ⊢r-var-∙ (∋∙-weaken= inΓ new)
⊢r-weaken= (⊢r-arr regA regA₁) new (↑ty-arr upA upA₁) = ⊢r-arr (⊢r-weaken= regA new upA) (⊢r-weaken= regA₁ new upA₁)
⊢r-weaken= {T = T} (⊢r-∀ regA) new (↑ty-∀ upA)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢r-∀ (⊢r-weaken= regA (▶S∙ new upT) upA)


▶=-𝕣 : Γ ▶ k ,= T ⇘ Γ'
     → 𝕣 Γ ▶ k ,= T ⇘ 𝕣 Γ'
▶=-𝕣 (▶Z regA) = ▶Z (⊢r-𝕣' regA)
▶=-𝕣 (▶S, new up) = ▶S, (▶=-𝕣 new) up
▶=-𝕣 (▶S^ new x) = ▶S^ (▶=-𝕣 new) x
▶=-𝕣 (▶S∙ new x) = ▶S∙ (▶=-𝕣 new) x
▶=-𝕣 (▶S= new x x₁) = ▶S= (▶=-𝕣 new) x x₁
▶=-𝕣 (▶S⋈ new) = new

▶⨟=-unique : Γ ⨟ Γ ▶ k ,= T ⇘ Γ' ⨟ Δ'
           → Γ' ≡ Δ'
▶⨟=-unique (▶Z regA) = refl
▶⨟=-unique (▶S, new up) with refl ← ▶⨟=-unique new = refl
▶⨟=-unique (▶S^ new x) with refl ← ▶⨟=-unique new = refl
▶⨟=-unique (▶S∙ new x) with refl ← ▶⨟=-unique new = refl
▶⨟=-unique (▶S= new x x₁) with refl ← ▶⨟=-unique new = refl
▶⨟=-unique (▶S⋈ new) with refl ← ▶⨟=-unique new = refl

▶⨟=-▶=-l : Γ ⨟ Δ ▶ k ,= T ⇘ Γ' ⨟ Δ'
         → Γ ▶ k ,= T ⇘ Γ'
▶⨟=-▶=-l (▶Z regA) = ▶Z regA
▶⨟=-▶=-l (▶S, new up) = ▶S, (▶⨟=-▶=-l new) up
▶⨟=-▶=-l (▶S^ new x) = ▶S^ (▶⨟=-▶=-l new) x
▶⨟=-▶=-l (▶S^= new x x₁) = ▶S^ (▶⨟=-▶=-l new) x
▶⨟=-▶=-l (▶S∙ new x) = ▶S∙ (▶⨟=-▶=-l new) x
▶⨟=-▶=-l (▶S= new x x₁) = ▶S= (▶⨟=-▶=-l new) x x₁
▶⨟=-▶=-l (▶S⋈ new) = ▶S⋈ (▶⨟=-▶=-l new)

▶=-▶⨟= : Γ ▶ k ,= T ⇘ Γ'
       → Γ ⨟ Γ ▶ k ,= T ⇘ Γ' ⨟ Γ'
▶=-▶⨟= (▶Z regA) = ▶Z regA
▶=-▶⨟= (▶S, new up) = ▶S, (▶=-▶⨟= new) up
▶=-▶⨟= (▶S^ new x) = ▶S^ (▶=-▶⨟= new) x
▶=-▶⨟= (▶S∙ new x) = ▶S∙ (▶=-▶⨟= new) x
▶=-▶⨟= (▶S= new x x₁) = ▶S= (▶=-▶⨟= new) x x₁
▶=-▶⨟= (▶S⋈ new) = ▶S⋈ (▶=-▶⨟= new)



tregular-weaken= : TRegular Γ
                 → Γ ▶ k ,= T ⇘ Γ'
                 → TRegular Γ'
tregular-weaken= reg-Z (▶Z regA) = reg-S= reg-Z regA
tregular-weaken= (reg-S, regΓ regA) (▶Z regA₁) = reg-S= (reg-S, regΓ regA) regA₁
tregular-weaken= (reg-S, regΓ regA) (▶S, new up) = reg-S, (tregular-weaken= regΓ new) (⊢r-weaken= regA new up)
tregular-weaken= (reg-S∙ regΓ) (▶Z regA) = reg-S= (reg-S∙ regΓ) regA
tregular-weaken= (reg-S∙ regΓ) (▶S∙ new x) = reg-S∙ (tregular-weaken= regΓ new)
tregular-weaken= (reg-S^ regΓ) (▶Z regA) = reg-S= (reg-S^ regΓ) regA
tregular-weaken= (reg-S^ regΓ) (▶S^ new x) = reg-S^ (tregular-weaken= regΓ new)
tregular-weaken= (reg-S= regΓ regA) (▶Z regA₁) = reg-S= (reg-S= regΓ regA) regA₁
tregular-weaken= (reg-S= regΓ regA) (▶S= new x x₁) = reg-S= (tregular-weaken= regΓ new) (⊢r-weaken= regA new x₁)

sregular-weaken= : SRegular Γ
                 → Γ ▶ k ,= T ⇘ Γ'
                 → SRegular Γ'
sregular-weaken= (reg-Z regΓ) (▶Z regA) = reg-S= (reg-Z regΓ) regA
sregular-weaken= (reg-Z regΓ) (▶S⋈ new) = reg-Z (tregular-weaken= regΓ new)
sregular-weaken= (reg-S∙ regΓ) (▶Z regA) = reg-S= (reg-S∙ regΓ) regA
sregular-weaken= (reg-S∙ regΓ) (▶S∙ new x) = reg-S∙ (sregular-weaken= regΓ new)
sregular-weaken= (reg-S^ regΓ) (▶Z regA) = reg-S= (reg-S^ regΓ) regA
sregular-weaken= (reg-S^ regΓ) (▶S^ new x) = reg-S^ (sregular-weaken= regΓ new)
sregular-weaken= (reg-S= regΓ regA) (▶Z regA₁) = reg-S= (reg-S= regΓ regA) regA₁
sregular-weaken= (reg-S= regΓ regA) (▶S= new x x₁) = reg-S= (sregular-weaken= regΓ new) (⊢r-weaken= regA new x₁)

∋⦂-weaken= : Γ ∋ x ⦂ A
           → Γ ▶ k ,= T ⇘ Γ'
           → A ↑ty k ⇘ A'
           → Γ' ∋ x ⦂ A'
∋⦂-weaken= Z (▶Z regA) upA = S= Z upA
∋⦂-weaken= Z (▶S, new up) upA
  with refl ← ↑ty-unique up upA = Z
∋⦂-weaken= (S, inΓ) (▶Z regA) upA = S= (S, inΓ) upA
∋⦂-weaken= (S, inΓ) (▶S, new up) upA = S, (∋⦂-weaken= inΓ new upA)
∋⦂-weaken= (S∙ inΓ up) (▶Z regA) upA = S= (S∙ inΓ up) upA
∋⦂-weaken= {k = #S k} (S∙ {A = A} inΓ up) (▶S∙ new x) upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = S∙ (∋⦂-weaken= inΓ new upA') (↑ty-comm0 up upA upA')
∋⦂-weaken= (S^ inΓ up) (▶Z regA) upA = S= (S^ inΓ up) upA
∋⦂-weaken= {k = #S k} (S^ {A = A} inΓ up) (▶S^ new x) upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = S^ (∋⦂-weaken= inΓ new upA') (↑ty-comm0 up upA upA')
∋⦂-weaken= (S= inΓ up) (▶Z regA) upA = S= (S= inΓ up) upA
∋⦂-weaken= {k = #S k} (S= {A = A} inΓ up) (▶S= new x x₁) upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = S= (∋⦂-weaken= inΓ new upA') (↑ty-comm0 up upA upA')

⊢c-weaken= : Γ ⊢c A
           → Γ ▶ k ,= T ⇘ Γ'
           → A ↑ty k ⇘ A'
           → Γ' ⊢c A'
⊢c-weaken= ⊢c-int new ↑ty-int = ⊢c-int
⊢c-weaken= (⊢c-var-∙ inΔ) new ↑ty-var = ⊢c-var-∙ (∋∙-weaken= inΔ new)
⊢c-weaken= (⊢c-var-= inΔ) new ↑ty-var = ⊢c-var-= (∋=-weaken= inΔ new)
⊢c-weaken= (⊢c-arr cloA cloA₁) new (↑ty-arr upA upA₁) = ⊢c-arr (⊢c-weaken= cloA new upA) (⊢c-weaken= cloA₁ new upA₁)
⊢c-weaken= {T = T} (⊢c-∀ cloA) new (↑ty-∀ upA)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢c-∀ (⊢c-weaken= cloA (▶S∙ new upT) upA)

⊢o-weaken= : Γ ⊢o A
           → Γ ▶ k ,= T ⇘ Γ'
           → A ↑ty k ⇘ A'
           → Γ' ⊢o A'
⊢o-weaken= (⊢o-var-^ x) new ↑ty-var = ⊢o-var-^ (∋^-weaken= x new)
⊢o-weaken= (⊢o-arr-l opnA) new (↑ty-arr upA upA₁) = ⊢o-arr-l (⊢o-weaken= opnA new upA)
⊢o-weaken= (⊢o-arr-r opnA) new (↑ty-arr upA upA₁) = ⊢o-arr-r (⊢o-weaken= opnA new upA₁)
⊢o-weaken= {T = T} (⊢o-∀ opnA) new (↑ty-∀ upA)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢o-∀ (⊢o-weaken= opnA (▶S∙ new upT) upA)

≫-weaken= : Γ ≫ A ⇘ B
          → Γ ▶ k ,= T ⇘ Γ'
          → A ↑ty k ⇘ A'
          → B ↑ty k ⇘ B'
          → Γ' ≫ A' ⇘ B'
≫-weaken= grd-int new ↑ty-int ↑ty-int = grd-int
≫-weaken= (grd-var= x) new ↑ty-var upB = grd-var= (∋:=-weaken= x new upB)
≫-weaken= (grd-var∙ x) new ↑ty-var ↑ty-var = grd-var∙ (∋∙-weaken= x new)
≫-weaken= (grd-arr grd grd₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = grd-arr (≫-weaken= grd new upA upB) (≫-weaken= grd₁ new upA₁ upB₁)
≫-weaken= {T = T} (grd-∀ grd) new (↑ty-∀ upA) (↑ty-∀ upB)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = grd-∀ (≫-weaken= grd (▶S∙ new upT) upA upB)


inst-weaken= : [ A / X ] Γ ⟹ Δ
             → Γ ⨟ Δ ▶ k ,= T ⇘ Γ' ⨟ Δ'
             → A ↑ty k ⇘ A'
             → [ A' / punchIn k X ] Γ' ⟹ Δ'
inst-weaken= (⟹^0 up regA env) (▶Z regA₁) upA = ⟹=S (⟹^0 up regA env) upA regA₁
inst-weaken= (⟹^0 up regA env) (▶S^= new x x₁) upA with refl ← ▶⨟=-unique new = ⟹^0 (↑ty-comm0 up upA x₁)
                                                                                      (⊢r-weaken= regA (▶⨟=-▶=-l new) x₁)
                                                                                      (sregular-weaken= env (▶⨟=-▶=-l new))
inst-weaken= (⟹^S inst up1) (▶Z regA) upA = ⟹=S (⟹^S inst up1) upA regA
inst-weaken= {k = #S k} (⟹^S {A = A} inst up1) (▶S^ new x) upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = ⟹^S (inst-weaken= inst new upA') (↑ty-comm0 up1 upA upA')
inst-weaken= (⟹∙S inst up1) (▶Z regA) upA = ⟹=S (⟹∙S inst up1) upA regA
inst-weaken= {k = #S k} (⟹∙S {A = A} inst up1) (▶S∙ new x) upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k  = ⟹∙S (inst-weaken= inst new upA') (↑ty-comm0 up1 upA upA')
inst-weaken= (⟹=S inst up1 regB) (▶Z regA) upA = ⟹=S (⟹=S inst up1 regB) upA regA
inst-weaken= {k = #S k} (⟹=S {A = A} inst up1 regB) (▶S= new x x₁) upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = ⟹=S (inst-weaken= inst new upA') (↑ty-comm0 up1 upA upA') (⊢r-weaken= regB (▶⨟=-▶=-l new) x₁)
