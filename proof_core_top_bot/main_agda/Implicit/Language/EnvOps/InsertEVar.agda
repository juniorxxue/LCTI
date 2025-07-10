module Implicit.Language.EnvOps.InsertEVar where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.Base
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Ground.Base
open import Implicit.Language.Find.Base
open import Implicit.Language.EnvOps.Base
open import Implicit.Language.EnvOps.Inst

infix 3 _▶_,^⇘_
data _▶_,^⇘_ : Env n m → Fin (1 + m) → Env n (1 + m) → Set where
  ▶Z : Γ ▶ #0 ,^⇘ Γ ,^
  ▶S, : Γ ▶ k ,^⇘ Γ'
      → (upA : A ↑ty k ⇘ A')
      → Γ , A ▶ k ,^⇘ Γ' , A'
  ▶S^ : Γ ▶ k ,^⇘ Γ'
      → Γ ,^ ▶ #S k ,^⇘ Γ' ,^
  ▶S∙ : Γ ▶ k ,^⇘ Γ'
      → Γ ,∙ ▶ #S k ,^⇘ Γ' ,∙
  ▶S= : Γ ▶ k ,^⇘ Γ'
      → (upA : A ↑ty k ⇘ A')
      → Γ ,= A ▶ #S k ,^⇘ Γ' ,= A'
  ▶S⋈ : Γ ▶ k ,^⇘ Γ'
      → Γ ⋈ ▶ k ,^⇘ Γ' ⋈


infix 3 _⨟_▶_,^⇘_⨟_
data _⨟_▶_,^⇘_⨟_ : Env n m → Env n m → Fin (1 + m) → Env n (1 + m) → Env n (1 + m) → Set where
  ▶Z : Γ ⨟ Δ ▶ #0 ,^⇘ Γ ,^ ⨟ Δ ,^
  ▶S, : Γ ⨟ Δ ▶ k ,^⇘ Γ' ⨟ Δ'
      → (upA : A ↑ty k ⇘ A')
      → Γ , A ⨟ Δ , A ▶ k ,^⇘ Γ' , A' ⨟ Δ' , A'
  ▶S^ : Γ ⨟ Δ ▶ k ,^⇘ Γ' ⨟ Δ'
      → Γ ,^ ⨟ Δ ,^ ▶ #S k ,^⇘ Γ' ,^ ⨟ Δ' ,^
  ▶S^= : Γ ⨟ Δ ▶ k ,^⇘ Γ' ⨟ Δ'
       → (upA : A ↑ty k ⇘ A')
      → Γ ,^ ⨟ Δ ,= A ▶ #S k ,^⇘ Γ' ,^ ⨟ Δ' ,= A'
  ▶S∙ : Γ ⨟ Δ ▶ k ,^⇘ Γ' ⨟ Δ'
      → Γ ,∙ ⨟ Δ ,∙ ▶ #S k ,^⇘ Γ' ,∙ ⨟ Δ' ,∙
  ▶S= : Γ ⨟ Δ ▶ k ,^⇘ Γ' ⨟ Δ'
      → (upA : A ↑ty k ⇘ A')
      → Γ ,= A ⨟ Δ ,= A ▶ #S k ,^⇘ Γ' ,= A' ⨟ Δ' ,= A'
  ▶S⋈ : Γ ⨟ Δ ▶ k ,^⇘ Γ' ⨟ Δ'
      → Γ ⋈ ⨟ Δ ⋈ ▶ k ,^⇘ Γ' ⋈ ⨟ Δ' ⋈


▶^-▶⨟^ : Γ ▶ k ,^⇘ Γ'
       → Γ ⨟ Γ ▶ k ,^⇘ Γ' ⨟ Γ'
▶^-▶⨟^ ▶Z = ▶Z
▶^-▶⨟^ (▶S, newΓ upA) = ▶S, (▶^-▶⨟^ newΓ) upA
▶^-▶⨟^ (▶S^ newΓ) = ▶S^ (▶^-▶⨟^ newΓ)
▶^-▶⨟^ (▶S∙ newΓ) = ▶S∙ (▶^-▶⨟^ newΓ)
▶^-▶⨟^ (▶S= newΓ upA) = ▶S= (▶^-▶⨟^ newΓ) upA
▶^-▶⨟^ (▶S⋈ newΓ) = ▶S⋈ (▶^-▶⨟^ newΓ)

▶⨟^-▶^-l : Γ ⨟ Δ ▶ k ,^⇘ Γ' ⨟ Δ'
       → Γ ▶ k ,^⇘ Γ'
▶⨟^-▶^-l ▶Z = ▶Z
▶⨟^-▶^-l (▶S, new upA) = ▶S, (▶⨟^-▶^-l new) upA
▶⨟^-▶^-l (▶S^ new) = ▶S^ (▶⨟^-▶^-l new)
▶⨟^-▶^-l (▶S^= new upA) = ▶S^ (▶⨟^-▶^-l new)
▶⨟^-▶^-l (▶S∙ new) = ▶S∙ (▶⨟^-▶^-l new)
▶⨟^-▶^-l (▶S= new upA) = ▶S= (▶⨟^-▶^-l new) upA
▶⨟^-▶^-l (▶S⋈ new) = ▶S⋈ (▶⨟^-▶^-l new)

▶⨟^-unique : Γ ⨟ Γ ▶ k ,^⇘ Γ' ⨟ Δ'
          → Γ' ≡ Δ'
▶⨟^-unique ▶Z = refl
▶⨟^-unique (▶S, ss upA) with refl ← ▶⨟^-unique ss = refl
▶⨟^-unique (▶S^ ss) with refl ← ▶⨟^-unique ss = refl
▶⨟^-unique (▶S∙ ss) with refl ← ▶⨟^-unique ss = refl
▶⨟^-unique (▶S= ss upA) with refl ← ▶⨟^-unique ss = refl
▶⨟^-unique (▶S⋈ ss) with refl ← ▶⨟^-unique ss = refl


∋⦂-weaken^ : Γ ∋ x ⦂ A
           → Γ ▶ k ,^⇘ Γ'
           → A ↑ty k ⇘ A'
           → Γ' ∋ x ⦂ A'
∋⦂-weaken^ Z ▶Z upA = S^ Z upA
∋⦂-weaken^ Z (▶S, newΓ upA₁) upA
  with refl ← ↑ty-unique upA upA₁ = Z
∋⦂-weaken^ (S, inΓ) ▶Z upA = S^ (S, inΓ) upA
∋⦂-weaken^ (S, inΓ) (▶S, newΓ upA₁) upA = S, (∋⦂-weaken^ inΓ newΓ upA)
∋⦂-weaken^ (S∙ inΓ up) ▶Z upA = S^ (S∙ inΓ up) upA
∋⦂-weaken^ {k = #S k} (S∙ {A = A} inΓ up) (▶S∙ newΓ) upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = S∙ (∋⦂-weaken^ inΓ newΓ upA') (↑ty-comm0 up upA upA')
∋⦂-weaken^ (S^ inΓ up) ▶Z upA = S^ (S^ inΓ up) upA
∋⦂-weaken^ {k = #S k} (S^ {A = A} inΓ up) (▶S^ newΓ) upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = S^ (∋⦂-weaken^ inΓ newΓ upA') (↑ty-comm0 up upA upA')
∋⦂-weaken^ (S= inΓ up) ▶Z upA = S^ (S= inΓ up) upA
∋⦂-weaken^ {k = #S k} (S= {A = A} inΓ up) (▶S= newΓ upA₁) upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = S= (∋⦂-weaken^ inΓ newΓ upA') (↑ty-comm0 up upA upA')

∋=-weaken^ : Γ ∋= X
           → Γ ▶ k ,^⇘ Γ'
           → Γ' ∋= punchIn k X
∋=-weaken^ Z ▶Z = S^ Z
∋=-weaken^ Z (▶S= newΓ upA) = Z
∋=-weaken^ (S∙ inΓ) ▶Z = S^ (S∙ inΓ)
∋=-weaken^ (S∙ inΓ) (▶S∙ newΓ) = S∙ (∋=-weaken^ inΓ newΓ)
∋=-weaken^ (S^ inΓ) ▶Z = S^ (S^ inΓ)
∋=-weaken^ (S^ inΓ) (▶S^ newΓ) = S^ (∋=-weaken^ inΓ newΓ)
∋=-weaken^ (S= inΓ) ▶Z = S^ (S= inΓ)
∋=-weaken^ (S= inΓ) (▶S= newΓ upA) = S= (∋=-weaken^ inΓ newΓ)
∋=-weaken^ (S, inΓ) ▶Z = S^ (S, inΓ)
∋=-weaken^ (S, inΓ) (▶S, new upA) = S, (∋=-weaken^ inΓ new)

∋^-weaken^ : Γ ∋^ X
           → Γ ▶ k ,^⇘ Γ'
           → Γ' ∋^ punchIn k X
∋^-weaken^ Z ▶Z = S^ Z
∋^-weaken^ Z (▶S^ newΓ) = Z
∋^-weaken^ (S∙ inΓ) ▶Z = S^ (S∙ inΓ)
∋^-weaken^ (S∙ inΓ) (▶S∙ newΓ) = S∙ (∋^-weaken^ inΓ newΓ)
∋^-weaken^ (S^ inΓ) ▶Z = S^ (S^ inΓ)
∋^-weaken^ (S^ inΓ) (▶S^ newΓ) = S^ (∋^-weaken^ inΓ newΓ)
∋^-weaken^ (S= inΓ) ▶Z = S^ (S= inΓ)
∋^-weaken^ (S= inΓ) (▶S= newΓ upA) = S= (∋^-weaken^ inΓ newΓ)
∋^-weaken^ (S, inΓ) ▶Z = S^ (S, inΓ)
∋^-weaken^ (S, inΓ) (▶S, new upA) = S, (∋^-weaken^ inΓ new)


∋∙-weaken^ : Γ ∋∙ X
           → Γ ▶ k ,^⇘ Γ'
           → Γ' ∋∙ punchIn k X
∋∙-weaken^ Z ▶Z = S^ Z
∋∙-weaken^ Z (▶S∙ newΓ) = Z
∋∙-weaken^ (S, inΓ) ▶Z = S^ (S, inΓ)
∋∙-weaken^ (S, inΓ) (▶S, newΓ upA) = S, (∋∙-weaken^ inΓ newΓ)
∋∙-weaken^ (S∙ inΓ) ▶Z = S^ (S∙ inΓ)
∋∙-weaken^ (S∙ inΓ) (▶S∙ newΓ) = S∙ (∋∙-weaken^ inΓ newΓ)
∋∙-weaken^ (S= inΓ) ▶Z = S^ (S= inΓ)
∋∙-weaken^ (S= inΓ) (▶S= newΓ upA) = S= (∋∙-weaken^ inΓ newΓ)
∋∙-weaken^ (S^ inΓ) ▶Z = S^ (S^ inΓ)
∋∙-weaken^ (S^ inΓ) (▶S^ newΓ) = S^ (∋∙-weaken^ inΓ newΓ)
∋∙-weaken^ (S⋈ inΓ) ▶Z = S^ (S⋈ inΓ)
∋∙-weaken^ (S⋈ inΓ) (▶S⋈ newΓ) = S⋈ (∋∙-weaken^ inΓ newΓ)

∋:=-weaken^ : Γ ∋ X := A
            → A ↑ty k ⇘ A'
            → Γ ▶ k ,^⇘ Γ'
            → Γ' ∋ punchIn k X := A'
∋:=-weaken^ (Z up) upA ▶Z = S^ (Z up) upA
∋:=-weaken^ (Z up) upA (▶S= newΓ upA₁) = Z (↑ty-comm0 up upA upA₁)
∋:=-weaken^ (S∙ inΓ up) upA ▶Z = S^ (S∙ inΓ up) upA
∋:=-weaken^ (S∙ {A = A} inΓ up) upA (▶S∙ {k = k} newΓ)
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = S∙ (∋:=-weaken^ inΓ upA' newΓ) (↑ty-comm0 up upA upA')
∋:=-weaken^ (S^ inΓ up) upA ▶Z = S^ (S^ inΓ up) upA
∋:=-weaken^ (S^ {A = A} inΓ up) upA (▶S^ {k = k} newΓ)
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = S^ (∋:=-weaken^ inΓ upA' newΓ) (↑ty-comm0 up upA upA')
∋:=-weaken^ (S= inΓ up) upA ▶Z = S^ (S= inΓ up) upA
∋:=-weaken^ (S= {A = A} inΓ up) upA (▶S= {k = k} newΓ upA₁)
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = S= (∋:=-weaken^ inΓ upA' newΓ) (↑ty-comm0 up upA upA')
∋:=-weaken^ (S, inΓ) upA ▶Z = S^ (S, inΓ) upA
∋:=-weaken^ (S, inΓ) upA (▶S, new upA₁) = S, (∋:=-weaken^ inΓ upA new)

⊢r-weaken^ : Γ ⊢r A
            → Γ ▶ k ,^⇘ Γ'
            → A ↑ty k ⇘ A'
            → Γ' ⊢r A'
⊢r-weaken^ ⊢r-int newΓ ↑ty-int = ⊢r-int
⊢r-weaken^ ⊢r-top newΓ ↑ty-top = ⊢r-top
⊢r-weaken^ ⊢r-bot newΓ ↑ty-bot = ⊢r-bot
⊢r-weaken^ (⊢r-var-∙ inΓ) newΓ ↑ty-var = ⊢r-var-∙ (∋∙-weaken^ inΓ newΓ)
⊢r-weaken^ (⊢r-arr regA regA₁) newΓ (↑ty-arr upA upA₁) = ⊢r-arr (⊢r-weaken^ regA newΓ upA) (⊢r-weaken^ regA₁ newΓ upA₁)
⊢r-weaken^ (⊢r-∀ regA) newΓ (↑ty-∀ upA) = ⊢r-∀ (⊢r-weaken^ regA (▶S∙ newΓ) upA)

⊢c-weaken^ : Γ ⊢c A
            → Γ ▶ k ,^⇘ Γ'
            → A ↑ty k ⇘ A'
            → Γ' ⊢c A'
⊢c-weaken^ ⊢c-int newΓ ↑ty-int = ⊢c-int
⊢c-weaken^ ⊢c-top newΓ ↑ty-top = ⊢c-top
⊢c-weaken^ ⊢c-bot newΓ ↑ty-bot = ⊢c-bot
⊢c-weaken^ (⊢c-var-∙ inΔ) newΓ ↑ty-var = ⊢c-var-∙ (∋∙-weaken^ inΔ newΓ)
⊢c-weaken^ (⊢c-var-= inΔ) newΓ ↑ty-var = ⊢c-var-= (∋=-weaken^ inΔ newΓ)
⊢c-weaken^ (⊢c-arr cloA cloA₁) newΓ (↑ty-arr upA upA₁) = ⊢c-arr (⊢c-weaken^ cloA newΓ upA) (⊢c-weaken^ cloA₁ newΓ upA₁)
⊢c-weaken^ (⊢c-∀ cloA) newΓ (↑ty-∀ upA) = ⊢c-∀ (⊢c-weaken^ cloA (▶S∙ newΓ) upA)

⊢o-weaken^ : Γ ⊢o A
            → Γ ▶ k ,^⇘ Γ'
            → A ↑ty k ⇘ A'
            → Γ' ⊢o A'
⊢o-weaken^ (⊢o-var-^ x) new ↑ty-var = ⊢o-var-^ (∋^-weaken^ x new)
⊢o-weaken^ (⊢o-arr-l opnA) new (↑ty-arr upA upA₁) = ⊢o-arr-l (⊢o-weaken^ opnA new upA)
⊢o-weaken^ (⊢o-arr-r opnA) new (↑ty-arr upA upA₁) = ⊢o-arr-r (⊢o-weaken^ opnA new upA₁)
⊢o-weaken^ (⊢o-∀ opnA) new (↑ty-∀ upA) = ⊢o-∀ (⊢o-weaken^ opnA (▶S∙ new) upA)

≫-weaken^ : Γ ≫ A ⇘ B
          → Γ ▶ k ,^⇘ Γ'
          → A ↑ty k ⇘ A'
          → B ↑ty k ⇘ B'
          → Γ' ≫ A' ⇘ B'
≫-weaken^ grd-int newΓ ↑ty-int ↑ty-int = grd-int
≫-weaken^ grd-top newΓ ↑ty-top ↑ty-top = grd-top
≫-weaken^ grd-bot newΓ ↑ty-bot ↑ty-bot = grd-bot
≫-weaken^ (grd-var= x) newΓ ↑ty-var upB = grd-var= (∋:=-weaken^ x upB newΓ)
≫-weaken^ (grd-var∙ x) newΓ ↑ty-var ↑ty-var = grd-var∙ (∋∙-weaken^ x newΓ)
≫-weaken^ (grd-arr grd grd₁) newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) = grd-arr (≫-weaken^ grd newΓ upA upB)
                                                                                  (≫-weaken^ grd₁ newΓ upA₁ upB₁)
≫-weaken^ (grd-∀ grd) newΓ (↑ty-∀ upA) (↑ty-∀ upB) = grd-∀ (≫-weaken^ grd (▶S∙ newΓ) upA upB)

tregular-weaken^ : TRegular Γ
                 → Γ ▶ k ,^⇘ Γ'
                 → TRegular Γ'
tregular-weaken^ reg-Z ▶Z = reg-S^ reg-Z
tregular-weaken^ (reg-S, regΓ regA) ▶Z = reg-S^ (reg-S, regΓ regA)
tregular-weaken^ (reg-S, regΓ regA) (▶S, newΓ upA) = reg-S, (tregular-weaken^ regΓ newΓ) (⊢r-weaken^ regA newΓ upA)
tregular-weaken^ (reg-S∙ regΓ) ▶Z = reg-S^ (reg-S∙ regΓ)
tregular-weaken^ (reg-S∙ regΓ) (▶S∙ newΓ) = reg-S∙ (tregular-weaken^ regΓ newΓ)
tregular-weaken^ (reg-S^ regΓ) ▶Z = reg-S^ (reg-S^ regΓ)
tregular-weaken^ (reg-S^ regΓ) (▶S^ newΓ) = reg-S^ (tregular-weaken^ regΓ newΓ)
tregular-weaken^ (reg-S= regΓ regA) ▶Z = reg-S^ (reg-S= regΓ regA)
tregular-weaken^ (reg-S= regΓ regA) (▶S= newΓ upA) = reg-S= (tregular-weaken^ regΓ newΓ) (⊢r-weaken^ regA newΓ upA)

sregular-weaken^ : SRegular Γ
                 → Γ ▶ k ,^⇘ Γ'
                 → SRegular Γ'
sregular-weaken^ (reg-Z regΓ) ▶Z = reg-S^ (reg-Z regΓ)
sregular-weaken^ (reg-Z regΓ) (▶S⋈ newΓ) = reg-Z (tregular-weaken^ regΓ newΓ)
sregular-weaken^ (reg-S∙ regΓ) ▶Z = reg-S^ (reg-S∙ regΓ)
sregular-weaken^ (reg-S∙ regΓ) (▶S∙ newΓ) = reg-S∙ (sregular-weaken^ regΓ newΓ)
sregular-weaken^ (reg-S^ regΓ) ▶Z = reg-S^ (reg-S^ regΓ)
sregular-weaken^ (reg-S^ regΓ) (▶S^ newΓ) = reg-S^ (sregular-weaken^ regΓ newΓ)
sregular-weaken^ (reg-S= regΓ regA) ▶Z = reg-S^ (reg-S= regΓ regA)
sregular-weaken^ (reg-S= regΓ regA) (▶S= newΓ upA) = reg-S= (sregular-weaken^ regΓ newΓ) (⊢r-weaken^ regA newΓ upA)


inst-weaken^ : [ A / X ] Γ ⟹ Δ
             → Γ ⨟ Δ ▶ k ,^⇘ Γ' ⨟ Δ'
             → A ↑ty k ⇘ A'
             → [ A' / punchIn k X ] Γ' ⟹ Δ'
inst-weaken^ (⟹^0 up regA env) ▶Z upA = ⟹^S (⟹^0 up regA env) upA
inst-weaken^ (⟹^0 up regA env) (▶S^= new upA₁) upA
  with refl ← ▶⨟^-unique new = ⟹^0 (↑ty-comm0 up upA upA₁) (⊢r-weaken^ regA (▶⨟^-▶^-l new) upA₁) (sregular-weaken^ env (▶⨟^-▶^-l new))
inst-weaken^ (⟹^S inst up1) ▶Z upA = ⟹^S (⟹^S inst up1) upA
inst-weaken^ {k = #S k} (⟹^S {A = A} inst up1) (▶S^ new) upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = ⟹^S (inst-weaken^ inst new upA') (↑ty-comm0 up1 upA upA')
inst-weaken^ (⟹∙S inst up1) ▶Z upA = ⟹^S (⟹∙S inst up1) upA
inst-weaken^ {k = #S k} (⟹∙S {A = A} inst up1) (▶S∙ new) upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = ⟹∙S (inst-weaken^ inst new upA') (↑ty-comm0 up1 upA upA')
inst-weaken^ (⟹=S inst up1 regB) ▶Z upA = ⟹^S (⟹=S inst up1 regB) upA
inst-weaken^ {k = #S k} (⟹=S {A = A} inst up1 regB) (▶S= new upA₁) upA
   with ⟨ A' , upA' ⟩ ← ↑ty-total A k = ⟹=S (inst-weaken^ inst new upA') (↑ty-comm0 up1 upA upA') (⊢r-weaken^ regB (▶⨟^-▶^-l new) upA₁)


⊢rʲ-weaken^ : Γ ⊢rʲ j
            → Γ ▶ k ,^⇘ Γ'
            → j ↑tyʲ k ⇘ j'
            → Γ' ⊢rʲ j'
⊢rʲ-weaken^ rj-Z new ↑tyʲ-Z = rj-Z
⊢rʲ-weaken^ rj-∞ new ↑tyʲ-∞ = rj-∞
⊢rʲ-weaken^ (rj-𝕚 regj) new (↑tyʲ-𝕚 upj) = rj-𝕚 (⊢rʲ-weaken^ regj new upj)
⊢rʲ-weaken^ (rj-𝕔 regj) new (↑tyʲ-𝕔 upj) = rj-𝕔 (⊢rʲ-weaken^ regj new upj)
⊢rʲ-weaken^ (rj-𝕥 regj regA) new (↑tyʲ-𝕥 upj upA) = rj-𝕥 (⊢rʲ-weaken^ regj new upj) (⊢r-weaken^ regA new upA)
