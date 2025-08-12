module Implicit.Decl.AuxLemmas where

open import Implicit.Language.All



infix 3 _▶'_,=_⇘_
data _▶'_,=_⇘_ : Env n m → Fin (1 + m) → Type m → Env n (1 + m) → Set where
  ▶'Z  : (regA : Γ ⊢r A)
      → Γ ▶' #0 ,= A ⇘ Γ ,= A
  ▶'S, : Γ ▶' k ,= A ⇘ Γ'
      → (up : B ↑ty k ⇘ B')
      → Γ , B ▶' k ,= A ⇘ Γ' , B'
  ▶'S^ : Γ ▶' k ,= A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → Γ ,^ ▶' #S k ,= A' ⇘ Γ' ,^
  ▶'S∙ : Γ ▶' k ,= A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → Γ ,∙ ▶' #S k ,= A' ⇘ Γ' ,∙
  ▶'S= : Γ ▶' k ,= A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → B ↑ty k ⇘ B'
      → Γ ,= B ▶' #S k ,= A' ⇘ Γ' ,= B'

▶'=-∋:= : Γ ▶' k ,= T ⇘ Γ'
       → T ↑ty k ⇘ T'
       → Γ' ∋ k := T'
▶'=-∋:= (▶'Z regA) upT = Z upT
▶'=-∋:= (▶'S, new up) upT = S, (▶'=-∋:= new upT)
▶'=-∋:= {k = #S k} (▶'S^ {A = A} new x) upT
  with ⟨ A' , upA ⟩ ← ↑ty-total A k
  = S^ (▶'=-∋:= new upA) (↑ty-comm0 x upT upA)
▶'=-∋:= {k = #S k} (▶'S∙ {A = A} new x) upT
  with ⟨ A' , upA ⟩ ← ↑ty-total A k
  = S∙ (▶'=-∋:= new upA) (↑ty-comm0 x upT upA)
▶'=-∋:= {k = #S k} (▶'S= {A = A} new up1 up2) upT
  with ⟨ A' , upA ⟩ ← ↑ty-total A k
  = S= (▶'=-∋:= new upA) (↑ty-comm0 up1 upT upA)

▶'-∋∙-helper : Γ ∋∙ X
             → Γ ▶' #0 ,= B ⇘ Γ'
             → Γ' ∋∙ #S X
▶'-∋∙-helper inΓ (▶'Z regA) = S= inΓ
▶'-∋∙-helper (S, inΓ) (▶'S, new up) = S, (▶'-∋∙-helper inΓ new)


▶'-∋∙ : Γ ▶' k ,= B ⇘ Γ'
      → (¬p : k ≢ X)
      → Γ ∋∙ punchOut ¬p
      → Γ' ∋∙ X
▶'-∋∙ {k = #0} {X = #0} new ¬p inΓ = ⊥-elim (¬p refl)
▶'-∋∙ {k = #0} {X = #S X} new ¬p inΓ = ▶'-∋∙-helper inΓ new
▶'-∋∙ {k = #S k} {X = #0} (▶'S∙ new x) ¬p Z = Z
▶'-∋∙ {k = #S k} {X = #0} (▶'S, new up) ¬p (S, inΓ) = S, (▶'-∋∙ new ¬p inΓ)
▶'-∋∙ {k = #S k} {X = #S X} (▶'S, new up) ¬p (S, inΓ) = S, (▶'-∋∙ new ¬p inΓ)
▶'-∋∙ {k = #S k} {X = #S X} (▶'S^ new x) ¬p (S^ inΓ) = S^ (▶'-∋∙ new (λ x₁ → ¬p (cong #S x₁)) inΓ)
▶'-∋∙ {k = #S k} {X = #S X} (▶'S∙ new x) ¬p (S∙ inΓ) = S∙ (▶'-∋∙ new (λ x₁ → ¬p (cong #S x₁)) inΓ)
▶'-∋∙ {k = #S k} {X = #S X} (▶'S= new x x₁) ¬p (S= inΓ) = S= (▶'-∋∙ new (λ x₂ → ¬p (cong #S x₂)) inΓ)

∋∙-∙⟹-∋:=-prv : Γ ∋∙ X
            → [ T' / k ] Γ ∙⟹ Γ'
            → Γ' ∋= X
            → X ≡ k
∋∙-∙⟹-∋:=-prv Z (∙⟹^0 up regA) Z = refl
∋∙-∙⟹-∋:=-prv (S, inΓ) (∙⟹,S new) (S, inΓ') = ∋∙-∙⟹-∋:=-prv inΓ new inΓ'
∋∙-∙⟹-∋:=-prv (S∙ inΓ) (∙⟹^0 up regA) (S= inΓ') = ⊥-elim (∋∙-∋=-false inΓ inΓ')
∋∙-∙⟹-∋:=-prv (S∙ inΓ) (∙⟹∙S new up1) (S∙ inΓ') = cong #S (∋∙-∙⟹-∋:=-prv inΓ new inΓ')
∋∙-∙⟹-∋:=-prv (S= inΓ) (∙⟹=S new up1) (S= inΓ') = cong #S (∋∙-∙⟹-∋:=-prv inΓ new inΓ')
∋∙-∙⟹-∋:=-prv (S^ inΓ) (∙⟹^S new up1) (S^ inΓ') = cong #S (∋∙-∙⟹-∋:=-prv inΓ new inΓ')


≫-↑ty-st' : Γ ⊢r A
          → T ↑ty k ⇘ T'
          → [ T' / k ] Γ ∙⟹ Γ'
          → Γ' ≫ A ⇘ A%
          → A* ↑ty k ⇘ A%
          → ⟦ k / T ⟧ A ⇘ A*
≫-↑ty-st' ⊢r-int upT new grd-int ↑ty-int = st-int
≫-↑ty-st' (⊢r-var-∙ inΓ) upT new (grd-var= x) upA*
  with refl ← ∋∙-∙⟹-∋:=-prv inΓ new (∋:=to∋= x)
  with refl ← ∋:=-unique (∙⟹-∋:= new) x
  with refl ← ↑ty-unique-inver upT upA* = st-var stx-eq
≫-↑ty-st' {k = k}(⊢r-var-∙ inΓ) upT new (grd-var∙ x) (↑ty-var {X = X})
  = st-var (stx-neq-helper helper (punchIn-injective k X (punchOut helper) (sym (punchIn-punchOut {i = k} {j = punchIn k X} helper))))
  where helper : k ≢ punchIn k X
        helper = ∙⟹-∋∙-neq inΓ new x
≫-↑ty-st' (⊢r-arr regA regA₁) upT new (grd-arr grd grd₁) (↑ty-arr upA* upA*₁) = st-arr (≫-↑ty-st' regA upT new grd upA*)
                                                                                       (≫-↑ty-st' regA₁ upT new grd₁ upA*₁)
≫-↑ty-st' {T = T} {k = k} (⊢r-∀ regA) upT new (grd-∀ grd) (↑ty-∀ upA*)
  with ⟨ T' , upT' ⟩ ← ↑ty0-total T
  with ⟨ T1 , upT1 ⟩ ← ↑ty-total T' (#S k) = st-∀ upT' (≫-↑ty-st' regA upT1 (∙⟹∙S new (↑ty-comm0 upT' upT1 upT)) grd upA*)

≫-↑ty-st'0 : Γ ,∙ ⊢r A
           → Γ ⊢r B
           → Γ ,= B ≫ A ⇘ A%
           → ↑ty0 A* ⇘ A%
           → ⟦ B ⟧ A ⇘ A*
≫-↑ty-st'0 {B = B} regA regB grd upA*
  with ⟨ B' , upB ⟩ ← ↑ty0-total B = ≫-↑ty-st' regA upB (∙⟹^0 upB regB) grd upA*


st-↑ty-≫ : ⟦ k / B ⟧ A ⇘ A*
         → A* ↑ty k ⇘ A*'
         → Γ ⊢r A*
         → Γ ▶' k ,= B ⇘ Γ'
         → Γ' ≫ A ⇘ A*'
st-↑ty-≫ st-int ↑ty-int regA* new = grd-int
st-↑ty-≫ (st-var stx-eq) upA* regA* new = grd-var= (▶'=-∋:= new upA*)
st-↑ty-≫ {k = k} (st-var (stx-neq ¬p)) ↑ty-var (⊢r-var-∙ inΓ) new rewrite punchIn-punchOut {i = k} ¬p
  = grd-var∙ (▶'-∋∙ new ¬p inΓ)
st-↑ty-≫ (st-arr stA stA₁) (↑ty-arr upA* upA*₁) (⊢r-arr regA* regA*₁) new = grd-arr (st-↑ty-≫ stA upA* regA* new)
                                                                                    (st-↑ty-≫ stA₁ upA*₁ regA*₁ new)
st-↑ty-≫ (st-∀ up stA) (↑ty-∀ upA*) (⊢r-∀ regA*) new = grd-∀ (st-↑ty-≫ stA upA* regA* (▶'S∙ new up))

st-↑ty-≫0 : ⟦ B ⟧ A ⇘ A*
          → Γ ⊢r A*
          → ↑ty0 A* ⇘ A*'
          → Γ ⊢r B
          → Γ ,= B ≫ A ⇘ A*'
st-↑ty-≫0 st regA upA* regB = st-↑ty-≫ st upA* regA (▶'Z regB)
