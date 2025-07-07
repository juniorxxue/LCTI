module Implicit.Decl.Equiv where

open import Implicit.Language.All
open import Implicit.Decl.Subtyping
open import Implicit.Decl.SubtypingV2



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

⊢d→⊢d² : Γ ⊢d j # A ≤ B
      → Γ ⊢d² j # A ≤ B
⊢d→⊢d² (s-refl regΔ cloA) = s-refl regΔ cloA
⊢d→⊢d² (s-int regΔ) = s-int regΔ
⊢d→⊢d² (s-var-∙ regΔ inΔ) = s-var-∙ regΔ inΔ
⊢d→⊢d² (s-arr₁ s s₁) = s-arr₁ (⊢d→⊢d² s) (⊢d→⊢d² s₁)
⊢d→⊢d² (s-arr₂ s s₁) = s-arr₂ (⊢d→⊢d² s) (⊢d→⊢d² s₁)
⊢d→⊢d² (s-arr₃ regA s) = s-arr₃ regA (⊢d→⊢d² s)
⊢d→⊢d² (s-∀ s) = s-∀ (⊢d→⊢d² s)
⊢d→⊢d² (s-∀l {B = B} {A* = A*} {C = C} {D = D} regB st s ic fd upj)
  with ⟨ C' , upC ⟩ ← ↑ty0-total C
  with ⟨ D' , upD ⟩ ← ↑ty0-total D
  with ⟨ A*' , upA* ⟩ ← ↑ty0-total A*
  with regA* ← s1-⊢r-l s
  with regA ← st-⊢r'' regA* ▶Z regB st
  = s-∀l {B = B} {A% = A*'} (st-↑ty-≫0 st regA* upA* regB) regA (s2-weaken=0 (⊢d→⊢d² s) upA* (↑ty-arr upC upD) upj regB) ic fd upC upD upj
⊢d→⊢d² (s-∀l-no-appear {B = B} {A* = A*} {j = j} {C = C} {D = D} regB st s ic fd)
  with ⟨ C' , upC ⟩ ← ↑ty0-total C
  with ⟨ D' , upD ⟩ ← ↑ty0-total D
  with ⟨ A*' , upA* ⟩ ← ↑ty0-total A*
  with ⟨ j' , upj ⟩ ← ↑tyʲ0-total j
  with regA* ← s1-⊢r-l s
  with regA ← st-⊢r'' regA* ▶Z regB st
  = s-∀l-no-appear (≫-weaken^ {k = #0} (⊢r-≫-eq regA*) ▶Z (st-↑ty fd st) upA*) regA (s2-weaken^0 (⊢d→⊢d² s) upA* (↑ty-arr upC upD) upj) ic fd upC upD upj
⊢d→⊢d² (s-tapp {A* = A*} {j = j} regB st s upC)
  with ⟨ A*' , upA* ⟩ ← ↑ty0-total A*
  with ⟨ j' , upj ⟩ ← ↑tyʲ0-total j
  = s-tapp (st-↑ty-≫0 st (s1-⊢r-l s) upA* regB) (st-⊢r'' (s1-⊢r-l s) ▶Z regB st) (s2-weaken=0 (⊢d→⊢d² s) upA* upC upj regB) upj

⊢d²→⊢d : Γ ⊢d² j # A ≤ B
         → Γ ⊢d j # A ≤ B
⊢d²→⊢d (s-refl regΔ cloA) = s-refl regΔ cloA
⊢d²→⊢d (s-int regΔ) = s-int regΔ
⊢d²→⊢d (s-var-∙ regΔ inΔ) = s-var-∙ regΔ inΔ
⊢d²→⊢d (s-arr₁ s s₁) = s-arr₁ (⊢d²→⊢d s) (⊢d²→⊢d s₁)
⊢d²→⊢d (s-arr₂ s s₁) = s-arr₂ (⊢d²→⊢d s) (⊢d²→⊢d s₁)
⊢d²→⊢d (s-arr₃ regA s) = s-arr₃ regA (⊢d²→⊢d s)
⊢d²→⊢d (s-∀ s) = s-∀ (⊢d²→⊢d s)
⊢d²→⊢d (s-∀l {B = B} grd regA s ic fd upC upD upj)
  with reg-S= r regA₁ ← s2-sregular s
  with ⟨ preA% , upp ⟩ ← ↑ty-surjective (⊢r-¬ε (s2-⊢r-l s) Z)
  = s-∀l regA₁ (≫-↑ty-st'0 regA regA₁ grd upp) (s1-strengthen=0 (⊢d²→⊢d s) upp (↑ty-arr upC upD) upj) ic fd upj
⊢d²→⊢d (s-∀l-no-appear grd regA s ic fd upC upD upj)
  with reg-S^ r ← s2-sregular s
  with ⟨ preA% , upp ⟩ ← ↑ty-surjective (⊢r-¬ε-^ (s2-⊢r-l s) Z)
  with ⟨ preA , upA ⟩ ← ↑ty-surjective fd
  with refl ← ⊢r-≫-eq' (⊢r-weaken^0 (⊢r-strengthen∙0 regA upA) upA) grd
  = s-∀l-no-appear ⊢r-int (↑ty-st upp) (s1-strengthen^0 (⊢d²→⊢d s) upp (↑ty-arr upC upD) upj) ic fd
⊢d²→⊢d (s-tapp grd regA s upj)
  with reg-S= r regA₁ ← s2-sregular s
  with ⟨ preA% , upp ⟩ ← ↑ty-surjective (⊢r-¬ε (s2-⊢r-l s) Z)
  with ⟨ preC , uppC ⟩ ← ↑ty-surjective (⊢r-¬ε (s2-⊢r-r s) Z)
  = s-tapp regA₁ (≫-↑ty-st'0 regA regA₁ grd upp) (s1-strengthen=0 (⊢d²→⊢d s) upp uppC upj) uppC
