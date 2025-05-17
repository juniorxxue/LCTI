module Implicit.Decl.Equiv where

open import Implicit.Language.All
open import Implicit.Decl.Subtyping renaming (_⊢_#_≤_ to _⊢¹_#_≤_)
open import Implicit.Decl.SubtypingV2 renaming (_⊢_#_≤_ to _⊢²_#_≤_)
open import Implicit.Decl.AuxLemmas



▶∙-punchOut-helper : Γ ∋∙ X
                   → Γ ▶ #0 ,∙⇘ Γ'
                   → Γ' ∋∙ #S X
▶∙-punchOut-helper inΓ ▶Z = S∙ inΓ
▶∙-punchOut-helper (S, inΓ) (▶S, new x) = S, (▶∙-punchOut-helper inΓ new)
▶∙-punchOut-helper (S⋈ inΓ) (▶S⋈ new) = S⋈ (▶∙-punchOut-helper inΓ new)

▶∙-punchOut : (¬p : k ≢ X)
            → Γ ∋∙ punchOut ¬p
            → Γ ▶ k ,∙⇘ Γ'
            → Γ' ∋∙ X
▶∙-punchOut {k = #0} {X = #0} ¬p inΓ new = ⊥-elim (¬p refl)
▶∙-punchOut {k = #0} {X = #S X} ¬p inΓ ▶Z = S∙ inΓ
▶∙-punchOut {k = #0} {X = #S X} ¬p (S, inΓ) (▶S, new x) = S, (▶∙-punchOut-helper inΓ new)
▶∙-punchOut {k = #0} {X = #S X} ¬p (S⋈ inΓ) (▶S⋈ new) = S⋈ (▶∙-punchOut-helper inΓ new)
▶∙-punchOut {k = #S k} {X = #0} ¬p (S, inΓ) (▶S, new x) = S, (▶∙-punchOut ¬p inΓ new)
▶∙-punchOut {k = #S k} {X = #0} ¬p inΓ (▶S∙ new) = Z
▶∙-punchOut {k = #S k} {X = #0} ¬p (S⋈ inΓ) (▶S⋈ new) = S⋈ (▶∙-punchOut ¬p inΓ new)
▶∙-punchOut {k = #S k} {X = #S X} ¬p (S, inΓ) (▶S, new x) = S, (▶∙-punchOut ¬p inΓ new)
▶∙-punchOut {k = #S k} {X = #S X} ¬p (S^ inΓ) (▶S^ new) = S^ (▶∙-punchOut (λ x → ¬p (cong #S x)) inΓ new)
▶∙-punchOut {k = #S k} {X = #S X} ¬p (S∙ inΓ) (▶S∙ new) = S∙ (▶∙-punchOut (λ x → ¬p (cong #S x)) inΓ new)
▶∙-punchOut {k = #S k} {X = #S X} ¬p (S= inΓ) (▶S= new x) = S= (▶∙-punchOut (λ x₁ → ¬p (cong #S x₁)) inΓ new)
▶∙-punchOut {k = #S k} {X = #S X} ¬p (S⋈ inΓ) (▶S⋈ new) = S⋈ (▶∙-punchOut ¬p inΓ new)


st-⊢r'' : Γ ⊢r A*
       → Γ ▶ k ,∙⇘ Γ'
       → Γ ⊢r T
       → ⟦ k / T ⟧ A ⇘ A*
       → Γ' ⊢r A
st-⊢r'' ⊢r-int new regT st-int = ⊢r-int
st-⊢r'' ⊢r-int new regT (st-var stx-eq) = ⊢r-var-∙ (▶∙-∋∙ new)
st-⊢r'' (⊢r-var-∙ inΓ) new regT (st-var stx-eq) = ⊢r-var-∙ (▶∙-∋∙ new)
st-⊢r'' (⊢r-var-∙ inΓ) new regT (st-var (stx-neq ¬p)) = ⊢r-var-∙ (▶∙-punchOut ¬p inΓ new)
st-⊢r'' (⊢r-arr regA regA₁) new regT (st-var stx-eq) = st-⊢r'' regA₁ new regA₁ (st-var stx-eq)
st-⊢r'' (⊢r-arr regA regA₁) new regT (st-arr st st₁) = ⊢r-arr (st-⊢r'' regA new regT st) (st-⊢r'' regA₁ new regT st₁)
st-⊢r'' (⊢r-∀ regA) new regT (st-var stx-eq) = ⊢r-var-∙ (▶∙-∋∙ new)
st-⊢r'' (⊢r-∀ regA) new regT (st-∀ up st) = ⊢r-∀ (st-⊢r'' regA (▶S∙ new) (⊢r-weaken∙0 regT up) st)


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

sound : Γ ⊢¹ j # A ≤ B
      → Γ ⊢² j # A ≤ B
sound (s-refl regΔ cloA) = s-refl regΔ cloA
sound (s-int regΔ) = s-int regΔ
sound (s-var-∙ regΔ inΔ) = s-var-∙ regΔ inΔ
sound (s-arr₁ s s₁) = s-arr₁ (sound s) (sound s₁)
sound (s-arr₂ s s₁) = s-arr₂ (sound s) (sound s₁)
sound (s-arr₃ regA s) = s-arr₃ regA (sound s)
sound (s-∀ s) = s-∀ (sound s)
sound (s-∀l {B = B} {A* = A*} {C = C} {D = D} regB st s ic fd upj)
  with ⟨ C' , upC ⟩ ← ↑ty0-total C
  with ⟨ D' , upD ⟩ ← ↑ty0-total D
  with ⟨ A*' , upA* ⟩ ← ↑ty0-total A*
  with regA* ← s1-⊢r-l s
  with regA ← st-⊢r'' regA* ▶Z regB st
  = s-∀l {B = B} {A% = A*'} (st-↑ty-≫0 st regA* upA* regB) regA (s2-weaken=0 (sound s) upA* (↑ty-arr upC upD) upj regB) ic fd upC upD upj
sound (s-tapp {A* = A*} {j = j} regB st s upC)
  with ⟨ A*' , upA* ⟩ ← ↑ty0-total A*
  with ⟨ j' , upj ⟩ ← ↑tyʲ0-total j
  = s-tapp (st-↑ty-≫0 st (s1-⊢r-l s) upA* regB) (st-⊢r'' (s1-⊢r-l s) ▶Z regB st) (s2-weaken=0 (sound s) upA* upC upj regB) upj

complete : Γ ⊢² j # A ≤ B
         → Γ ⊢¹ j # A ≤ B
complete (s-refl regΔ cloA) = s-refl regΔ cloA
complete (s-int regΔ) = s-int regΔ
complete (s-var-∙ regΔ inΔ) = s-var-∙ regΔ inΔ
complete (s-arr₁ s s₁) = s-arr₁ (complete s) (complete s₁)
complete (s-arr₂ s s₁) = s-arr₂ (complete s) (complete s₁)
complete (s-arr₃ regA s) = s-arr₃ regA (complete s)
complete (s-∀ s) = s-∀ (complete s)
complete (s-∀l {B = B} grd regA s ic fd upC upD upj)
  with reg-S= r regA₁ ← s2-sregular s
  with ⟨ preA% , upp ⟩ ← ↑ty-surjective (⊢r-¬ε (s2-⊢r-l s) Z)
  = s-∀l regA₁ (≫-↑ty-st'0 regA regA₁ grd upp) (s1-strengthen=0 (complete s) upp (↑ty-arr upC upD) upj) ic fd upj
complete (s-tapp grd regA s upj)
  with reg-S= r regA₁ ← s2-sregular s
  with ⟨ preA% , upp ⟩ ← ↑ty-surjective (⊢r-¬ε (s2-⊢r-l s) Z)
  with ⟨ preC , uppC ⟩ ← ↑ty-surjective (⊢r-¬ε (s2-⊢r-r s) Z)
  = s-tapp regA₁ (≫-↑ty-st'0 regA regA₁ grd upp) (s1-strengthen=0 (complete s) upp uppC upj) uppC
