module Implicit.Annotatability.IF where

open import Implicit.Language.All
-- open import Implicit.Decl.All
open import Implicit.Annotatability.DeclPartial
open import Implicit.Decl.Subtyping
open import Implicit.Annotatability.Elaboration

private variable
  𝕛 𝕛' : Counter m

infix 3 _⊢_⟾_
data _⊢_⟾_ : Env n m → Counter m × Type m → Counter m × Type m → Set where

  base : Γ ⊢ A 𝕄 B
       → Γ ⊢ ⟨ ∞ , A ⟩ ⟾ ⟨ 𝕚 ∞ , B ⟩

  case-𝕚 : Γ ⊢ ⟨ j , B ⟩ ⟾ ⟨ 𝕛 , D ⟩
         → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ⟾ ⟨ 𝕚 𝕛 , A `→ D ⟩

  case-𝕔 : Γ ⊢ ⟨ j , B ⟩ ⟾ ⟨ 𝕛 , D ⟩
         → Γ ⊢ ⟨ 𝕔 j , A `→ B ⟩ ⟾ ⟨ 𝕔 𝕛 , A `→ D ⟩

  case-𝕥 : Γ ⊢ ⟨ j , A* ⟩ ⟾ ⟨ 𝕛 , B* ⟩
         → (upj : ↑tyʲ0 j ⇘ j')
         → (up𝕛 : ↑tyʲ0 𝕛 ⇘ 𝕛')
         → ⟦ T ⟧ A ⇘ A*
         → (upB* : ↑ty0 B* ⇘ B)
         → Γ ⊢ ⟨ 𝕥₍ T ₎ j , `∀ A ⟩ ⟾ ⟨ 𝕥₍ T ₎ 𝕛 , `∀ B ⟩

⟾-NonZ : NonZ j
       → Γ ⊢ ⟨ j , A ⟩ ⟾ ⟨ 𝕛 , B ⟩
       → NonZ 𝕛
⟾-NonZ nz-∞ (base x) = nz-I
⟾-NonZ nz-I (case-𝕚 ~j) = nz-I
⟾-NonZ nz-C (case-𝕔 ~j) = nz-C
⟾-NonZ nz-T (case-𝕥 cv upj up𝕛 x upB*) = nz-T

𝕄-weaken⋈ : Γ ⊢ A 𝕄 B
          → Γ ⋈ ⊢ A 𝕄 B
𝕄-weaken⋈ 𝕄-arr = 𝕄-arr
𝕄-weaken⋈ (M-∀ x st mm) = M-∀ (⊢r-𝕣 x) st (𝕄-weaken⋈ mm)

⟾-weaken⋈ : Γ ⊢ ⟨ j , A ⟩ ⟾ ⟨ 𝕛 , B ⟩
           → Γ ⋈ ⊢ ⟨ j , A ⟩ ⟾ ⟨ 𝕛 , B ⟩
⟾-weaken⋈ (base x) = base (𝕄-weaken⋈ x)
⟾-weaken⋈ (case-𝕚 ~j) = case-𝕚 (⟾-weaken⋈ ~j)
⟾-weaken⋈ (case-𝕔 ~j) = case-𝕔 (⟾-weaken⋈ ~j)
⟾-weaken⋈ (case-𝕥 cv upj up𝕛 x upB*) = case-𝕥 (⟾-weaken⋈ cv) upj up𝕛 x upB*

𝕄-weaken^0 : Γ ⊢ A 𝕄 B
           → ↑ty0 A ⇘ A'
           → ↑ty0 B ⇘ B'
           → Γ ,^ ⊢ A' 𝕄 B'
𝕄-weaken^0 𝕄-arr (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  with refl ← ↑ty-unique upA upB
  with refl ← ↑ty-unique upA₁ upB₁ = 𝕄-arr
𝕄-weaken^0 (M-∀ {T = T} {A* = A*} x st mm) (↑ty-∀ upA) (↑ty-arr upB upB₁)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  with ⟨ A*' , upA* ⟩ ← ↑ty0-total A*
  = M-∀ (⊢r-weaken^0 x upT) (↑ty-st-comm z≤n st upA upT upA*) (𝕄-weaken^0 mm upA* (↑ty-arr upB upB₁))

𝕄-weaken,0 : Γ ⊢ A 𝕄 B
           → Γ ⊢r T
           → Γ , T ⊢ A 𝕄 B
𝕄-weaken,0 𝕄-arr regT = 𝕄-arr
𝕄-weaken,0 (M-∀ x st mm) regT = M-∀ (⊢r-weaken,0 x regT) st (𝕄-weaken,0 mm regT)

⟾-weaken,0 : Γ ⊢ ⟨ j , A ⟩ ⟾ ⟨ 𝕛 , B ⟩
           → Γ ⊢r T
           → Γ , T ⊢ ⟨ j , A ⟩ ⟾ ⟨ 𝕛 , B ⟩
⟾-weaken,0 (base x) regT = base (𝕄-weaken,0 x regT)
⟾-weaken,0 (case-𝕚 ~j) regT = case-𝕚 (⟾-weaken,0 ~j regT)
⟾-weaken,0 (case-𝕔 ~j) regT = case-𝕔 (⟾-weaken,0 ~j regT)
⟾-weaken,0 (case-𝕥 cv upj up𝕛 x upB*) regT = case-𝕥 (⟾-weaken,0 cv regT) upj up𝕛 x upB*

⟾-isoinf : IsoInf j
         → Γ ⊢ ⟨ j , B ⟩ ⟾ ⟨ 𝕛 , D ⟩
         → IsoInf 𝕛
⟾-isoinf i∞-z (case-𝕚 (base x)) = i∞-i i∞-z
⟾-isoinf (i∞-i iso) (case-𝕚 cv) = i∞-i (⟾-isoinf iso cv)


⟾-weaken^0 : Γ ⊢ ⟨ j , A ⟩ ⟾ ⟨ 𝕛 , B ⟩
            → ↑tyʲ0 j ⇘ j'
            → ↑tyʲ0 𝕛 ⇘ 𝕛'
            → ↑ty0 A ⇘ A'
            → ↑ty0 B ⇘ B'
            → Γ ,^ ⊢ ⟨ j' , A' ⟩ ⟾ ⟨ 𝕛' , B' ⟩

⟾-weaken^0 (base x) ↑tyʲ-∞ (↑tyʲ-𝕚 ↑tyʲ-∞) upA upB = base (𝕄-weaken^0 x upA upB)
⟾-weaken^0 (case-𝕚 cv) (↑tyʲ-𝕚 upj) (↑tyʲ-𝕚 up𝕛) (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  with refl ← ↑ty-unique upA upB = case-𝕚 (⟾-weaken^0 cv upj up𝕛 upA₁ upB₁)
⟾-weaken^0 (case-𝕔 cv) (↑tyʲ-𝕔 upj) (↑tyʲ-𝕔 up𝕛) (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  with refl ← ↑ty-unique upA upB = case-𝕔 (⟾-weaken^0 cv upj up𝕛 upA₁ upB₁)
⟾-weaken^0 (case-𝕥 cv upj₁ up𝕛₁ x upB*) (↑tyʲ-𝕥 upj upA₁) (↑tyʲ-𝕥 up𝕛 upA₂) (↑ty-∀ upA) (↑ty-∀ upB)
  = {!!}

find-iso-gen : k ε A
             → find A k (𝕚 ∞)
find-iso-gen ε-var = f-iso i∞-z
find-iso-gen (ε-arr-l inA) = f-arr-𝕚-l inA
find-iso-gen (ε-arr-r ¬inA inA) = f-arr-𝕚-r ¬inA (f-∞ inA)
find-iso-gen (ε-∀ inA) = f-∀-𝕚 (find-iso-gen inA) ↑tyʲ-∞

⟾-find : find A k j
        → Γ ⊢ ⟨ j , B ⟩ ⟾ ⟨ 𝕛 , C ⟩
        → find A k 𝕛
⟾-find (f-∞ inA) (base x) = find-iso-gen inA
⟾-find (f-iso iso) b = f-iso (⟾-isoinf iso b)
⟾-find (f-arr-𝕚-l x) (case-𝕚 cv) = f-arr-𝕚-l x
⟾-find (f-arr-𝕚-r ¬inA fd) (case-𝕚 cv) = f-arr-𝕚-r ¬inA (⟾-find fd cv)
⟾-find (f-arr-𝕔 ¬inA fd) (case-𝕔 cv) = f-arr-𝕔 ¬inA (⟾-find fd cv)
⟾-find (f-∀-𝕚 fd upj) (case-𝕚 {B = B} {𝕛 = 𝕛} {D = C} cv)
  with ⟨ 𝕛' , up𝕛 ⟩ ← ↑tyʲ0-total 𝕛
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with ⟨ C' , upC ⟩ ← ↑ty0-total C = f-∀-𝕚 (⟾-find fd (case-𝕚 {A = Int} (⟾-weaken^0 cv upj up𝕛 upB upC))) up𝕛
⟾-find (f-∀-𝕔 fd upj) (case-𝕔 {B = B} {𝕛 = 𝕛} {D = C} cv)
  with ⟨ 𝕛' , up𝕛 ⟩ ← ↑tyʲ0-total 𝕛
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with ⟨ C' , upC ⟩ ← ↑ty0-total C = f-∀-𝕔 (⟾-find fd (case-𝕔  {A = Int} (⟾-weaken^0 cv upj up𝕛 upB upC))) up𝕛
⟾-find (f-𝕥 fd upj) (case-𝕥 {A* = A*} cv upj₁ up𝕛 x upB*)
  with ⟨ A*' , upA* ⟩ ← ↑ty0-total A* = f-𝕥 (⟾-find fd (⟾-weaken^0 cv upj up𝕛 upA* upB*)) up𝕛

mm-sub : Γ ⊢ A 𝕄 B
       → SRegular Γ
       → Γ ⊢r A
       → Γ ⊢d 𝕚 ∞ # A ≤ B
mm-sub 𝕄-arr regΓ (⊢r-arr regA regA₁) = s-arr₂ (s-refl-∞ regΓ regA) (s-refl-∞ regΓ regA₁)
mm-sub (M-∀ {A = A} x st mm) regΓ regA with ε-dec {k = #0} {A = A}
... | inj₁ p = s-∀l x st (mm-sub mm regΓ (st0-⊢r regA x st)) case-𝕚 (find-iso-gen p) (↑tyʲ-𝕚 ↑tyʲ-∞)
... | inj₂ ¬p = s-∀l-no-appear x st (mm-sub mm regΓ (st0-⊢r regA x st)) case-𝕚 ¬p

conv-sub-gen-s : Γ ⊢d j # A ≤ B
               → Γ ⊢ ⟨ j , B ⟩ ⟾ ⟨ j' , C ⟩
               → Γ ⊢d j' # A ≤ C  --- we need to generalize the conclusion
conv-sub-gen-s (s-int regΔ) (base ())
conv-sub-gen-s (s-var-∙ regΔ inΔ) (base ())
conv-sub-gen-s (s-arr₁ s s₁) (base 𝕄-arr) = s-arr₂ s s₁
conv-sub-gen-s (s-arr₂ s s₁) (case-𝕚 cv) = s-arr₂ s (conv-sub-gen-s s₁ cv)
conv-sub-gen-s (s-arr₃ regA s) (case-𝕔 cv) = s-arr₃ regA (conv-sub-gen-s s cv)
conv-sub-gen-s (s-∀ s) (base mm)
  with refl ← s-trans-∞-eq s  = mm-sub mm (s-sregular (s-∀ s)) (⊢r-∀ (s1-⊢r-l s))
conv-sub-gen-s (s-∀l regB st s case-𝕚 fd (↑tyʲ-𝕚 upj)) (case-𝕚 {B = B} {𝕛 = 𝕛} {D = D} cv)
  with ⟨ 𝕛' , up𝕛 ⟩ ← ↑tyʲ0-total 𝕛
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with ⟨ D' , upD ⟩ ← ↑ty0-total D
  = s-∀l regB st (conv-sub-gen-s s (case-𝕚 cv)) case-𝕚 (⟾-find fd (case-𝕚  {A = Int} (⟾-weaken^0 cv upj up𝕛 upB upD))) (↑tyʲ-𝕚 up𝕛)
conv-sub-gen-s (s-∀l regB st s case-𝕔 fd (↑tyʲ-𝕔 upj)) (case-𝕔 {B = B} {𝕛 = 𝕛} {D = D} cv)
  with ⟨ 𝕛' , up𝕛 ⟩ ← ↑tyʲ0-total 𝕛
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with ⟨ D' , upD ⟩ ← ↑ty0-total D
  = s-∀l regB st (conv-sub-gen-s s (case-𝕔 cv)) case-𝕔 (⟾-find fd (case-𝕔  {A = Int} (⟾-weaken^0 cv upj up𝕛 upB upD))) (↑tyʲ-𝕔 up𝕛)
conv-sub-gen-s (s-∀l-no-appear regB st s case-𝕚 fd) (case-𝕚 cv) = s-∀l-no-appear regB st (conv-sub-gen-s s (case-𝕚 cv)) case-𝕚 fd
conv-sub-gen-s (s-∀l-no-appear regB st s case-𝕔 fd) (case-𝕔 cv) = s-∀l-no-appear regB st (conv-sub-gen-s s (case-𝕔 cv)) case-𝕔 fd
conv-sub-gen-s (s-tapp regB st x₁ upC) (case-𝕥 cv upj up𝕛 x upB*)
  with refl ← ↑ty-st-eq upC x = s-tapp regB st (conv-sub-gen-s x₁ cv) upB*

conv-sub-gen : Γ ⊢ j # e ⦂ A
             → Γ ⊢ ⟨ j , A ⟩ ⟾ ⟨ 𝕛 , B ⟩
             → Γ ⊢ 𝕛 # e ⦂ B
conv-sub-gen (⊢lam₁ ⊢e) (base 𝕄-arr) = ⊢lam₂ ⊢e
conv-sub-gen (⊢lam₂ ⊢e) (case-𝕚 cv) with t-tregular ⊢e
... | reg-S, r regA = ⊢lam₂ (conv-sub-gen ⊢e (⟾-weaken,0 cv regA))
conv-sub-gen (⊢app₁ ⊢e ⊢e₁) cv = ⊢app₁ (conv-sub-gen ⊢e (case-𝕔 cv)) ⊢e₁
conv-sub-gen (⊢app₂ ⊢e ⊢e₁) cv = ⊢app₂ (conv-sub-gen ⊢e (case-𝕚 cv)) ⊢e₁
conv-sub-gen (⊢sub ⊢e B≤A gc j≢Z) cv = ⊢sub ⊢e (conv-sub-gen-s B≤A (⟾-weaken⋈ cv)) gc (⟾-NonZ j≢Z cv)
conv-sub-gen {j = j} {𝕛 = 𝕛} {B = B} (⊢tapp ⊢e st) mm
  with ⟨ j' , upj ⟩ ← ↑tyʲ0-total j
  with ⟨ 𝕛' , up𝕛 ⟩ ← ↑tyʲ0-total 𝕛
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  = ⊢tapp (conv-sub-gen ⊢e (case-𝕥 mm upj up𝕛 st upB)) (↑ty-st upB)

conv-sub : Γ ⊢ ∞ # e ⦂ A
         → Γ ⊢ A 𝕄 B
         → Γ ⊢ 𝕚 ∞ # e ⦂ B
conv-sub ⊢e cv = conv-sub-gen ⊢e (base cv)


annotatability : Γ ⊢ e ⦂ A ⟶ e'
               → Γ ⊢ ∞ # e' ⦂ A
annotatability (ela-lit reg) = ⊢sub (⊢lit reg) (s-int (reg-Z reg)) gc-i nz-∞
annotatability (ela-var reg x) = ⊢sub (⊢var reg x) (s-refl-∞ (reg-Z reg) (⊢r-𝕣 (∋⦂-⊢r reg x))) gc-var nz-∞
annotatability (ela-lam ⊢e) = ⊢lam₁ (annotatability ⊢e)
annotatability (ela-app ⊢e cv ⊢e₁) = ⊢app₂ (conv-sub (annotatability ⊢e) cv) (⊢ann (annotatability ⊢e₁))
annotatability (ela-app-g ⊢e cv (ela-lit regΓ) gc-i) = ⊢app₂ (conv-sub (annotatability ⊢e) cv) (⊢lit regΓ)
annotatability (ela-app-g ⊢e cv (ela-∀i ⊢e₁ upe) gc-i) =
  ⊢app₂ (conv-sub (annotatability ⊢e) cv) (⊢tabs (⊢ann (annotatability ⊢e₁)))
annotatability (ela-app-g ⊢e cv (ela-var regΓ x) gc-var)
  = ⊢app₂ (conv-sub (annotatability ⊢e) cv) (⊢var regΓ x)
annotatability (ela-app-g ⊢e cv (ela-∀i ⊢e₁ upe) gc-var)
  = ⊢app₂ (conv-sub (annotatability ⊢e) cv) (⊢tabs (⊢ann (annotatability ⊢e₁)))
annotatability (ela-app-g ⊢e cv (ela-∀i ⊢e₁ upe) gc-ann)
  = ⊢app₂ (conv-sub (annotatability ⊢e) cv) (⊢tabs (⊢ann (annotatability ⊢e₁)))
annotatability (ela-app-g ⊢e cv (ela-∀i ⊢e₁ upe) gc-tlam)
  = ⊢app₂ (conv-sub (annotatability ⊢e) cv) (⊢tabs (⊢ann (annotatability ⊢e₁)))
annotatability (ela-∀i ⊢e upe) = ⊢sub (⊢tabs (⊢ann (annotatability ⊢e)))
  (s-refl-∞ (reg-Z (ela-tregular (ela-∀i ⊢e upe))) (⊢r-𝕣 (⊢r-∀ (ela-⊢r ⊢e)))) gc-tlam nz-∞


annotatability' : Γ ⊢ e ⦂ A ⟶ e'
                → Γ ⊢ Z # (e' ⦂ A) ⦂ A
annotatability' ⊢e = ⊢ann (annotatability ⊢e)
