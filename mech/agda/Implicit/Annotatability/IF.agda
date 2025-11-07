module Implicit.Annotatability.IF where

open import Implicit.Language.All
open import Implicit.Annotatability.DeclPartial
open import Implicit.Decl.Subtyping
open import Implicit.Annotatability.Elaboration

private variable
  𝕛 𝕛' : Mask

infix 3 _⊢_⟾_
data _⊢_⟾_ : Env n m → Mask × Type m → Mask × Type m → Set where

  base : Γ ⊢ A 𝕄 B
       → Γ ⊢ ⟨ ` □ , A ⟩ ⟾ ⟨ □ · `□ , B ⟩

  case-S : Γ ⊢ ⟨ j , B ⟩ ⟾ ⟨ 𝕛 , D ⟩
         → Γ ⊢ ⟨ i · j , A `→ B ⟩ ⟾ ⟨ i · 𝕛 , A `→ D ⟩


⟾-NonZ : NonZ j
       → Γ ⊢ ⟨ j , A ⟩ ⟾ ⟨ 𝕛 , B ⟩
       → NonZ 𝕛
⟾-NonZ nz-□ (base x) = nz-app
⟾-NonZ nz-app (case-S nj) = nz-app

𝕄-weaken⋈ : Γ ⊢ A 𝕄 B
          → Γ ⋈ ⊢ A 𝕄 B
𝕄-weaken⋈ 𝕄-arr = 𝕄-arr
𝕄-weaken⋈ (M-∀ x st mm) = M-∀ (⊢r-𝕣 x) st (𝕄-weaken⋈ mm)

⟾-weaken⋈ : Γ ⊢ ⟨ j , A ⟩ ⟾ ⟨ 𝕛 , B ⟩
           → Γ ⋈ ⊢ ⟨ j , A ⟩ ⟾ ⟨ 𝕛 , B ⟩
⟾-weaken⋈ (base x) = base (𝕄-weaken⋈ x)
⟾-weaken⋈ (case-S ~j) = case-S (⟾-weaken⋈ ~j)

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
⟾-weaken,0 (case-S ~j) regT = case-S (⟾-weaken,0 ~j regT)

⟾-isoinf : □like j
         → Γ ⊢ ⟨ j , B ⟩ ⟾ ⟨ 𝕛 , D ⟩
         → □like 𝕛
⟾-isoinf □like-Z (case-S (base x)) = □like-S □like-Z
⟾-isoinf (□like-S wlike) (case-S newj) = □like-S (⟾-isoinf wlike newj)

⟾-weaken^0 : Γ ⊢ ⟨ j , A ⟩ ⟾ ⟨ 𝕛 , B ⟩
            → ↑ty0 A ⇘ A'
            → ↑ty0 B ⇘ B'
            → Γ ,^ ⊢ ⟨ j , A' ⟩ ⟾ ⟨ 𝕛 , B' ⟩
⟾-weaken^0 (base x) upA upB = base (𝕄-weaken^0 x upA upB)
⟾-weaken^0 (case-S cv) (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  with refl ← ↑ty-unique upA upB = case-S (⟾-weaken^0 cv upA₁ upB₁)


find-iso-gen : k ε A
             → find A k (□ · `□)
find-iso-gen ε-var = f-iso □like-Z
find-iso-gen (ε-arr-l inA) = f-arr-l inA
find-iso-gen (ε-arr-r ¬inA inA) = f-arr-r ¬inA (f-□ inA)
find-iso-gen (ε-∀ inA) = f-∀ (find-iso-gen inA)

⟾-find : find A k j
        → Γ ⊢ ⟨ j , B ⟩ ⟾ ⟨ 𝕛 , C ⟩
        → find A k 𝕛
⟾-find (f-□ inA) (base x) = find-iso-gen inA
⟾-find (f-iso iso) b = f-iso (⟾-isoinf iso b)
⟾-find (f-arr-l x) (case-S cv) = f-arr-l x
⟾-find (f-arr-r ¬inA fd) (case-S cv) = f-arr-r ¬inA (⟾-find fd cv)
⟾-find (f-∀ fd) (case-S {B = B} {𝕛 = 𝕛} {D = C} cv)
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with ⟨ C' , upC ⟩ ← ↑ty0-total C = f-∀ (⟾-find fd (case-S {A = Int} (⟾-weaken^0 cv upB upC)))

mm-sub : Γ ⊢ A 𝕄 B
       → SRegular Γ
       → Γ ⊢r A
       → Γ ⊢d □ · `□ # A ≤ B
mm-sub 𝕄-arr regΓ (⊢r-arr regA regA₁) = s-arr₂ (s-refl-∞ regΓ regA) (s-refl-∞ regΓ regA₁)
mm-sub (M-∀ {A = A} x st mm) regΓ regA with ε-dec {k = #0} {A = A}
... | inj₁ p = s-∀l x st (mm-sub mm regΓ (st0-⊢r regA x st)) (find-iso-gen p)
... | inj₂ ¬p = s-∀l-no-appear x st (mm-sub mm regΓ (st0-⊢r regA x st)) ¬p

conv-sub-gen-s : Γ ⊢d j # A ≤ B
               → Γ ⊢ ⟨ j , B ⟩ ⟾ ⟨ j' , C ⟩
               → Γ ⊢d j' # A ≤ C  --- we need to generalize the conclusion
conv-sub-gen-s (s-int regΔ) (base ())
conv-sub-gen-s (s-var-∙ regΔ inΔ) (base ())
conv-sub-gen-s (s-arr₁ s s₁) (base 𝕄-arr) = s-arr₂ s s₁
conv-sub-gen-s (s-arr₂ s s₁) (case-S cv) = s-arr₂ s (conv-sub-gen-s s₁ cv)
conv-sub-gen-s (s-arr₃ regA s) (case-S cv) = s-arr₃ regA (conv-sub-gen-s s cv)
conv-sub-gen-s (s-∀ s) (base mm)
  with refl ← s-trans-∞-eq s  = mm-sub mm (s-sregular (s-∀ s)) (⊢r-∀ (s1-⊢r-l s))
conv-sub-gen-s (s-∀l regB st s fd ) (case-S {B = B} {𝕛 = 𝕛} {D = D} cv)
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with ⟨ D' , upD ⟩ ← ↑ty0-total D
  = s-∀l regB st (conv-sub-gen-s s (case-S cv)) (⟾-find fd (case-S {A = Int} (⟾-weaken^0 cv upB upD)))
conv-sub-gen-s (s-∀l-no-appear regB st s fd) (case-S cv) = s-∀l-no-appear regB st (conv-sub-gen-s s (case-S cv)) fd

conv-sub-gen : Γ ⊢ j # e ⦂ A
             → Γ ⊢ ⟨ j , A ⟩ ⟾ ⟨ 𝕛 , B ⟩
             → Γ ⊢ 𝕛 # e ⦂ B
conv-sub-gen (⊢lam₁ ⊢e) (base 𝕄-arr) = ⊢lam₂ ⊢e
conv-sub-gen (⊢lam₂ ⊢e) (case-S cv) with t-tregular ⊢e
... | reg-S, r regA = ⊢lam₂ (conv-sub-gen ⊢e (⟾-weaken,0 cv regA))
conv-sub-gen (⊢app ⊢e ⊢e₁) cv = ⊢app (conv-sub-gen ⊢e (case-S cv)) ⊢e₁
conv-sub-gen (⊢sub ⊢e B≤A gc j≢Z) cv = ⊢sub ⊢e (conv-sub-gen-s B≤A (⟾-weaken⋈ cv)) gc (⟾-NonZ j≢Z cv)

conv-sub : Γ ⊢ `□ # e ⦂ A
         → Γ ⊢ A 𝕄 B
         → Γ ⊢ □ · `□ # e ⦂ B
conv-sub ⊢e cv = conv-sub-gen ⊢e (base cv)


annotatability : Γ ⊢ e ⦂ A ⟶ e'
               → Γ ⊢ `□ # e' ⦂ A
annotatability (ela-lit reg) = ⊢sub (⊢lit reg) (s-int (reg-Z reg)) gc-i nz-□
annotatability (ela-var reg x) = ⊢sub (⊢var reg x) (s-refl-∞ (reg-Z reg) (⊢r-𝕣 (∋⦂-⊢r reg x))) gc-var nz-□
annotatability (ela-lam ⊢e) = ⊢lam₁ (annotatability ⊢e)
annotatability (ela-app ⊢e cv ⊢e₁) = ⊢app (conv-sub (annotatability ⊢e) cv) (⊢ann (annotatability ⊢e₁))
annotatability (ela-app-g ⊢e cv (ela-lit regΓ) gc-i) = ⊢app (conv-sub (annotatability ⊢e) cv) (⊢lit regΓ)
annotatability (ela-app-g ⊢e cv (ela-∀i ⊢e₁ upe) gc-i) =
  ⊢app (conv-sub (annotatability ⊢e) cv) (⊢tabs (⊢ann (annotatability ⊢e₁)))
annotatability (ela-app-g ⊢e cv (ela-var regΓ x) gc-var)
  = ⊢app (conv-sub (annotatability ⊢e) cv) (⊢var regΓ x)
annotatability (ela-app-g ⊢e cv (ela-∀i ⊢e₁ upe) gc-var)
  = ⊢app (conv-sub (annotatability ⊢e) cv) (⊢tabs (⊢ann (annotatability ⊢e₁)))
annotatability (ela-app-g ⊢e cv (ela-∀i ⊢e₁ upe) gc-ann)
  = ⊢app (conv-sub (annotatability ⊢e) cv) (⊢tabs (⊢ann (annotatability ⊢e₁)))
annotatability (ela-app-g ⊢e cv (ela-∀i ⊢e₁ upe) gc-tlam)
  = ⊢app (conv-sub (annotatability ⊢e) cv) (⊢tabs (⊢ann (annotatability ⊢e₁)))
annotatability (ela-∀i ⊢e upe) = ⊢sub (⊢tabs (⊢ann (annotatability ⊢e)))
  (s-refl-∞ (reg-Z (ela-tregular (ela-∀i ⊢e upe))) (⊢r-𝕣 (⊢r-∀ (ela-⊢r ⊢e)))) gc-tlam nz-□


annotatability' : Γ ⊢ e ⦂ A ⟶ e'
                → Γ ⊢ `■ # (e' ⦂ A) ⦂ A
annotatability' ⊢e = ⊢ann (annotatability ⊢e)
