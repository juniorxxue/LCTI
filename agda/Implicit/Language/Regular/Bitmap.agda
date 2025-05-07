module Implicit.Language.Regular.Bitmap where

open import Implicit.Language.Base
open import Implicit.Language.Shift.Base

{-

Γ ⊢ e ≊ ∀ x in fv(e), x is in Γ

Γ := ∅
   | Γ , x : A
   | Γ , a
   | Γ , â
   | Γ , â = A

-}

data HitMis : ℕ → Set where
  ∅ : HitMis 0
  hit : HitMis m → HitMis (1 + m)
  mis : HitMis m → HitMis (1 + m)

variable
  H H₁ H₂ : HitMis m

mkMis : ∀ {m} → HitMis m
mkMis {zero} = ∅
mkMis {suc m} = mis (mkMis {m})

mkHit : ∀ {m} → Fin m → HitMis m
mkHit {suc m} #0 = hit (mkMis {m})
mkHit {suc m} (#S k) = mis (mkHit {m} k)

data orHit : HitMis m → HitMis m → HitMis m → Set where
  Z : orHit ∅ ∅ ∅
  S-hm : orHit H₁ H₂ H
    → orHit (hit H₁) (mis H₂) (hit H)
  S-mh : orHit H₁ H₂ H
    → orHit (mis H₁) (hit H₂) (hit H)
  S-hh : orHit H₁ H₂ H
    → orHit (hit H₁) (hit H₂) (hit H)
  s-mm : orHit H₁ H₂ H
    → orHit (mis H₁) (mis H₂) (mis H)

infix 3 _𝕗𝕧_
data _𝕗𝕧_ : Type m → HitMis m → Set where
  fv-Int : ∀ {m} → (Type m ∋⦂ Int) 𝕗𝕧 mkMis {m}
  fv-var : (‶ X) 𝕗𝕧 mkHit X
  fv-arr : A 𝕗𝕧 H₁
         → B 𝕗𝕧 H₂
         → orHit H₁ H₂ H
         → A `→ B 𝕗𝕧 H
  fv-∀-h : A 𝕗𝕧 (hit H)
         → `∀ A 𝕗𝕧 H
  fv-∀-m : A 𝕗𝕧 (mis H)
         → `∀ A 𝕗𝕧 H

data AllUVars : Env n m → HitMis m → Set where
  au-Z : AllUVars ∅ ∅
  au-h : AllUVars Γ H
       → AllUVars (Γ ,∙) (hit H)
  au-m1 : AllUVars Γ H
       → AllUVars (Γ ,^) (mis H)
  au-m2 : AllUVars Γ H
       → AllUVars (Γ ,= A) (mis H)
  au-, : AllUVars Γ H
       → AllUVars (Γ , A) H
  au-⋈ : AllUVars Γ H
       → AllUVars (Γ ⋈) H

infix 3 _⊢r_
data _⊢r_ (Γ : Env n m) (A : Type m) : Set where
  all-uvars : (fv : A 𝕗𝕧 H)
            → (allu : AllUVars Γ H)
            → Γ ⊢r A

⊢r-weaken,0 : Γ ⊢r A
            → Γ , T ⊢r A
⊢r-weaken,0 (all-uvars fv allu) = all-uvars fv (au-, allu)

⊢r-weaken^0 : Γ ⊢r A
            → ↑ty0 A ⇘ A'
            → Γ ,^ ⊢r A'
⊢r-weaken^0 (all-uvars fv allu) upA = all-uvars {!!} (au-m1 allu)
