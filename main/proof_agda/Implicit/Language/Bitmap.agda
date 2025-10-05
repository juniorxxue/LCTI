module Implicit.Language.Bitmap where

open import Implicit.Language.Prelude
open import Implicit.Language.Base

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

orHit-total : ∀ (H₁ H₂ : HitMis m)
  → ∃[ H ](orHit H₁ H₂ H)
orHit-total ∅ ∅ = ⟨ ∅ , Z ⟩
orHit-total (hit H₁) (hit H₂) = ⟨ hit (orHit-total H₁ H₂ .proj₁) , S-hh (orHit-total H₁ H₂ .proj₂) ⟩
orHit-total (hit H₁) (mis H₂) = ⟨ hit (orHit-total H₁ H₂ .proj₁) , S-hm (orHit-total H₁ H₂ .proj₂) ⟩
orHit-total (mis H₁) (hit H₂) = ⟨ hit (orHit-total H₁ H₂ .proj₁) , S-mh (orHit-total H₁ H₂ .proj₂) ⟩
orHit-total (mis H₁) (mis H₂) = ⟨ mis (orHit-total H₁ H₂ .proj₁) , s-mm (orHit-total H₁ H₂ .proj₂) ⟩

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

𝕗𝕧-total : ∀ {m} (A : Type m)
         → ∃[ H ](A 𝕗𝕧 H)
𝕗𝕧-total {m} Int = ⟨ mkMis , fv-Int ⟩
𝕗𝕧-total (‶ X) = ⟨ mkHit X , fv-var ⟩
𝕗𝕧-total (A `→ B)
  with ⟨ H1 , fv1 ⟩ ← 𝕗𝕧-total A
  with ⟨ H2 , fv2 ⟩ ← 𝕗𝕧-total B
  with ⟨ H , or-hit ⟩ ← orHit-total H1 H2
  = ⟨ H , fv-arr fv1 fv2 or-hit ⟩
𝕗𝕧-total (`∀ A) with 𝕗𝕧-total A
... | ⟨ hit H , fv ⟩ = ⟨ H , fv-∀-h fv ⟩
... | ⟨ mis H , fv ⟩ = ⟨ H , fv-∀-m fv ⟩
