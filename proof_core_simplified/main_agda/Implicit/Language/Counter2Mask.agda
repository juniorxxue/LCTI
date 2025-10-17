module Implicit.Language.Counter2Mask where

open import Implicit.Language.Base

data Counter : Set where
  Z : Counter
  ∞ : Counter
  𝕚 : Counter → Counter
  𝕔 : Counter → Counter


c2m : Counter → Mask
c2m Z = ` ■
c2m ∞ = ` □
c2m (𝕚 j) = □ · c2m j
c2m (𝕔 j) = ■ · c2m j

m2c : Mask → Counter
m2c (` □) = ∞
m2c (` ■) = Z
m2c (□ · m) = 𝕚 (m2c m)
m2c (■ · m) = 𝕔 (m2c m)


iso1 : ∀ j
  → c2m (m2c j) ≡ j
iso1 (` □) = refl
iso1 (` ■) = refl
iso1 (□ · j) = cong₂ _·_ refl (iso1 j)
iso1 (■ · j) = cong₂ _·_ refl (iso1 j)

iso2 : ∀ j
  → m2c (c2m j) ≡ j
iso2 Z = refl
iso2 ∞ = refl
iso2 (𝕚 j) = cong 𝕚 (iso2 j)
iso2 (𝕔 j) = cong 𝕔 (iso2 j)
