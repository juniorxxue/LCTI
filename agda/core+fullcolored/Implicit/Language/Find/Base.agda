module Implicit.Language.Find.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.Base
open import Implicit.Language.Occur.Base
open import Implicit.Language.Regular.Base

infix 3 _↑tyʲ_⇘_
data _↑tyʲ_⇘_ : Counter m → Fin (1 + m) → Counter (1 + m) → Set where
  ↑tyʲ-𝔼 : 𝔼 𝕖 ↑tyʲ k ⇘ 𝔼 𝕖
  ↑tyʲ-𝕊 :  j ↑tyʲ k ⇘ j'
         → 𝕊₍ 𝕖 ₎ j ↑tyʲ k ⇘ 𝕊₍ 𝕖 ₎ j'
  ↑tyʲ-𝕥 : j ↑tyʲ k ⇘ j'
         → (upA : A ↑ty k ⇘ A')
         → 𝕥₍ A ₎ j ↑tyʲ k ⇘ 𝕥₍ A' ₎ j'

infix 3 ↑tyʲ0_⇘_
↑tyʲ0_⇘_ : Counter m → Counter (1 + m) → Set
↑tyʲ0_⇘_ j = _↑tyʲ_⇘_ j #0

postulate
  ↑tyʲ-unique : j ↑tyʲ k ⇘ j'
            → j ↑tyʲ k ⇘ j''
            → j' ≡ j''

  ↑tyʲ0-total : ∀ (j : Counter m)
            → ∃[ j' ](↑tyʲ0 j ⇘ j')


  ↑tyʲ-comm0' : ∀ {k : Fin (1 + m)} {j jₖ j₀ jₖ₊₁}
            → j ↑tyʲ k ⇘ jₖ
            → ↑tyʲ0 jₖ ⇘ jₖ₊₁
            → ↑tyʲ0 j ⇘ j₀
            → j₀ ↑tyʲ #S k ⇘ jₖ₊₁

  nonz-↑tyʲ' : NonZ j'
          → j ↑tyʲ k ⇘ j'
          → NonZ j

  nonz-↑tyʲ : NonZ j
          → j ↑tyʲ k ⇘ j'
          → NonZ j


{- Example
_ : find2 ((Int `→ ‶ #0) `→ ‶ #0) #0 (𝕊₍ 𝕊₍ Z ₎ Z ₎ Z)
_ = f2-arr-l (f1-arr-r-Z (f1-∞ ε-var))
-}




infix 3 _⊢rʲ_
data _⊢rʲ_ : Env n m → Counter m → Set where
  rj-𝔼 : Γ ⊢rʲ (𝔼 𝕖)
  rj-𝕊 : Γ ⊢rʲ j
       → Γ ⊢rʲ (𝕊₍ 𝕖 ₎ j)
  rj-𝕥 : Γ ⊢rʲ j
       → (regA : Γ ⊢r A)
       → Γ ⊢rʲ (𝕥₍ A ₎ j)
