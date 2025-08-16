module Implicit.Language.Find.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.Base
open import Implicit.Language.Occur.Base
open import Implicit.Language.Regular.Base

infix 3 _↑tyʲ_⇘_
data _↑tyʲ_⇘_ : Counter m → Fin (1 + m) → Counter (1 + m) → Set where
  ↑tyʲ-Z : Z ↑tyʲ k ⇘ Z
  ↑tyʲ-∞ : ∞ ↑tyʲ k ⇘ ∞
  ↑tyʲ-𝕚 : j ↑tyʲ k ⇘ j'
         → (𝕚 j) ↑tyʲ k ⇘ (𝕚 j')
  ↑tyʲ-𝕔 : j ↑tyʲ k ⇘ j'
         → (𝕔 j) ↑tyʲ k ⇘ (𝕔 j')
  ↑tyʲ-𝕥 : j ↑tyʲ k ⇘ j'
         → (upA : A ↑ty k ⇘ A')
         → 𝕥₍ A ₎ j ↑tyʲ k ⇘ 𝕥₍ A' ₎ j'

infix 3 ↑tyʲ0_⇘_
↑tyʲ0_⇘_ : Counter m → Counter (1 + m) → Set
↑tyʲ0_⇘_ j = _↑tyʲ_⇘_ j #0


↑tyʲ-unique : j ↑tyʲ k ⇘ j'
            → j ↑tyʲ k ⇘ j''
            → j' ≡ j''
↑tyʲ-unique ↑tyʲ-Z ↑tyʲ-Z = refl
↑tyʲ-unique ↑tyʲ-∞ ↑tyʲ-∞ = refl
↑tyʲ-unique (↑tyʲ-𝕚 up1) (↑tyʲ-𝕚 up2) = cong 𝕚 (↑tyʲ-unique up1 up2)
↑tyʲ-unique (↑tyʲ-𝕔 up1) (↑tyʲ-𝕔 up2) = cong 𝕔 (↑tyʲ-unique up1 up2)
↑tyʲ-unique (↑tyʲ-𝕥 up1 upA) (↑tyʲ-𝕥 up2 upA₁)
  with refl ← ↑ty-unique upA upA₁
  with refl ← ↑tyʲ-unique up1 up2 = refl

↑tyʲ0-total : ∀ (j : Counter m)
            → ∃[ j' ](↑tyʲ0 j ⇘ j')
↑tyʲ0-total Z = ⟨ Z , ↑tyʲ-Z ⟩
↑tyʲ0-total ∞ = ⟨ ∞ , ↑tyʲ-∞ ⟩
↑tyʲ0-total (𝕚 j) = ⟨ 𝕚 (↑tyʲ0-total j .proj₁) , ↑tyʲ-𝕚 (↑tyʲ0-total j .proj₂) ⟩
↑tyʲ0-total (𝕔 j) = ⟨ 𝕔 (↑tyʲ0-total j .proj₁) , ↑tyʲ-𝕔 (↑tyʲ0-total j .proj₂) ⟩
↑tyʲ0-total (𝕥₍ A ₎ j) with ↑ty0-total A | ↑tyʲ0-total j
... | ⟨ A' , upA ⟩ | ⟨ j' , upj ⟩ = ⟨ 𝕥₍ A' ₎ j' , ↑tyʲ-𝕥 upj upA ⟩


↑tyʲ-comm0' : ∀ {k : Fin (1 + m)} {j jₖ j₀ jₖ₊₁}
            → j ↑tyʲ k ⇘ jₖ
            → ↑tyʲ0 jₖ ⇘ jₖ₊₁
            → ↑tyʲ0 j ⇘ j₀
            → j₀ ↑tyʲ #S k ⇘ jₖ₊₁
↑tyʲ-comm0' ↑tyʲ-Z ↑tyʲ-Z ↑tyʲ-Z = ↑tyʲ-Z
↑tyʲ-comm0' ↑tyʲ-∞ ↑tyʲ-∞ ↑tyʲ-∞ = ↑tyʲ-∞
↑tyʲ-comm0' (↑tyʲ-𝕚 up1) (↑tyʲ-𝕚 up2) (↑tyʲ-𝕚 up3) = ↑tyʲ-𝕚 (↑tyʲ-comm0' up1 up2 up3)
↑tyʲ-comm0' (↑tyʲ-𝕔 up1) (↑tyʲ-𝕔 up2) (↑tyʲ-𝕔 up3) = ↑tyʲ-𝕔 (↑tyʲ-comm0' up1 up2 up3)
↑tyʲ-comm0' (↑tyʲ-𝕥 up1 upA) (↑tyʲ-𝕥 up2 upA₁) (↑tyʲ-𝕥 up3 upA₂)
  = ↑tyʲ-𝕥 (↑tyʲ-comm0' up1 up2 up3) (↑ty-comm0' upA upA₁ upA₂)

𝕚𝕔-↑tyʲ' : 𝕚𝕔 j'
         → j ↑tyʲ k ⇘ j'
         → 𝕚𝕔 j
𝕚𝕔-↑tyʲ' case-𝕚 (↑tyʲ-𝕚 upj) = case-𝕚
𝕚𝕔-↑tyʲ' case-𝕔 (↑tyʲ-𝕔 upj) = case-𝕔

𝕚𝕔-↑tyʲ : 𝕚𝕔 j
         → j ↑tyʲ k ⇘ j'
         → 𝕚𝕔 j'
𝕚𝕔-↑tyʲ case-𝕚 (↑tyʲ-𝕚 upj) = case-𝕚
𝕚𝕔-↑tyʲ case-𝕔 (↑tyʲ-𝕔 upj) = case-𝕔

nonz-↑tyʲ' : NonZ j'
          → j ↑tyʲ k ⇘ j'
          → NonZ j
nonz-↑tyʲ' nz-∞ ↑tyʲ-∞ = nz-∞
nonz-↑tyʲ' nz-I (↑tyʲ-𝕚 upj) = nz-I
nonz-↑tyʲ' nz-C (↑tyʲ-𝕔 upj) = nz-C
nonz-↑tyʲ' nz-T (↑tyʲ-𝕥 upj upA) = nz-T

nonz-↑tyʲ : NonZ j
          → j ↑tyʲ k ⇘ j'
          → NonZ j
nonz-↑tyʲ nz-∞ ↑tyʲ-∞ = nz-∞
nonz-↑tyʲ nz-I (↑tyʲ-𝕚 upj) = nz-I
nonz-↑tyʲ nz-C (↑tyʲ-𝕔 upj) = nz-C
nonz-↑tyʲ nz-T (↑tyʲ-𝕥 upj upA) = nz-T

data IsoInf : Counter m → Set where
  i∞-z : IsoInf (Counter m ∋⦂ 𝕚 ∞)
  i∞-i : IsoInf j
       → IsoInf (𝕚 j)

-- find A k j
-- at j-th position of A type, should have a bound variable, example: |-1 forall a. a -> a <: Int
data find : Type m → Fin m → Counter m → Set where
{-
  f-∞       : (inA : k ε A)
            → find A k ∞
-}
  f-iso     : (iso : IsoInf j)
            → find (‶ k) k j
  f-arr-𝕚-l : (inA : k ε A)
            → find (A `→ B) k (𝕚 j)
  f-arr-𝕚-r : (¬inA : k ¬ε A)
            → find B k j
            → find (A `→ B) k (𝕚 j)
  f-arr-𝕔   : (¬inA : k ¬ε A)
            → find B k j
            → find (A `→ B) k (𝕔 j)
  f-∀-𝕚     : find A (#S k) (𝕚 j')
            → (upj : ↑tyʲ0 j ⇘ j')
            → find (`∀ A) k (𝕚 j)
  f-∀-𝕔     : find A (#S k) (𝕔 j')
            → (upj : ↑tyʲ0 j ⇘ j')
            → find (`∀ A) k (𝕔 j)
  f-𝕥       : find A (#S k) j'
            → (upj : ↑tyʲ0 j ⇘ j')
            → find (`∀ A) k (𝕥₍ B ₎ j)

data peek : Type m → Fin m → Counter m → Set where
  peek-base : (inA : k ε A)
            → peek A k ∞
  peek-arr-i : peek B k j
             → peek (A `→ B) k (𝕚 j)
  peek-arr-c : peek B k j
             → peek (A `→ B) k (𝕔 j)
  peek-∀-i : peek A (#S k) (𝕚 j')
             → (upj : ↑tyʲ0 j ⇘ j')
             → peek (`∀ A) k (𝕚 j)
  peek-∀-c : peek A (#S k) (𝕔 j')
             → (upj : ↑tyʲ0 j ⇘ j')
             → peek (`∀ A) k (𝕔 j)
  peek-∀-t : peek A (#S k) j'
            → (upj : ↑tyʲ0 j ⇘ j')
            → peek (`∀ A) k (𝕥₍ B ₎ j)

data ¬peek : Type m → Fin m → Counter m → Set where
  ¬peek-base1 : ¬peek A k Z
  ¬peek-base2 : (¬inA : k ¬ε A)
             → ¬peek A k ∞
  ¬peek-arr-i : ¬peek B k j
              → ¬peek (A `→ B) k (𝕚 j)
  ¬peek-arr-c : ¬peek B k j
              → ¬peek (A `→ B) k (𝕔 j)
  ¬peek-∀-i : ¬peek A (#S k) (𝕚 j')
              → (upj : ↑tyʲ0 j ⇘ j')
            → ¬peek (`∀ A) k (𝕚 j)
  ¬peek-∀-c : ¬peek A (#S k) (𝕔 j')
            → (upj : ↑tyʲ0 j ⇘ j')
            → ¬peek (`∀ A) k (𝕔 j)
  ¬peek-∀-t : ¬peek A (#S k) j'
            → (upj : ↑tyʲ0 j ⇘ j')
            → ¬peek (`∀ A) k (𝕥₍ B ₎ j)

find-Z-false : find A k Z
             → ⊥
find-Z-false (f-iso ())

infix 3 _⊢rʲ_
data _⊢rʲ_ : Env n m → Counter m → Set where
  rj-Z : Γ ⊢rʲ Z
  rj-∞ : Γ ⊢rʲ ∞
  rj-𝕚 : Γ ⊢rʲ j
       → Γ ⊢rʲ (𝕚 j)
  rj-𝕔 : Γ ⊢rʲ j
       → Γ ⊢rʲ (𝕔 j)
  rj-𝕥 : Γ ⊢rʲ j
       → (regA : Γ ⊢r A)
       → Γ ⊢rʲ (𝕥₍ A ₎ j)
