module Implicit.Algo.Subst.Definitions where

open import Implicit.Common
open import Implicit.Algo

variable

  Ψ Ψ' : SEnv n m
  Σ : Context n m

postulate

  substituition-case2 : ∀ {A B C A' B'}
    → Ψ ,= C ⊢ A ≤ ↑tyΣ0 Σ ⊣ Ψ' ,= C ↪ B
    → [ C ]ˢ A ⇨ A'
    → [ C ]ˢ B ⇨ B'
    → Ψ ⊢ A' ≤ Σ ⊣ Ψ' ↪ B'

-- remove (^a = A) from subtyping environment
infix 4 _/_⦂_⇨_
data _/_⦂_⇨_ : SEnv n (1 + m) → Fin (1 + m) → Type m → SEnv n m → Set where
  Z : ∀ {A}
    → (Ψ ,= A) / #0 ⦂ A ⇨ Ψ
  S, : ∀ {A : Type (1 + m)} {k B A'}
    → Ψ / k ⦂ B ⇨ Ψ'
    → [ k / B ]ˢ A ⇨ A' -- substituition is required, not sure if it's k-th position
    → (Ψ , A) / k ⦂ B ⇨ (Ψ' , A')
  S,∙ : ∀ {A : Type (1 + m)} {k A'}
    → Ψ / k ⦂ A' ⇨ Ψ'
    → [ Int ]ˢ A ⇨ A' -- the given A doesn't contain such universal variables
    → (Ψ ,∙) / #S k ⦂ A ⇨ (Ψ' ,∙)
  S,^ : ∀ {A : Type (1 + m)} {k A'}
    → Ψ / k ⦂ A' ⇨ Ψ'
    → [ Int ]ˢ A ⇨ A' -- the given A doesn't contain such universal variables
    → (Ψ ,^) / #S k ⦂ A ⇨ (Ψ' ,^)
  S,= : ∀ {A : Type (1 + m)} {B : Type (1 + m)} {k A' B'}
    → Ψ / k ⦂ A' ⇨ Ψ'
    → [ Int ]ˢ A ⇨ A' -- the given A doesn't contain such universal variables, thus a safe unshift
    → [ k / A' ]ˢ B ⇨ B'
    → (Ψ ,= B) / #S k ⦂ A ⇨ (Ψ' ,= B')

