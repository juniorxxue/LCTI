{-# OPTIONS --allow-unsolved-metas #-}

module Poly.Basic where

-- open import Data.Fin using (_≤_; inject₁)

open import Poly.Common

_/ˣ_ : Env (1 + n) m → Fin (1 + n) → Env n m
(Γ , A) /ˣ #0 = Γ
_/ˣ_ {suc n} (Γ , A) (#S k) = (Γ /ˣ k) , A
(Γ ,∙) /ˣ k = (Γ /ˣ k) ,∙

∈-weaken : ∀ {Γ : Env (1 + n) m} {k x A}
  → (Γ /ˣ k) ∋ x ⦂ A
  → Γ ∋ (punchIn k x) ⦂ A
∈-weaken {Γ = Γ , A} {#0} ∈Γ = S, ∈Γ
∈-weaken {m = zero} {Γ = Γ , A} {#S k} Z = Z
∈-weaken {m = zero} {Γ = Γ , A} {#S k} (S, ∈Γ) = S, (∈-weaken ∈Γ)
∈-weaken {suc n} {m = suc m} {Γ = Γ , A} {#S k} Z = Z
∈-weaken {suc n} {m = suc m} {Γ = Γ , A} {#S k} (S, ∈Γ) = S, (∈-weaken ∈Γ)
∈-weaken {Γ = Γ ,∙} (S∙ ∈Γ x) = S∙ (∈-weaken ∈Γ) x 

↑tm-comm : ∀ {e : Term n m} {j k}
  → j F≤ k
  → ↑tm (inject₁ j) (↑tm k e) ≡ ↑tm (#S k) (↑tm j e)
↑tm-comm = {!   !}

