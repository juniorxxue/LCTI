module Implicit.WM where

open import Implicit.Language
open import Implicit.Decl
open import Implicit.Algo

-- study 𝕎 and 𝕄 operation on decl. system
-- this is part of proof in soundness

private variable
  Ψ Ψ' : SEnv n m
  j : Counter
  A : Type m
  e : Term n m


⊢cᵉto⊢c : 𝕄 Ψ ⊢ j # e ⦂ A
        → Ψ ⊢cᵉ e
        → Ψ ⊢c A
⊢cᵉto⊢c ⊢lit clo = ⊢c-int
⊢cᵉto⊢c (⊢var x) ⊢c-var = {!!}
⊢cᵉto⊢c (⊢ann ⊢e) clo = {!!}
⊢cᵉto⊢c (⊢lam₁ ⊢e) clo = {!!}
⊢cᵉto⊢c (⊢lam₂ ⊢e) clo = {!!}
⊢cᵉto⊢c (⊢app₁ ⊢e ⊢e₁) clo = {!!}
⊢cᵉto⊢c (⊢app₂ ⊢e ⊢e₁) clo = {!!}
⊢cᵉto⊢c (⊢sub ⊢e B≤A j≢Z) clo = {!!}
⊢cᵉto⊢c (⊢tabs ⊢e) (⊢c-tlam clo) = ⊢c-∀ (⊢cᵉto⊢c ⊢e clo)

  
⊢clo-prv :
    𝕄 Ψ ⊢ j # e ⦂ A
  → Ψ ⊢cᵉ e
  → Ψ ⊆ Ψ'
  → 𝕄 Ψ' ⊢ j # e ⦂ A
⊢clo-prv ⊢lit clo ss = ⊢lit
⊢clo-prv (⊢var x) clo ss = ⊢var {!!}
⊢clo-prv (⊢ann ⊢e) (⊢c-ann x clo) ss = ⊢ann (⊢clo-prv ⊢e clo ss)
⊢clo-prv (⊢lam₁ ⊢e) (⊢c-lam clo) ss = ⊢lam₁ (⊢clo-prv ⊢e {!!} (var ss))
⊢clo-prv (⊢lam₂ ⊢e) (⊢c-lam clo) ss = ⊢lam₂ (⊢clo-prv ⊢e {!!} (var ss))
⊢clo-prv (⊢app₁ ⊢e ⊢e₁) (⊢c-app clo clo₁) ss = ⊢app₁ (⊢clo-prv ⊢e clo ss) (⊢clo-prv ⊢e₁ clo₁ ss)
⊢clo-prv (⊢app₂ ⊢e ⊢e₁) (⊢c-app clo clo₁) ss = ⊢app₂ (⊢clo-prv ⊢e clo ss) (⊢clo-prv ⊢e₁ clo₁ ss)
⊢clo-prv (⊢sub ⊢e B≤A j≢Z) clo ss = ⊢sub (⊢clo-prv ⊢e clo ss) {!!} j≢Z
⊢clo-prv (⊢tabs ⊢e) (⊢c-tlam clo) ss = ⊢tabs (⊢clo-prv ⊢e clo (uvar ss))
