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
  
⊢clo-prv :
    𝕄 Ψ ⊢ j # e ⦂ A
  → Ψ ⊢c e
  → Ψ ⊆ Ψ'
  → 𝕄 Ψ' ⊢ j # e ⦂ A
⊢clo-prv ⊢lit clo ss = ⊢lit
⊢clo-prv (⊢var x) clo ss = ⊢var {!!}
⊢clo-prv (⊢ann ⊢e) clo ss = ⊢ann (⊢clo-prv ⊢e clo ss) 
⊢clo-prv (⊢lam₁ ⊢e) (⊢c-arr clo clo₁) ss = ⊢lam₁ (⊢clo-prv ⊢e (⊢c-, clo₁) (var ss))
⊢clo-prv (⊢lam₂ ⊢e) (⊢c-arr clo clo₁) ss = ⊢lam₂ (⊢clo-prv ⊢e (⊢c-, clo₁) (var ss))
⊢clo-prv (⊢app₁ ⊢e ⊢e₁) clo ss = ⊢app₁ {!!} {!!}
⊢clo-prv (⊢app₂ ⊢e ⊢e₁) clo ss = {!!}
⊢clo-prv (⊢sub ⊢e B≤A j≢Z) clo ss = {!!}
⊢clo-prv (⊢tabs ⊢e) clo ss = {!!}
