module Poly.Algo.Properties where

open import Poly.Common
open import Poly.Algo

↑tm-apps : Fin (1 + n) → Apps n m → Apps (1 + n) m
↑tm-apps n nil = nil
↑tm-apps n (e ∷a as) = (↑tm n e) ∷a (↑tm-apps n as)
↑tm-apps n (A ∷t as) = A ∷t (↑tm-apps n as)

↑ty-apps : Fin (1 + m) → Apps n m → Apps n (1 + m)
↑ty-apps k nil = nil
↑ty-apps k (e ∷a as) = ↑ty-in-tm k e ∷a (↑ty-apps k as)
↑ty-apps k (A ∷t as) = ↑ty k A ∷t (↑ty-apps k as)

↑ty-appstype : Fin (1 + m) → AppsType m → AppsType (1 + m)
↑ty-appstype k nil = nil
↑ty-appstype k (A ∷a as) = ↑ty k A ∷a (↑ty-appstype k as)
↑ty-appstype k (A ∷t as) = ↑ty k A ∷a (↑ty-appstype k as)

-- subst-appstype : Fin (1 + m) → AppsType m → AppsType (1 + m)


spl-weaken-tm : ∀ {Σ Σ' : Context n m} {A es As A' n}
  → ⟦ Σ , A ⟧→⟦ es , Σ' , As , A' ⟧
  → ⟦ ↑Σ n Σ , A ⟧→⟦ ↑tm-apps n es , ↑Σ n Σ' , As , A' ⟧
spl-weaken-tm none-□ = none-□
spl-weaken-tm none-τ = none-τ
spl-weaken-tm (have-e spl) = have-e (spl-weaken-tm spl)
spl-weaken-tm (have-t spl) = have-t (spl-weaken-tm spl)

{-
spl-weaken-ty : ∀ {Σ Σ' : Context n m} {Σ' T A es As A' n B}
  → [ B ]ˢ A ⇨ A'
  → ⟦ Σ , A' ⟧→⟦ es , τ T , As , A' ⟧
  → ty-in-con Σ ↑ #0 ⇨ Σ'
  → ⟦ Σ' , A ⟧→⟦ {!!} , τ {!!} , {!!} , {!!} ⟧
spl-weaken = {!!}

spl-weaken-ty {A = ‶ X} spl = {!!}
spl-weaken-ty {A = A `→ A₁} spl = {!!}
spl-weaken-ty {A = `∀ A} spl = {!!}
-}


-- this property is not true

⊢id : ∀ {Γ : Env n m} {Σ e A A' T es As}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
  → T ≡ A'

⊢id-0 : ∀ {Γ : Env n m} {e A B}
  → Γ ⊢ τ B ⇒ e ⇒ A
  → A ≡ B
⊢id-0 ⊢e = sym (⊢id ⊢e none-τ)

⊢id (⊢app ⊢e) spl = ⊢id ⊢e (have-e spl)
⊢id (⊢lam₁ ⊢e) none-τ rewrite ⊢id-0 ⊢e = refl
⊢id (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = ⊢id ⊢e₁ (spl-weaken-tm spl)
⊢id (⊢tapp ⊢e ⊢e₁) spl = ⊢id ⊢e {!!}
⊢id (⊢sub ⊢e ¬□ gc s) spl = {!!}
