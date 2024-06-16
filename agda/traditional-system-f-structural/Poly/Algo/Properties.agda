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

spl-weaken-ty : ∀ {Σ Σ' : Context n m} {A es As A' n B}
  → ⟦ Σ , [ B ]ˢ A ⟧→⟦ es , Σ' , As , A' ⟧
  → ⟦ ↑tyΣ n Σ , A ⟧→⟦ ↑ty-apps n es , ↑tyΣ n Σ' , ↑ty-appstype n As , ↑ty n A' ⟧
spl-weaken-ty {A = Int} none-□ = none-□
spl-weaken-ty {A = Int} none-τ = none-τ
spl-weaken-ty {A = Int} {B = B} (have-t spl) = have-t (spl-weaken-ty {B = B} spl)

spl-weaken-ty {A = ‶ X} spl = {!!}
spl-weaken-ty {A = A `→ A₁} spl = {!!}
spl-weaken-ty {A = `∀ A} spl = {!!}

⊢id : ∀ {Γ : Env n m} {Σ e A A' T es As}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
  → T ≡ A'

≤id : ∀ {Γ Γ' : Env n m} {Σ A B Bs B' es T}
  → Γ ⊢ A ≤ Σ ⊣ Γ' ↪ B
  → ⟦ Σ , B ⟧→⟦ es , τ T , Bs , B' ⟧
  → T ≡ B'

⊢id-0 : ∀ {Γ : Env n m} {e A B}
  → Γ ⊢ τ B ⇒ e ⇒ A
  → A ≡ B
⊢id-0 ⊢e = sym (⊢id ⊢e none-τ)

≤id-0 : ∀ {Γ Γ' : Env n m} {A B C}
  → Γ ⊢ A ≤ τ B ⊣ Γ' ↪ C
  → C ≡ B
≤id-0 A≤B = sym (≤id A≤B none-τ)

⊢id (⊢app ⊢e) spl = ⊢id ⊢e (have-e spl)
⊢id (⊢lam₁ ⊢e) none-τ rewrite ⊢id-0 ⊢e = refl
⊢id (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = ⊢id ⊢e₁ (spl-weaken-tm spl)
⊢id (⊢sub ⊢e ¬□ gc s) spl = ≤id s spl
⊢id (⊢tapp ⊢e) spl = ⊢id ⊢e (have-t spl)

postulate
  ↑ty-eq : ∀ {A : Type m} {B k}
    → ↑ty k A ≡ ↑ty k B
    → A ≡ B

≤id s-int none-τ = refl
≤id s-var none-τ = refl
≤id (s-ex-l= x s) none-τ = sym (≤id-0 s)
≤id (s-ex-r= x s) none-τ = refl
≤id (s-arr s s₁) none-τ = refl
≤id (s-term-c x s) (have-e spl) = ≤id s spl
≤id (s-∀ s) none-τ rewrite ≤id-0 s = refl
≤id (s-∀-t s) (have-t spl) with ≤id s (spl-weaken-ty spl)
... | eq = ↑ty-eq eq


{-
↑ty-eq {A = Int} {B = Int} refl = refl
↑ty-eq {A = ‶ X} {B = ‶ X₁} eq = {!!}
↑ty-eq {A = A `→ A₁} {B = B `→ B₁} eq = {!!}
↑ty-eq {A = `∀ A} {B = `∀ B} eq = {!!}
-}
  
s-closed : ∀ {Γ Γ' : Env n m} {A B Σ}
  → Γ ⊢ A ≤ Σ ⊣ Γ' ↪ B
  → Γ ≡ Γ'
s-closed s-int = refl
s-closed s-empty = refl
s-closed s-var = refl
s-closed (s-ex-l= x s) = s-closed s
s-closed (s-ex-r= x s) = s-closed s
s-closed (s-arr s s₁) rewrite s-closed s | s-closed s₁ = refl
s-closed (s-term-c x s) = s-closed s
s-closed (s-∀ s) with s-closed s
... | refl = refl
s-closed (s-∀-t s) with s-closed s
... | refl = refl
