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
↑ty-appstype k (`∀ as) = `∀ (↑ty-appstype (#S k) as)

-- subst-appstype : Fin (1 + m) → AppsType m → AppsType (1 + m)

{-
spl-weaken-tm : ∀ {Σ Σ' : Context n m} {A es As A' n}
  → ⟦ Σ , A ⟧→⟦ es , Σ' , As , A' ⟧
  → ⟦ ↑Σ n Σ , A ⟧→⟦ ↑tm-apps n es , ↑Σ n Σ' , As , A' ⟧
spl-weaken-tm none-□ = none-□
spl-weaken-tm none-τ = none-τ
spl-weaken-tm (have-e spl) = have-e (spl-weaken-tm spl)
spl-weaken-tm (have-t st1 st2 sts spl) = have-t st1 st2 sts (spl-weaken-tm spl)
-}

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

↑tmGenCon : ∀ {e : Term n m} {k }
  → GenericConsumer e 
  → GenericConsumer (↑tm k e)
↑tmGenCon {e = .(Term _ _ ∋⦂ lit _)} gc-i = gc-i
↑tmGenCon {e = .(Term _ _ ∋⦂ ` _)} gc-var = gc-var
↑tmGenCon {e = .(_ ⦂ _)} gc-ann = gc-ann
↑tmGenCon {e = .(Λ _)} gc-tlam = gc-tlam 

↑ΣnonEmpty : ∀ {Σ : Context n m} {k}
  → NonEmpty Σ
  → NonEmpty (↑Σ k Σ)
↑ΣnonEmpty ne-τ = ne-τ
↑ΣnonEmpty ne-app = ne-app
↑ΣnonEmpty ne-tapp = ne-tapp

↑Σ-comm : ∀ {Σ : Context n m} {j : Fin (1 + n)} {k : Fin (1 + n)}
  → j F≤ k
  → ↑Σ (inject₁ j) (↑Σ k Σ) ≡ ↑Σ (#S k) (↑Σ j Σ)
↑Σ-comm {Σ = □} j≤k = refl
↑Σ-comm {Σ = τ A} j≤k = refl
↑Σ-comm {Σ = [ e ]↝ Σ} j≤k = cong₂ [_]↝_ (↑tm-comm j≤k) (↑Σ-comm j≤k)
↑Σ-comm {Σ = ⟦ A ⟧↝ Σ} j≤k = cong (⟦_⟧↝_ A) (↑Σ-comm j≤k)

↑Σ-comm0 : ∀ {Σ : Context n m} {k}
  → ↑Σ0 (↑Σ k Σ) ≡ ↑Σ (#S k) (↑Σ0 Σ)
↑Σ-comm0 = ↑Σ-comm _≤_.z≤n

≤weaken : ∀ {Γ : Env (1 + n) m} {Σ k A}
  → (Γ /ˣ k) ⊢ A ≤ Σ
  → Γ ⊢ A ≤ ↑Σ k Σ

⊢weaken : ∀ {Γ : Env (1 + n) m} { Σ k e A }
  → (Γ /ˣ k) ⊢ Σ ⇒ e ⇒ A
  → Γ ⊢ ↑Σ k Σ ⇒ ↑tm k e ⇒ A
    
≤weaken s-empty = s-empty
≤weaken s-refl = s-refl
≤weaken (s-arr ≤A ⊢e) = s-arr (≤weaken ≤A) (⊢weaken ⊢e)
≤weaken (s-∀-t st ≤A) = s-∀-t st (≤weaken ≤A)

⊢weaken ⊢lit = ⊢lit
⊢weaken (⊢var x∈Γ) = ⊢var (∈-weaken x∈Γ)
⊢weaken (⊢ann ⊢e) = ⊢ann (⊢weaken ⊢e)
⊢weaken (⊢app ⊢e) = ⊢app (⊢weaken ⊢e)
⊢weaken (⊢lam₁ ⊢e) = ⊢lam₁ (⊢weaken ⊢e)
⊢weaken {Γ = Γ} {k = k} (⊢lam₂ {Σ = Σ} {A} ⊢e ⊢e₁) with ⊢weaken {Γ = Γ , A} { k = #S k} ⊢e₁ 
... | p rewrite (sym (↑Σ-comm0 {Σ = Σ} {k = k})) = ⊢lam₂ (⊢weaken ⊢e) p
⊢weaken (⊢sub ⊢e ¬□ gc s) = ⊢sub (⊢weaken ⊢e) (↑ΣnonEmpty ¬□) (↑tmGenCon gc) (≤weaken s)
⊢weaken (⊢tabs₁ ⊢e) = ⊢tabs₁ (⊢weaken ⊢e)
⊢weaken (⊢tapp ⊢e st) = ⊢tapp (⊢weaken ⊢e) st


postulate
  ≤strengthen0 : ∀ {Γ : Env n m} {Σ A B}
    → Γ , A ⊢ B ≤ ↑Σ #0 Σ
    → Γ ⊢ B ≤ Σ

infix 4 _~↑Σ~_
data _~↑Σ~_ : Context (1 + n) m → Fin (1 + n) → Set where
  ↑Σ-□ : ∀ {k}
    → (Context (1 + n) m ∋⦂ □) ~↑Σ~ k
  ↑Σ-τ : ∀ {k A}
    → (Context (1 + n) m ∋⦂ τ A) ~↑Σ~ k
  ↑Σ-e : ∀ {Σ : Context (1 + n) m} {e k}
    → (sd-e : e ~↑tm~ k)
    → Σ ~↑Σ~ k
    → ([ e ]↝ Σ) ~↑Σ~ k
  ↑Σ-t : ∀ {Σ : Context (1 + n) m} {A k}
    → Σ ~↑Σ~ k
    → (⟦ A ⟧↝ Σ) ~↑Σ~ k

↓Σ : (k : Fin (1 + n)) → (Σ : Context (1 + n) m) → (sd : Σ ~↑Σ~ k) → Context n m
↓Σ k □ sd = □
↓Σ k (τ A) sd = τ A
↓Σ k ([ e ]↝ Σ) (↑Σ-e sde sd) = [ ↓tm k e sde ]↝ ↓Σ k Σ sd
↓Σ k (⟦ A ⟧↝ Σ) (↑Σ-t sd) = ⟦ A ⟧↝ ↓Σ k Σ sd

↓Σ-NonEmpty : ∀ {Σ : Context (1 + n) m} {k}
  → NonEmpty Σ
  → (sdΣ : Σ ~↑Σ~ k)
  → NonEmpty (↓Σ k Σ sdΣ)
↓Σ-NonEmpty ne-τ sdΣ = ne-τ
↓Σ-NonEmpty ne-app (↑Σ-e sd-e sdΣ) = ne-app
↓Σ-NonEmpty ne-tapp (↑Σ-t sdΣ) = ne-tapp

↓tm-GenericConsumer : ∀ {e : Term (1 + n) m} {k}
  → GenericConsumer e
  → (sde : e ~↑tm~ k)
  → GenericConsumer (↓tm k e sde)
↓tm-GenericConsumer gc-i sde = gc-i
↓tm-GenericConsumer {k = k} gc-var (sd-var {x = x} k≢x) with k #≟ x
... | yes p = ⊥-elim (k≢x p)
... | no ¬p = gc-var
↓tm-GenericConsumer gc-ann (sd-ann sde) = gc-ann
↓tm-GenericConsumer gc-tlam (sd-Λ sde) = gc-tlam

↓tm-↑tm-comm-var : ∀ x (k₁ : Fin (1 + n)) k₂
  → k₂ F≤ k₁
  → (p1 : k₁ ≢ x)
  → (p2 : #S k₁ ≢ punchIn (inject₁ k₂) x)
  → punchIn k₂ (punchOut p1) ≡ punchOut p2
↓tm-↑tm-comm-var #0 #0 k₂ sm p1 p2 = ⊥-elim (p1 refl)
↓tm-↑tm-comm-var #0 (#S k₁) k₂ sm p1 p2 = {!!}
↓tm-↑tm-comm-var (#S x) k₁ k₂ sm p1 p2 = {!!}

↓tm-↑tm-comm : ∀ {e : Term (1 + n) m} {k₁ k₂}
  → k₂ F≤ k₁
  → (sd1 : e ~↑tm~ k₁)
  → (sd2 : (↑tm (inject₁ k₂) e) ~↑tm~ #S k₁)
  → ↑tm k₂ (↓tm k₁ e sd1) ≡ ↓tm (#S k₁) (↑tm (inject₁ k₂) e) sd2
↓tm-↑tm-comm {e = lit i} sm sd1 sd2 = refl
↓tm-↑tm-comm {e = ` x} {k₁} {k₂} sm (sd-var k≢x) (sd-var k≢x₁) with k₁ #≟ x | #S k₁ #≟ punchIn (inject₁ k₂) x
... | yes p1 | yes p2 = ⊥-elim (k≢x p1)
... | yes p1 | no ¬p2 = ⊥-elim (k≢x p1)
... | no ¬p1 | yes p2 = ⊥-elim (k≢x₁ p2)
... | no ¬p1 | no ¬p2 = {!!}
↓tm-↑tm-comm {e = ƛ e} sm (sd-lam sd1) (sd-lam sd2) rewrite ↓tm-↑tm-comm {e = e} (s≤s sm) sd1 sd2 = refl
↓tm-↑tm-comm {e = e · e₁} sm (sd-app sd1 sd3) (sd-app sd2 sd4) rewrite ↓tm-↑tm-comm {e = e} sm sd1 sd2 | ↓tm-↑tm-comm {e = e₁} sm sd3 sd4 = refl
↓tm-↑tm-comm {e = e ⦂ A} sm (sd-ann sd1) (sd-ann sd2) rewrite ↓tm-↑tm-comm {e = e} sm sd1 sd2 = refl
↓tm-↑tm-comm {e = Λ e} sm (sd-Λ sd1) (sd-Λ sd2) rewrite ↓tm-↑tm-comm {e = e} sm sd1 sd2 = refl
↓tm-↑tm-comm {e = e [ A ]} sm (sd-tapp sd1) (sd-tapp sd2)  rewrite ↓tm-↑tm-comm {e = e} sm sd1 sd2 = refl


↓Σ-↑Σ-comm : ∀ {Σ : Context (1 + n) m} {k₁ k₂}
  → k₂ F≤ k₁
  → (sd1 : Σ ~↑Σ~ k₁)
  → (sd2 : ↑Σ (inject₁ k₂) Σ ~↑Σ~ #S k₁)
  → ↑Σ k₂ (↓Σ k₁ Σ sd1) ≡ ↓Σ (#S k₁) (↑Σ (inject₁ k₂) Σ) sd2
↓Σ-↑Σ-comm {Σ = □} sm sd1 sd2 = refl
↓Σ-↑Σ-comm {Σ = τ A} sm sd1 sd2 = refl
↓Σ-↑Σ-comm {Σ = [ e ]↝ Σ} sm (↑Σ-e sd-e sd1) (↑Σ-e sd-e₁ sd2) rewrite ↓Σ-↑Σ-comm {Σ = Σ} sm sd1 sd2 | ↓tm-↑tm-comm sm sd-e sd-e₁ = refl
↓Σ-↑Σ-comm {Σ = ⟦ A ⟧↝ Σ} sm (↑Σ-t sd1) (↑Σ-t sd2) rewrite ↓Σ-↑Σ-comm {Σ = Σ} sm sd1 sd2 = refl

helper : ∀ {Σ : Context (1 + n) m} {k}
  → Σ ~↑Σ~ k
  → ↑Σ #0 Σ ~↑Σ~ #S k

⊢strengthen : ∀ {Γ : Env (1 + n) m} {Σ k e A}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → (sdΣ : Σ ~↑Σ~ k)
  → (sde : e ~↑tm~ k)
  → (Γ /ˣ k) ⊢ ↓Σ k Σ sdΣ ⇒ ↓tm k e sde ⇒ A

≤strengthen : ∀ {Γ : Env (1 + n) m} {Σ B k}
  → Γ ⊢ B ≤ Σ
  → (sdΣ : Σ ~↑Σ~ k)  
  → Γ /ˣ k ⊢ B ≤ ↓Σ k Σ sdΣ

⊢strengthen ⊢lit sdΣ sde = ⊢lit
⊢strengthen {k = k} (⊢var x∈Γ) sdΣ (sd-var {x = x} k≢x) with k #≟ x
... | yes p = ⊥-elim (k≢x p)
... | no ¬p = ⊢var (∈-strengthen x∈Γ k≢x)
⊢strengthen (⊢ann ⊢e) sdΣ (sd-ann sde) = ⊢ann (⊢strengthen ⊢e ↑Σ-τ sde)
⊢strengthen (⊢app ⊢e) sdΣ (sd-app sde sde₁) = ⊢app (⊢strengthen ⊢e (↑Σ-e sde₁ sdΣ) sde)
⊢strengthen (⊢lam₁ ⊢e) ↑Σ-τ (sd-lam sde) = ⊢lam₁ (⊢strengthen ⊢e ↑Σ-τ sde)
⊢strengthen {k = k} (⊢lam₂ {Σ = Σ} ⊢e ⊢e₁) (↑Σ-e sd-e sdΣ) (sd-lam sde) with ↓Σ-↑Σ-comm {Σ = Σ} {k₁ = k} {k₂ = #0} z≤n sdΣ (helper sdΣ)
... | r = ⊢lam₂ (⊢strengthen ⊢e ↑Σ-□ sd-e) {!!}
⊢strengthen (⊢sub ⊢e ¬□ gc s) sdΣ sde = ⊢sub (⊢strengthen ⊢e ↑Σ-□ sde) (↓Σ-NonEmpty ¬□ sdΣ) (↓tm-GenericConsumer gc sde) (≤strengthen s sdΣ)
⊢strengthen (⊢tabs₁ ⊢e) ↑Σ-□ (sd-Λ sde) = ⊢tabs₁ (⊢strengthen ⊢e ↑Σ-□ sde)
⊢strengthen (⊢tapp ⊢e st) sdΣ (sd-tapp sde) = ⊢tapp (⊢strengthen ⊢e (↑Σ-t sdΣ) sde) st

≤strengthen s-empty sdΣ = s-empty
≤strengthen s-refl sdΣ = s-refl
≤strengthen (s-arr s ⊢e) (↑Σ-e sd-e sdΣ) = s-arr (≤strengthen s sdΣ) (⊢strengthen ⊢e ↑Σ-τ sd-e)
≤strengthen (s-∀-t st s) (↑Σ-t sdΣ) = s-∀-t st (≤strengthen s sdΣ)


≤weaken0 : ∀ {Γ : Env n m} {Σ A B}
  → Γ ⊢ B ≤ Σ
  → Γ , A ⊢ B ≤ ↑Σ #0 Σ
≤weaken0 s = ≤weaken s  
    
Σspl-weaken0 : ∀ {Σ : Context n m} {a̅}
  → ⟦ Σ ⟧⇒⟦ a̅ , □ ⟧
  → ⟦ ↑Σ0 Σ ⟧⇒⟦ up0 a̅ , □ ⟧
Σspl-weaken0 none-□ = none-□
Σspl-weaken0 (have-e s) = have-e (Σspl-weaken0 s)
Σspl-weaken0 (have-t s) = have-t (Σspl-weaken0 s)
