module Poly.Sound where

open import Poly.Common
open import Poly.Decl
open import Poly.Decl.Subst
open import Poly.Decl.Properties
open import Poly.Algo
open import Poly.Algo.Subsumption


postulate
  spl-weaken-0 : ∀ {Σ Σ' : Context n m} {e̅ B A'}
    → ⟦ Σ , B ⟧⇢⟦ e̅ , Σ' , A' ⟧
    → ⟦ ↑Σ0 Σ , B ⟧⇢⟦ up #0 e̅ , ↑Σ0 Σ'  , A' ⟧

  spl-weaken : ∀ {Σ Σ' : Context n m} {A e̅ A̅ A' k}
    → ⟦ Σ , A ⟧→⟦ e̅ , Σ' , A̅ , A' ⟧
    → ⟦ ↑Σ k Σ , A ⟧→⟦ up k e̅ , ↑Σ k Σ' , A̅ , A' ⟧


⊢spl-eq : ∀ {Γ : Env n m} {Σ A e es T As A'}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
  → T ≡ A'
⊢spl-eq ⊢e none-τ = ⊢context-full-type ⊢e
⊢spl-eq ⊢e (have-e spl) = ⊢spl-eq (⊢app ⊢e) spl
⊢spl-eq ⊢e (have-t st spl) = ⊢spl-eq (⊢tapp ⊢e st) spl
  
----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

infix 4 _⊩_⇐_
data _⊩_⇐_ : Env n m → Apps n m → AppsType m → Set where
  ⊩none : ∀ {Γ : Env n m}
    → Γ ⊩ nil ⇐ nil

  ⊩cons-a : ∀ {Γ : Env n m} {es As e A}
    → Γ ⊩ es ⇐ As
    → Γ ⊢ ∞ # e ⦂ A
    → Γ ⊩ (e ∷a es) ⇐ (A ∷a As)

  ⊩cons-t : ∀ {Γ : Env n m} {es A Bs Bs'}
    → Γ ⊩ es ⇐ Bs'
    → [ A ]ˢˢ Bs ⇨ Bs'
    → Γ ⊩ (A ∷t es) ⇐ `∀ Bs

⊩-elim : ∀ {Γ : Env n m} {e Σ A es T As A'}
  → Γ ⊢ Z # e ⦂ A
  → Γ ⊩ es ⇐ As
  → ⟦ Σ , A ⟧→⟦ es , T , As , A' ⟧
  → Γ ⊢ Z # e ▻ es ⦂ A'
⊩-elim ⊢e ⊩none none-□ = ⊢e
⊩-elim ⊢e ⊩none none-τ = ⊢e
⊩-elim ⊢e (⊩cons-a ⊢es x) (have-e spl) = ⊩-elim (⊢app₁ ⊢e x) ⊢es spl
⊩-elim ⊢e (⊩cons-t ⊢es x) (have-t st spl) = ⊩-elim (⊢tapp ⊢e st) ⊢es {!!}
-- ⊩-elim ⊢e (⊩cons-t ⊢es st1) (have-t st spl) rewrite substs-unique st1 ? = ⊩-elim (⊢tapp ⊢e st) ⊢es spl
    
soundd-i : ∀ {Γ : Env n m} {Σ e e̅ A A'}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧⇢⟦ e̅ , □ , A' ⟧
  → Γ ⊢ Z # e ▻ e̅ ⦂ A'

soundd-c : ∀ {Γ : Env n m} {Σ e e̅ A A' T}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧⇢⟦ e̅ , τ T , A' ⟧
  → Γ ⊢ ∞ # e ▻ e̅ ⦂ T

soundd-i-0 : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ □ ⇒ e ⇒ A
  → Γ ⊢ Z # e ⦂ A
soundd-i-0 ⊢e = soundd-i ⊢e none-□

soundd-c-0 : ∀ {Γ : Env n m} {e A B}
  → Γ ⊢ τ B ⇒ e ⇒ A
  → Γ ⊢ ∞ # e ⦂ B
soundd-c-0 ⊢e = soundd-c ⊢e none-τ

soundd-i ⊢lit none-□ = ⊢lit
soundd-i (⊢var x∈Γ) none-□ = ⊢var x∈Γ
soundd-i (⊢ann ⊢e) none-□ = ⊢ann (soundd-c-0 ⊢e)
soundd-i (⊢app ⊢e) spl = soundd-i ⊢e (have-e spl)
soundd-i {e̅ = e ∷a e̅} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = subst e̅ (soundd-i ⊢e₁ (spl-weaken-0 spl)) (soundd-i-0 ⊢e) -- weaken
soundd-i (⊢sub ⊢e ¬□ gc s) spl = {!!}
soundd-i (⊢tabs₁ ⊢e) none-□ = ⊢tabs₁ (soundd-i-0 ⊢e)
soundd-i (⊢tapp ⊢e st) spl = soundd-i ⊢e (have-t st spl)
-- soundd-i ⊢e (have-t st spl)

soundd-c (⊢app ⊢e) spl = soundd-c ⊢e (have-e spl)
soundd-c (⊢lam₁ ⊢e) none-τ = ⊢lam₁ (soundd-c-0 ⊢e)
soundd-c {e̅ = e ∷a e̅} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = subst e̅ (soundd-c ⊢e₁ (spl-weaken-0 spl )) (soundd-i-0 ⊢e) -- weaken
soundd-c (⊢sub ⊢e ¬□ gc s) spl = {!!}
soundd-c (⊢tapp ⊢e st) spl = soundd-c ⊢e (have-t st spl)

helper-lemma : ∀ {Γ : Env n m} {Σ Σ' e̅ e A A' A̅}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ e̅ , Σ' , A̅ , A' ⟧
  → ⟦ Σ , A ⟧⇒⟦ A̅ ⟧
helper-lemma = {!!}  

create-sts' : ∀ {Γ : Env n m} {Σ : Context n m} {Σ' A B B' B̅ B̅' C e̅}
  → ⟦ Σ , B' ⟧→⟦ e̅ , Σ' , B̅' , C ⟧
  → [ A ]ˢ B ⇨ B'
  → ⟦ ⟦ A ⟧↝ Σ , `∀ B ⟧⇒⟦ `∀ B̅ ⟧
  → [ A ]ˢˢ B̅ ⇨ B̅'

create-sts : ∀ {Γ : Env n m} {Σ Σ' A B B' B̅' C e̅}
  → ⟦ Σ , B' ⟧→⟦ e̅ , Σ' , B̅' , C ⟧
  → [ A ]ˢ B ⇨ B'
  → Γ ⊢ B' ≤ Σ
  → ∃[ B̅ ]([ A ]ˢˢ B̅ ⇨ B̅') -- directly compute the B̅, define a function f : Context → Type → AppsType
create-sts none-□ st s-empty = ⟨ nil , st-nil ⟩
create-sts none-τ st s-refl = ⟨ nil , st-nil ⟩
create-sts (have-e spl) st-var-eq (s-arr s ⊢e) with create-sts spl st-var-eq s
... | ⟨ Bs , sts ⟩ = ⟨ {!!} , st-cons {!!} {!!} ⟩
create-sts (have-e spl) (st-arr st st₁) (s-arr s ⊢e) = {!!}
create-sts spl st (s-∀-t st₁ s) = {!!}

sound-i : ∀ {Γ : Env n m} {Σ e e̅ A A' A̅}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ e̅ , □ , A̅ , A' ⟧
  → Γ ⊢ Z # e ▻ e̅ ⦂ A'

sound-c : ∀ {Γ : Env n m} {Σ e e̅ A A' A̅ T}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ e̅ , τ T , A̅ , A' ⟧
  → Γ ⊢ ∞ # e ▻ e̅ ⦂ T

sound-≤ : ∀ {Γ : Env n m} {Σ A es Σ' As A'}
  → Γ ⊢ A ≤ Σ
  → ⟦ Σ , A ⟧→⟦ es , Σ' , As , A' ⟧
  → Γ ⊩ es ⇐ As

sound-i-0 : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ □ ⇒ e ⇒ A
  → Γ ⊢ Z # e ⦂ A
sound-i-0 ⊢e = sound-i ⊢e none-□

sound-c-0 : ∀ {Γ : Env n m} {e A B}
  → Γ ⊢ τ B ⇒ e ⇒ A
  → Γ ⊢ ∞ # e ⦂ B
sound-c-0 ⊢e = sound-c ⊢e none-τ

sound-≤ s-empty none-□ = ⊩none
sound-≤ s-refl none-τ = ⊩none
sound-≤ (s-arr A≤Σ x) (have-e spl) = ⊩cons-a (sound-≤ A≤Σ spl) (sound-c-0 x)
sound-≤ (s-∀-t st A≤Σ) (have-t st₁ spl) rewrite subst-unique st st₁ = {!!}

sound-i ⊢lit none-□ = ⊢lit
sound-i (⊢var x∈Γ) none-□ = ⊢var x∈Γ
sound-i (⊢ann ⊢e) none-□ = ⊢ann (sound-c-0 ⊢e)
sound-i (⊢app ⊢e) spl = sound-i ⊢e (have-e spl)
sound-i {e̅ = e ∷a e̅} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = subst e̅ (sound-i ⊢e₁ (spl-weaken spl)) (sound-i-0 ⊢e) -- weaken
sound-i (⊢sub ⊢e ¬□ gc s) spl = ⊩-elim (sound-i-0 ⊢e) (sound-≤ s spl) spl
sound-i (⊢tabs₁ ⊢e) none-□ = ⊢tabs₁ (sound-i-0 ⊢e)
sound-i (⊢tapp ⊢e st) spl = sound-i ⊢e (have-t st spl)

sound-c (⊢app ⊢e) spl = sound-c ⊢e (have-e spl)
sound-c (⊢lam₁ ⊢e) none-τ = ⊢lam₁ (sound-c-0 ⊢e)
sound-c {e̅ = e ∷a e̅} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = subst e̅ (sound-c ⊢e₁ (spl-weaken spl)) (sound-i-0 ⊢e) -- weaken
sound-c ty@(⊢sub ⊢e ¬□ gc s) spl rewrite ⊢spl-eq ty spl = ⊢sub' (⊩-elim (sound-i-0 ⊢e) (sound-≤ s spl) spl)
sound-c (⊢tapp ⊢e st) spl = sound-c ⊢e (have-t st spl)
-- sound-c ⊢e (have-t st {!!} spl)
