module Poly.Sound where

open import Poly.Common
open import Poly.Decl
open import Poly.Decl.Subst
open import Poly.Decl.Properties
open import Poly.Algo
open import Poly.Algo.Subsumption


postulate
  spl-weaken : ∀ {Σ Σ' : Context n m} {A e̅ A̅ A' k}
    → ⟦ Σ , A ⟧→⟦ e̅ , Σ' , A̅ , A' ⟧
    → ⟦ ↑Σ k Σ , A ⟧→⟦ up k e̅ , ↑Σ k Σ' , A̅ , A' ⟧
  sts-unique : ∀ {Bs : AppsType (1 + m)} {B Bs₁ Bs₂}
    → [ B ]ˢˢ Bs ⇨ Bs₁
    → [ B ]ˢˢ Bs ⇨ Bs₂
    → Bs₁ ≡ Bs₂


⊢spl-eq : ∀ {Γ : Env n m} {Σ A e es T As A'}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
  → T ≡ A'
⊢spl-eq ⊢e none-τ = ⊢context-full-type ⊢e
⊢spl-eq ⊢e (have-e spl) = ⊢spl-eq (⊢app ⊢e) spl
⊢spl-eq ⊢e (have-t st sts sps spl) = ⊢spl-eq (⊢tapp ⊢e st) {!!}
  
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
⊩-elim ⊢e (⊩cons-t ⊢es st1) (have-t st sts sps spl) = ⊩-elim (⊢tapp ⊢e st) ⊢es {!!}

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
sound-≤ (s-∀-t st A≤Σ) (have-t st₁ sts sps spl) rewrite subst-unique st st₁ = ⊩cons-t (sound-≤ A≤Σ {!!}) {!!}

sound-i ⊢lit none-□ = ⊢lit
sound-i (⊢var x∈Γ) none-□ = ⊢var x∈Γ
sound-i (⊢ann ⊢e) none-□ = ⊢ann (sound-c-0 ⊢e)
sound-i (⊢app ⊢e) spl = sound-i ⊢e (have-e spl)
sound-i {e̅ = e ∷a e̅} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = subst e̅ (sound-i ⊢e₁ (spl-weaken spl)) (sound-i-0 ⊢e) -- weaken
sound-i (⊢sub ⊢e ¬□ gc s) spl = ⊩-elim (sound-i-0 ⊢e) (sound-≤ s spl) spl
sound-i (⊢tabs₁ ⊢e) none-□ = ⊢tabs₁ (sound-i-0 ⊢e)
sound-i {A̅ = A̅} (⊢tapp {A = A} {B} ⊢e st) spl = sound-i ⊢e (have-t st spl {!!} {!!})
-- 

sound-c (⊢app ⊢e) spl = sound-c ⊢e (have-e spl)
sound-c (⊢lam₁ ⊢e) none-τ = ⊢lam₁ (sound-c-0 ⊢e)
sound-c {e̅ = e ∷a e̅} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = subst e̅ (sound-c ⊢e₁ (spl-weaken spl)) (sound-i-0 ⊢e) -- weaken
sound-c ty@(⊢sub ⊢e ¬□ gc s) spl rewrite ⊢spl-eq ty spl = ⊢sub' (⊩-elim (sound-i-0 ⊢e) (sound-≤ s spl) spl)
sound-c {A̅ = A̅} (⊢tapp {A = A} {B} ⊢e st) spl = {!!}

