module Poly.Sound where

open import Poly.Common
open import Poly.Decl
open import Poly.Decl.Subst
open import Poly.Decl.Properties
open import Poly.Algo


{-
spl-weaken : ∀ {Σ Σ' : Context n m} {A e̅ A̅ A' k}
  → ⟦ Σ , A ⟧→⟦ e̅ , Σ' , A̅ , A' ⟧
  → ⟦ ↑Σ k Σ , A ⟧→⟦ up k e̅ , ↑Σ k Σ' , A̅ , A' ⟧
spl-weaken = {!!}
-}

postulate
  spl-weaken-0 : ∀ {Σ Σ' : Context n m} {e̅ B A'}
    → ⟦ Σ , B ⟧⇢⟦ e̅ , Σ' , A' ⟧
    → ⟦ ↑Σ0 Σ , B ⟧⇢⟦ up #0 e̅ , ↑Σ0 Σ'  , A' ⟧
  
----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

sound-i : ∀ {Γ : Env n m} {Σ e e̅ A A'}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧⇢⟦ e̅ , □ , A' ⟧
  → Γ ⊢ Z # e ▻ e̅ ⦂ A'

sound-c : ∀ {Γ : Env n m} {Σ e e̅ A A' T}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧⇢⟦ e̅ , τ T , A' ⟧
  → Γ ⊢ ∞ # e ▻ e̅ ⦂ T

sound-i-0 : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ □ ⇒ e ⇒ A
  → Γ ⊢ Z # e ⦂ A
sound-i-0 ⊢e = sound-i ⊢e none-□

sound-c-0 : ∀ {Γ : Env n m} {e A B}
  → Γ ⊢ τ B ⇒ e ⇒ A
  → Γ ⊢ ∞ # e ⦂ B
sound-c-0 ⊢e = sound-c ⊢e none-τ

sound-i ⊢lit none-□ = ⊢lit
sound-i (⊢var x∈Γ) none-□ = ⊢var x∈Γ
sound-i (⊢ann ⊢e) none-□ = ⊢ann (sound-c-0 ⊢e)
sound-i (⊢app ⊢e) spl = sound-i ⊢e (have-e spl)
sound-i {e̅ = e ∷a e̅} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = subst e̅ (sound-i ⊢e₁ (spl-weaken-0 spl)) (sound-i-0 ⊢e) -- weaken
sound-i (⊢sub ⊢e ¬□ gc s) spl = {!!}
sound-i (⊢tabs₁ ⊢e) none-□ = ⊢tabs₁ (sound-i-0 ⊢e)
sound-i (⊢tapp ⊢e st) spl = sound-i ⊢e (have-t st spl)

sound-c (⊢app ⊢e) spl = sound-c ⊢e (have-e spl)
sound-c (⊢lam₁ ⊢e) none-τ = ⊢lam₁ (sound-c-0 ⊢e)
sound-c {e̅ = e ∷a e̅} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = subst e̅ (sound-c ⊢e₁ (spl-weaken-0 spl )) (sound-i-0 ⊢e) -- weaken
sound-c (⊢sub ⊢e ¬□ gc s) spl = {!!}
sound-c (⊢tapp ⊢e st) spl = sound-c ⊢e (have-t st spl)
