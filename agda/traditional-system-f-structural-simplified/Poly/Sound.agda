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
  
----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

sound-i : ∀ {Γ : Env n m} {Σ e e̅ A A' A̅}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ e̅ , □ , A̅ , A' ⟧
  → Γ ⊢ Z # e ▻ e̅ ⦂ A'

sound-c : ∀ {Γ : Env n m} {Σ e e̅ A A' A̅ T}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ e̅ , τ T , A̅ , A' ⟧
  → Γ ⊢ ∞ # e ▻ e̅ ⦂ T

sound-i-0 : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ □ ⇒ e ⇒ A
  → Γ ⊢ Z # e ⦂ A
sound-i-0 ⊢e = sound-i ⊢e none-□

sound-c-0 : ∀ {Γ : Env n m} {e A B}
  → Γ ⊢ τ B ⇒ e ⇒ A
  → Γ ⊢ ∞ # e ⦂ B
sound-c-0 ⊢e = sound-c ⊢e none-τ

sound-i ⊢lit spl = {!!}
sound-i (⊢var x∈Γ) spl = {!!}
sound-i (⊢ann ⊢e) spl = {!!}
sound-i (⊢app ⊢e) spl = {!!}
sound-i (⊢lam₂ ⊢e ⊢e₁) spl = {!!}
sound-i (⊢sub ⊢e ¬□ gc s) spl = {!!}
sound-i (⊢tabs₁ ⊢e) none-□ = ⊢tabs₁ (sound-i-0 ⊢e)
sound-i (⊢tabs₃ x ⊢e) (have-t spl) = {!!}
sound-i (⊢tapp ⊢e x) spl = sound-i ⊢e (have-t {!!})

sound-c ⊢e spl = {!!}
