module Implicit.Interm2Algo.Corollaries where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.Regularity
open import Implicit.Interm.Properties.Polarity
open import Implicit.Interm.Ground
open import Implicit.Interm2Algo.Counter2Context
open import Implicit.Interm2Algo.ExtIrrev
open import Implicit.Interm2Algo.EnvDiff
open import Implicit.Interm2Algo.OpenClose
open import Implicit.Interm2Algo.Find
open import Implicit.Interm2Algo.AuxLemmas
open import Implicit.Interm2Algo.Main2


complete : Γ ⊢ j # e ⦂ A
         → Γ ⊢ ⟨ j , A ⟩ ~t Σ
         → Γ ⊢ Σ ⇒ e ⇒ A
complete (⊢lit cloΓ) ~Z = ⊢lit cloΓ
complete (⊢var cloΓ x∈Γ) ~Z = ⊢var cloΓ x∈Γ
complete (⊢ann ⊢e) ~Z = ⊢ann (complete ⊢e ~∞)
complete (⊢lam₁ ⊢e) ~∞ = ⊢lam₁ (complete ⊢e ~∞)
complete (⊢lam₂ ⊢e) (~I {Σ = Σ} ⊢e₁ j~Σ)
  with reg-S, regΓ regA ← t-tregular ⊢e
  with ⟨ Σ' , upΣ ⟩ ← ↑tmᶜ0-total Σ
  = ⊢lam₂ ⊢e₁ upΣ (complete ⊢e (~weaken,0 j~Σ upΣ regA))
complete (⊢app₁ ⊢e ⊢e₁) j~Σ = ⊢app (complete ⊢e (~C (complete ⊢e₁ ~∞) j~Σ))
complete (⊢app₂ ⊢e ⊢e₁) j~Σ = ⊢app (complete ⊢e (~I (complete ⊢e₁ ~Z) j~Σ))
complete (⊢sub ⊢e B≤A x j≢Z) j~Σ = ⊢sub (complete ⊢e ~Z) (nonempty j≢Z j~Σ) x (complete-s0 B≤A j~Σ)
  where nonempty : NonZ j
                 → Γ ⊢ ⟨ j , A ⟩ ~t Σ
                 → NonEmpty Σ
        nonempty nz-∞ ~∞ = ne-τ
        nonempty nz-I (~I ⊢e j~Σ) = ne-app
        nonempty nz-C (~C ⊢e j~Σ) = ne-app
        nonempty nz-T (~T ~j st) = ne-tapp
complete (⊢tabs ⊢e) ~Z = ⊢tabs (complete ⊢e ~Z)
complete (⊢tapp ⊢e st) ~j = ⊢tapp (complete ⊢e (~T ~j st)) st

-- corollaries
complete-0 : Γ ⊢ Z # e ⦂ A
           → Γ ⊢ □ ⇒ e ⇒ A
complete-0 ⊢e = complete ⊢e ~Z

complete-∞ : Γ ⊢ ∞ # e ⦂ A
           → Γ ⊢ τ A ⇒ e ⇒ A
complete-∞ ⊢e = complete ⊢e ~∞
