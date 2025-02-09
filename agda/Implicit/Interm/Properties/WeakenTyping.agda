module Implicit.Interm.Properties.WeakenTyping where

open import Implicit.Language.All
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.Weaken

----------------------------------------------------------------------
--+                       weaken for typing                        +--
----------------------------------------------------------------------

▶,-∋⦂ : Γ ∋ x ⦂ A
      → Γ ▶ k , T ⇘ Γ'
      → Γ' ∋ punchIn k x ⦂ A
▶,-∋⦂ Z (▶Z cloA) = S, Z
▶,-∋⦂ Z (▶S, upΓ) = Z
▶,-∋⦂ (S, inΓ) (▶Z cloA) = S, (S, inΓ)
▶,-∋⦂ (S, inΓ) (▶S, upΓ) = S, (▶,-∋⦂ inΓ upΓ)
▶,-∋⦂ (S∙ inΓ up) (▶Z cloA) = S, (S∙ inΓ up)
▶,-∋⦂ (S∙ inΓ up) (▶S∙ upΓ x) = S∙ (▶,-∋⦂ inΓ upΓ) up
▶,-∋⦂ (S^ inΓ up) (▶Z cloA) = S, (S^ inΓ up)
▶,-∋⦂ (S^ inΓ up) (▶S^ upΓ x) = S^ (▶,-∋⦂ inΓ upΓ) up
▶,-∋⦂ (S= inΓ up) (▶Z cloA) = S, (S= inΓ up)
▶,-∋⦂ (S= inΓ up) (▶S= upΓ x) = S= (▶,-∋⦂ inΓ upΓ) up

t-weaken, : Γ ⊢ j # e ⦂ A
          → Γ ▶ k , T ⇘ Γ'
          → e ↑tm k ⇘ e'
          → Γ' ⊢ j # e' ⦂ A
t-weaken, (⊢lit cloΣ) newΓ ↑tm-lit = ⊢lit (closed-weaken, cloΣ newΓ)
t-weaken, (⊢var cloΣ x∈Γ) newΓ ↑tm-var = ⊢var (closed-weaken, cloΣ newΓ) (▶,-∋⦂ x∈Γ newΓ)
t-weaken, (⊢ann ⊢e) newΓ (↑tm-⦂ up-e) = ⊢ann (t-weaken, ⊢e newΓ up-e)
t-weaken, (⊢lam₁ ⊢e) newΓ (↑tm-ƛ up-e) = ⊢lam₁ (t-weaken, ⊢e (▶S, newΓ) up-e)
t-weaken, (⊢lam₂ ⊢e) newΓ (↑tm-ƛ up-e) = ⊢lam₂ (t-weaken, ⊢e (▶S, newΓ) up-e)
t-weaken, (⊢app₁ ⊢e ⊢e₁) newΓ (↑tm-app up-e up-e₁) = ⊢app₁ (t-weaken, ⊢e newΓ up-e) (t-weaken, ⊢e₁ newΓ up-e₁)
t-weaken, (⊢app₂ ⊢e ⊢e₁) newΓ (↑tm-app up-e up-e₁) = ⊢app₂ (t-weaken, ⊢e newΓ up-e) (t-weaken, ⊢e₁ newΓ up-e₁)
t-weaken, (⊢sub ⊢e B≤A j≢Z) newΓ up-e = ⊢sub (t-weaken, ⊢e newΓ up-e) (s-weaken, B≤A newΓ) j≢Z
t-weaken, {T = T} (⊢tabs ⊢e) newΓ (↑tm-Λ up-e) = ⊢tabs (t-weaken, ⊢e (▶S∙ newΓ (proj₂ (↑ty0-total T))) up-e)

t-weaken,0 : Γ ⊢ j # e ⦂ A
           → Γ ⊢c T
           → ↑tm0 e ⇘ e'
           → Γ , T ⊢ j # e' ⦂ A
t-weaken,0 ⊢e cloT up-e = t-weaken, ⊢e (▶Z cloT) up-e
