module Implicit.Algo.Properties.StrengthenTVar where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.Regularity


◀,-⊆-total : Γ ⊆ Δ
           → Γ ◀ k ,⇘ Γ'
           → ∃[ Δ' ](Δ ◀ k ,⇘ Δ')
◀,-⊆-total (uvar ext) (◀S∙ newΓ) = ⟨ ◀,-⊆-total ext newΓ .proj₁ ,∙ , ◀S∙ (◀,-⊆-total ext newΓ .proj₂) ⟩
◀,-⊆-total (evar ext) (◀S^ newΓ) = ⟨ ◀,-⊆-total ext newΓ .proj₁ ,^ , ◀S^ (◀,-⊆-total ext newΓ .proj₂) ⟩
◀,-⊆-total (evar-sol {A = A} ext regA) (◀S^ newΓ) = ⟨ ◀,-⊆-total ext newΓ .proj₁ ,= A , ◀S= (◀,-⊆-total ext newΓ .proj₂) ⟩
◀,-⊆-total (svar ext regA) (◀S= {A = A} newΓ) = ⟨ ◀,-⊆-total ext newΓ .proj₁ ,= A , ◀S= (◀,-⊆-total ext newΓ .proj₂) ⟩
◀,-⊆-total (mark regΓ) (◀S⋈ {Γ' = Γ'} newΓ) = ⟨ Γ' ⋈ , ◀S⋈ newΓ ⟩

inst-strengthen, : [ A / X ] Γ ⟹ Δ
                 → Γ ◀ k ,⇘ Γ'
                 → Δ ◀ k ,⇘ Δ'
                 → [ A / X ] Γ' ⟹ Δ'
inst-strengthen, (⟹^0 up regA env) (◀S^ newΓ) (◀S= newΔ) with refl ← ◀,-unique newΓ newΔ = ⟹^0 up (⊢r-strengthen, regA newΓ) (sregular-strengthen, env newΓ)
inst-strengthen, (⟹^S inst up1) (◀S^ newΓ) (◀S^ newΔ) = ⟹^S (inst-strengthen, inst newΓ newΔ) up1
inst-strengthen, (⟹∙S inst up1) (◀S∙ newΓ) (◀S∙ newΔ) = ⟹∙S (inst-strengthen, inst newΓ newΔ) up1
inst-strengthen, (⟹=S inst up1 regB) (◀S= newΓ) (◀S= newΔ) = ⟹=S (inst-strengthen, inst newΓ newΔ) up1 (⊢r-strengthen, regB newΓ)

ss-strengthen, : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
               → Γ ◀ k ,⇘ Γ'
               → Δ ◀ k ,⇘ Δ'
               → Γ' ⊢ A ⌞ ≤ ⌝ B ⊣ Δ'
ss-strengthen, (s-int regΓ) newΓ newΔ with refl ← ◀,-unique newΓ newΔ = s-int (sregular-strengthen, regΓ newΔ)
ss-strengthen, (s-var-∙ regΓ x) newΓ newΔ
  with refl ← ◀,-unique newΓ newΔ = s-var-∙ (sregular-strengthen, regΓ newΓ) (∋∙-strengthen, x newΓ)
ss-strengthen, (s-ex-l^ inst) newΓ newΔ = s-ex-l^ (inst-strengthen, inst newΓ newΔ)
ss-strengthen, (s-ex-r^ inst) newΓ newΔ = s-ex-r^ (inst-strengthen, inst newΓ newΔ)
ss-strengthen, (s-ex-l= regΓ x-in) newΓ newΔ with refl ← ◀,-unique newΓ newΔ = s-ex-l= (sregular-strengthen, regΓ newΓ) (∋:=-strengthen, x-in newΓ)
ss-strengthen, (s-ex-r= regΓ x-in) newΓ newΔ with refl ← ◀,-unique newΓ newΔ = s-ex-r= (sregular-strengthen, regΓ newΓ) (∋:=-strengthen, x-in newΓ)
ss-strengthen, (s-arr ss ss₁) newΓ newΔ with ◀,-⊆-total (ss-⊆ ss) newΓ
... | ⟨ Ω' , newΩ ⟩ = s-arr (ss-strengthen, ss newΓ newΩ) (ss-strengthen, ss₁ newΩ newΔ)
ss-strengthen, (s-∀ ss) newΓ newΔ = s-∀ (ss-strengthen, ss (◀S∙ newΓ) (◀S∙ newΔ))


t-strengthen, : Γ ⊢ Σ' ⇒ e' ⇒ A
              → Γ ◀ k ,⇘ Γ'
              → Σ ↑tmᶜ k ⇘ Σ'
              → e ↑tm k ⇘ e'
              → Γ' ⊢ Σ ⇒ e ⇒ A

infs-strengthen, : Γ ⊨ Σ' ⟹ A
                 → Γ ◀ k ,⇘ Γ'
                 → Σ ↑tmᶜ k ⇘ Σ'
                 → Γ' ⊨ Σ ⟹ A
infs-strengthen, (infs-z regΓ regA) newΓ ↑tmᶜ-τ = infs-z (tregular-strengthen, regΓ newΓ) (⊢r-strengthen, regA newΓ)
infs-strengthen, (infs-s ⊢e infs) newΓ (↑tmᶜ-e up-e upΣ) = infs-s (t-strengthen, ⊢e newΓ ↑tmᶜ-□ up-e) (infs-strengthen, infs newΓ upΣ)


s-strengthen, : Γ ⊢ A ≤⁺ Σ' ⊣ Δ ↪ B
              → Γ ◀ k ,⇘ Γ'
              → Δ ◀ k ,⇘ Δ'
              → Σ ↑tmᶜ k ⇘ Σ'
              → Γ' ⊢ A ≤⁺ Σ ⊣ Δ' ↪ B

t-strengthen, (⊢lit regΓ) newΓ ↑tmᶜ-□ ↑tm-lit = ⊢lit (tregular-strengthen, regΓ newΓ)
t-strengthen, (⊢var regΓ x∈Γ) newΓ ↑tmᶜ-□ ↑tm-var = ⊢var (tregular-strengthen, regΓ newΓ) (∋⦂-strengthen, x∈Γ newΓ)
t-strengthen, (⊢ann ⊢e) newΓ ↑tmᶜ-□ (↑tm-⦂ upe) = ⊢ann (t-strengthen, ⊢e newΓ ↑tmᶜ-τ upe)
t-strengthen, (⊢app ⊢e) newΓ upΣ (↑tm-app upe upe₁) = ⊢app (t-strengthen, ⊢e newΓ (↑tmᶜ-e upe₁ upΣ) upe)
t-strengthen, (⊢lam₁ ⊢e) newΓ ↑tmᶜ-τ (↑tm-ƛ upe) = ⊢lam₁ (t-strengthen, ⊢e (◀S, newΓ) ↑tmᶜ-τ upe)
t-strengthen, (⊢lam₂ ⊢e up-c ⊢e₁) newΓ (↑tmᶜ-e {Σ = Σ} up-e upΣ) (↑tm-ƛ upe) with ↑tmᶜ0-total Σ
... | ⟨ Σ' , upΣ' ⟩ = ⊢lam₂ (t-strengthen, ⊢e newΓ ↑tmᶜ-□ up-e) upΣ' (t-strengthen, ⊢e₁ (◀S, newΓ) (↑tmᶜ-comm' z≤n upΣ up-c upΣ') upe)
t-strengthen, (⊢sub ⊢e ne gc s) newΓ upΣ upe = ⊢sub (t-strengthen, ⊢e newΓ ↑tmᶜ-□ upe) (nonempty-↑tmᶜ' ne upΣ) (↑tm-gc' gc upe) (s-strengthen, s (◀S⋈ newΓ) (◀S⋈ newΓ) upΣ)
t-strengthen, (⊢tabs ⊢e) newΓ ↑tmᶜ-□ (↑tm-Λ upe) = ⊢tabs (t-strengthen, ⊢e (◀S∙ newΓ) ↑tmᶜ-□ upe)
t-strengthen, (⊢tapp ⊢e st) newΓ newΣ (↑tm-⓪ upe) = ⊢tapp (t-strengthen, ⊢e newΓ (↑tmᶜ-⓪ newΣ) upe) st

s-strengthen, (s-empty regΓ cloA x) newΓ newΔ ↑tmᶜ-□ with refl ← ◀,-unique newΓ newΔ = s-empty (sregular-strengthen, regΓ newΓ)
                                                                                               (⊢c-strengthen, cloA newΓ)
                                                                                               (≫-strengthen, x newΓ)
s-strengthen, (s-type ss) newΓ newΔ ↑tmᶜ-τ = s-type (ss-strengthen, ss newΓ newΔ)
s-strengthen, (s-term-c cloA ap ⊢e s) newΓ newΔ (↑tmᶜ-e up-e upΣ) = s-term-c (⊢c-strengthen, cloA newΓ) (≫-strengthen, ap newΓ)
                                                                             (t-strengthen, ⊢e (◀,-𝕣 newΓ) ↑tmᶜ-τ up-e) (s-strengthen, s newΓ newΔ upΣ)
s-strengthen, (s-term-o opnA ⊢e ss s) newΓ newΔ (↑tmᶜ-e up-e upΣ) with ◀,-⊆-total (ss-⊆ ss) newΓ
... | ⟨ Ω' , newΩ ⟩ = s-term-o (⊢o-strengthen, opnA newΓ) (t-strengthen, ⊢e (◀,-𝕣 newΓ) ↑tmᶜ-□ up-e) (ss-strengthen, ss newΓ newΩ) (s-strengthen, s newΩ newΔ upΣ)
s-strengthen, (s-∀l s upᶜ upᵉ upC upD) newΓ newΔ (↑tmᶜ-e {e = e} {Σ = Σ} up-e upΣ)
  with ⟨ Σ' , upΣ' ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  = s-∀l (s-strengthen, s (◀S^ newΓ) (◀S= newΔ) (↑tmᶜ-e (↑tm-↑tyᵉ-comm up-e upᵉ upe) (↑tmᶜ-↑tyᶜ-comm upΣ upᶜ upΣ'))) upΣ' upe upC upD
s-strengthen, (s-∀l-no s upᶜ upᵉ upC upD) newΓ newΔ (↑tmᶜ-e {e = e} {Σ = Σ} up-e upΣ)
  with ⟨ Σ' , upΣ' ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  = s-∀l-no (s-strengthen, s (◀S^ newΓ) (◀S^ newΔ) (↑tmᶜ-e (↑tm-↑tyᵉ-comm up-e upᵉ upe) (↑tmᶜ-↑tyᶜ-comm upΣ upᶜ upΣ'))) upΣ' upe upC upD
s-strengthen, (s-tapp s upᶜ) newΓ newΔ (↑tmᶜ-⓪ {Σ = Σ} upΣ)
  with ⟨ Σ' , upΣ' ⟩ ← ↑tyᶜ0-total Σ
  = s-tapp (s-strengthen, s (◀S= newΓ) (◀S= newΔ) (↑tmᶜ-↑tyᶜ-comm upΣ upᶜ upΣ')) upΣ'
s-strengthen, (s-svar-term inΓ s) newΓ newΔ (↑tmᶜ-e up-e upΣ)
  with refl ← ◀,-unique newΓ newΔ = s-svar-term (∋:=-strengthen, inΓ newΓ) (s-strengthen, s newΓ newΓ (↑tmᶜ-e up-e upΣ))
s-strengthen, (s-svar-tapp inΓ s) newΓ newΔ (↑tmᶜ-⓪ upΣ)
  with refl ← ◀,-unique newΓ newΔ = s-svar-tapp (∋:=-strengthen, inΓ newΓ) (s-strengthen, s newΓ newΓ (↑tmᶜ-⓪ upΣ))
s-strengthen, (s-evar-infers infs inst) newΓ newΔ (↑tmᶜ-e up-e upΣ)
  = s-evar-infers (infs-strengthen, infs (◀,-𝕣 newΓ) (↑tmᶜ-e up-e upΣ)) (inst-strengthen, inst newΓ newΔ)

-- corollaries
s-strengthen,0 : Γ , T ⋈ ⊢ A ≤⁺ Σ' ⊣ Δ , T ⋈  ↪ B
                 → ↑tmᶜ0 Σ ⇘ Σ'
                 → Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Δ ⋈ ↪ B
s-strengthen,0 s up  = s-strengthen, s (◀S⋈ ◀Z) (◀S⋈ ◀Z) up
