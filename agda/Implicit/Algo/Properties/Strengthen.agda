module Implicit.Algo.Properties.Strengthen where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.Regularity


postulate
  s-strengthen=0 : Γ ,= T ⊢ A' ≤⁺ Σ' ⊣ Δ ,= T ↪ B'
                 → ↑ty0 B ⇘ B'
                 → ↑ty0 A ⇘ A'
                 → ↑tyᶜ0 Σ ⇘ Σ'
                 → Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B

↑tm-↑tyᵉ-comm : e ↑tm k₁ ⇘ e₁
             → e₁ ↑tyᵉ k₂ ⇘ e₂
             → e ↑tyᵉ k₂ ⇘ e'
             → e' ↑tm k₁ ⇘ e₂
↑tm-↑tyᵉ-comm ↑tm-lit ↑tyᵉ-lit ↑tyᵉ-lit = ↑tm-lit
↑tm-↑tyᵉ-comm ↑tm-var ↑tyᵉ-var ↑tyᵉ-var = ↑tm-var
↑tm-↑tyᵉ-comm (↑tm-ƛ up1) (↑tyᵉ-ƛ up2) (↑tyᵉ-ƛ up3) = ↑tm-ƛ (↑tm-↑tyᵉ-comm up1 up2 up3)
↑tm-↑tyᵉ-comm (↑tm-app up1 up4) (↑tyᵉ-app up2 up5) (↑tyᵉ-app up3 up6) = ↑tm-app (↑tm-↑tyᵉ-comm up1 up2 up3) (↑tm-↑tyᵉ-comm up4 up5 up6)
↑tm-↑tyᵉ-comm (↑tm-⦂ up1) (↑tyᵉ-⦂ up2 up) (↑tyᵉ-⦂ up3 up₁) with refl ← ↑ty-unique up₁ up = ↑tm-⦂ (↑tm-↑tyᵉ-comm up1 up2 up3)
↑tm-↑tyᵉ-comm (↑tm-Λ up1) (↑tyᵉ-Λ up2) (↑tyᵉ-Λ up3) = ↑tm-Λ (↑tm-↑tyᵉ-comm up1 up2 up3)

↑tmᶜ-↑tyᶜ-comm : Σ ↑tmᶜ k₁ ⇘ Σ₁
               → Σ₁ ↑tyᶜ k₂ ⇘ Σ₂
               → Σ ↑tyᶜ k₂ ⇘ Σ'
               → Σ' ↑tmᶜ k₁ ⇘ Σ₂
↑tmᶜ-↑tyᶜ-comm ↑tmᶜ-□ ↑tyᶜ-□ ↑tyᶜ-□ = ↑tmᶜ-□
↑tmᶜ-↑tyᶜ-comm ↑tmᶜ-τ (↑tyᶜ-τ up-t) (↑tyᶜ-τ up-t₁) with refl ← ↑ty-unique up-t up-t₁ = ↑tmᶜ-τ
↑tmᶜ-↑tyᶜ-comm (↑tmᶜ-e up-e up1) (↑tyᶜ-e up-e₁ up2) (↑tyᶜ-e up-e₂ up3) = ↑tmᶜ-e (↑tm-↑tyᵉ-comm up-e up-e₁ up-e₂) (↑tmᶜ-↑tyᶜ-comm up1 up2 up3)

↑tmᶜ-comm' : k₁ #≤ k₂
           → Σ ↑tmᶜ k₂ ⇘ Σ₁
           → Σ₁ ↑tmᶜ (inject₁ k₁) ⇘ Σ₂
           ----------------
           → Σ ↑tmᶜ k₁ ⇘ Σ'
           → Σ' ↑tmᶜ #S k₂ ⇘ Σ₂
↑tmᶜ-comm' lt ↑tmᶜ-□ ↑tmᶜ-□ ↑tmᶜ-□ = ↑tmᶜ-□
↑tmᶜ-comm' lt ↑tmᶜ-τ ↑tmᶜ-τ ↑tmᶜ-τ = ↑tmᶜ-τ
↑tmᶜ-comm' lt (↑tmᶜ-e up-e up1) (↑tmᶜ-e up-e₁ up2) (↑tmᶜ-e up-e₂ up3) = ↑tmᶜ-e (↑tm-comm' lt up-e up-e₁ up-e₂) (↑tmᶜ-comm' lt up1 up2 up3)

nonempty-↑tmᶜ : NonEmpty Σ'
              → Σ ↑tmᶜ k ⇘ Σ'
              → NonEmpty Σ
nonempty-↑tmᶜ ne-τ ↑tmᶜ-τ = ne-τ
nonempty-↑tmᶜ ne-app (↑tmᶜ-e up-e upΣ) = ne-app


◀,-unique : Γ ◀ k ,⇘ Γ'
         → Γ ◀ k ,⇘ Δ'
         → Γ' ≡ Δ'
◀,-unique ◀Z ◀Z = refl
◀,-unique (◀S, newΓ) (◀S, newΔ) rewrite ◀,-unique newΓ newΔ = refl
◀,-unique (◀S^ newΓ) (◀S^ newΔ) rewrite ◀,-unique newΓ newΔ = refl
◀,-unique (◀S∙ newΓ) (◀S∙ newΔ) rewrite ◀,-unique newΓ newΔ = refl
◀,-unique (◀S= newΓ) (◀S= newΔ) rewrite ◀,-unique newΓ newΔ = refl
◀,-unique (◀S⋈ newΓ) (◀S⋈ newΔ) rewrite ◀,-unique newΓ newΔ = refl

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


◀,-𝕣 : Γ ◀ k ,⇘ Γ'
     → 𝕣 Γ ◀ k ,⇘ 𝕣 Γ'
◀,-𝕣 ◀Z = ◀Z
◀,-𝕣 (◀S, newΓ) = ◀S, (◀,-𝕣 newΓ)
◀,-𝕣 (◀S^ newΓ) = ◀S^ (◀,-𝕣 newΓ)
◀,-𝕣 (◀S∙ newΓ) = ◀S∙ (◀,-𝕣 newΓ)
◀,-𝕣 (◀S= newΓ) = ◀S= (◀,-𝕣 newΓ)
◀,-𝕣 (◀S⋈ newΓ) = newΓ

t-strengthen, : Γ ⊢ Σ' ⇒ e' ⇒ A
              → Γ ◀ k ,⇘ Γ'
              → Σ ↑tmᶜ k ⇘ Σ'
              → e ↑tm k ⇘ e'
              → Γ' ⊢ Σ ⇒ e ⇒ A

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
t-strengthen, (⊢sub ⊢e ne gc s) newΓ upΣ upe = ⊢sub (t-strengthen, ⊢e newΓ ↑tmᶜ-□ upe) (nonempty-↑tmᶜ ne upΣ) (↑tm-gc' gc upe) (s-strengthen, s (◀S⋈ newΓ) (◀S⋈ newΓ) upΣ)
t-strengthen, (⊢tabs ⊢e) newΓ ↑tmᶜ-□ (↑tm-Λ upe) = ⊢tabs (t-strengthen, ⊢e (◀S∙ newΓ) ↑tmᶜ-□ upe)

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


-- corollaries
s-strengthen,0 : Γ , T ⋈ ⊢ A ≤⁺ Σ' ⊣ Δ , T ⋈  ↪ B
                 → ↑tmᶜ0 Σ ⇘ Σ'
                 → Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Δ ⋈ ↪ B
s-strengthen,0 s up  = s-strengthen, s (◀S⋈ ◀Z) (◀S⋈ ◀Z) up



◀=-unique : Γ ◀ k =⇘ Γ'
          → Γ ◀ k =⇘ Δ'
          → Γ' ≡ Δ'
◀=-unique ◀Z ◀Z = refl
◀=-unique (◀S, new1 up) (◀S, new2 up₁) with refl ← ◀=-unique new1 new2
                                       with refl ← ↑ty-unique-inver up up₁ = refl
◀=-unique (◀S^ new1) (◀S^ new2) with refl ← ◀=-unique new1 new2 = refl
◀=-unique (◀S∙ new1) (◀S∙ new2) with refl ← ◀=-unique new1 new2 = refl
◀=-unique (◀S= new1 x) (◀S= new2 x₁) with refl ← ◀=-unique new1 new2
                                     with refl ← ↑ty-unique-inver x x₁ = refl
◀=-unique (◀S⋈ new1) (◀S⋈ new2) with refl ← ◀=-unique new1 new2 = refl

ss-strengthen= : Γ ⊢ A' ⌞ ≤ ⌝ B' ⊣ Δ
               → Γ ◀ k =⇘ Γ'
              → Δ ◀ k =⇘ Δ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → Γ' ⊢ A ⌞ ≤ ⌝ B ⊣ Δ'

ss-strengthen= ss newΓ newΔ upA upB = {!!}


s-strengthen= : Γ ⊢ A' ≤⁺ Σ' ⊣ Δ ↪ B'
              → Γ ◀ k =⇘ Γ'
              → Δ ◀ k =⇘ Δ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → Σ ↑tyᶜ k ⇘ Σ'
              → Γ' ⊢ A ≤⁺ Σ ⊣ Δ' ↪ B
s-strengthen= (s-empty regΓ cloA x) newΓ newΔ upA upB ↑tyᶜ-□
  with refl ← ◀=-unique newΓ newΔ = s-empty (sregular-strengthen= regΓ newΓ) (⊢c-strengthen= cloA newΓ upA) (≫-strengthen= x regΓ newΔ upA upB)
s-strengthen= (s-type ss) newΓ newΔ upA upB (↑tyᶜ-τ up-t)
  with refl ← ↑ty-unique-inver upB up-t = s-type (ss-strengthen= ss newΓ newΔ upA up-t)
s-strengthen= (s-term-c cloA ap ⊢e s) newΓ newΔ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyᶜ-e up-e upΣ)
  with refl ← ⊢id0 ⊢e
  = s-term-c (⊢c-strengthen= cloA newΓ upA) (≫-strengthen= ap (s-env-in s) newΓ upA upB) {!!} (s-strengthen= s newΓ newΔ upA₁ upB₁ upΣ)
s-strengthen= (s-term-o opnA ⊢e ss s) newΓ newΔ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyᶜ-e up-e upΣ)
  = s-term-o {!⊢o-strengthen=!} {!!} {!!} {!!}
s-strengthen= (s-∀l s upᶜ upᵉ upC upD) newΓ newΔ (↑ty-∀ upA) (↑ty-arr upB upB₁) (↑tyᶜ-e up-e upΣ)
  = s-∀l (s-strengthen= s (◀S^ newΓ) (◀S= newΔ {!!}) upA {!!} {!!}) {!!} {!!} {!!} {!!}
