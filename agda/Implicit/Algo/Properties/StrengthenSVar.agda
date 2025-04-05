module Implicit.Algo.Properties.StrengthenSVar where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.Regularity
{-
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

◀=-⊆-total : Γ ⊆ Δ
           → Γ ◀ k =⇘ Γ'
           → ∃[ Δ' ](Δ ◀ k =⇘ Δ')
◀=-⊆-total (uvar ext) (◀S∙ newΓ) = ⟨ ◀=-⊆-total ext newΓ .proj₁ ,∙ , ◀S∙ (◀=-⊆-total ext newΓ .proj₂) ⟩
◀=-⊆-total (evar ext) (◀S^ newΓ) = ⟨ ◀=-⊆-total ext newΓ .proj₁ ,^ , ◀S^ (◀=-⊆-total ext newΓ .proj₂) ⟩
◀=-⊆-total (evar-sol ext regA) (◀S^ newΓ)
  with ⟨ Δ' , newΔ ⟩ ← ◀=-⊆-total ext newΓ
  with ⟨ preA , uppA ⟩ ← ⊢r-◀-↑ty-surjective regA newΔ
  = ⟨ Δ' ,= preA , (◀S= newΔ uppA) ⟩
◀=-⊆-total (svar {Δ = Δ} ext regA) ◀Z = ⟨ Δ , ◀Z ⟩
◀=-⊆-total (svar ext regA) (◀S= {A = A} newΓ x) = ⟨ ◀=-⊆-total ext newΓ .proj₁ ,= A , ◀S= (◀=-⊆-total ext newΓ .proj₂) x ⟩
◀=-⊆-total (mark regΓ) (◀S⋈ {Γ' = Γ'} newΓ) = ⟨ Γ' ⋈ , ◀S⋈ newΓ ⟩

inst-strengthen= : [ B' / punchIn k X ] Γ ⟹ Δ
                 → Γ ◀ k =⇘ Γ'
                 → Δ ◀ k =⇘ Δ'
                 → B ↑ty k ⇘ B'
                 → [ B / X ] Γ' ⟹ Δ'
inst-strengthen= {k = #0} {#0} (⟹=S inst up1 regB) ◀Z ◀Z upB
  with refl ← ↑ty-unique-inver up1 upB = inst
inst-strengthen= {k = #0} {#S X} (⟹=S inst up1 regB) ◀Z ◀Z upB
  with refl ← ↑ty-unique-inver up1 upB = inst
inst-strengthen= {k = #S k} {#0} (⟹^0 up regA env) (◀S^ newΓ) (◀S= newΔ x) upB
  with refl ← ◀=-unique newΓ newΔ = ⟹^0 (↑ty-comm1 upB up x) (⊢r-strengthen= regA newΓ x) (sregular-strengthen= env newΓ)
inst-strengthen= {k = #S k} {#S X} (⟹^S inst up1) (◀S^ newΓ) (◀S^ newΔ) upB
  with regA ← inst-⊢r inst
  with ⟨ preA , uppA ⟩ ← ⊢r-◀-↑ty-surjective regA newΓ = ⟹^S (inst-strengthen= inst newΓ newΔ uppA) (↑ty-comm1 upB up1 uppA)
inst-strengthen= {k = #S k} {#S X} (⟹∙S inst up1) (◀S∙ newΓ) (◀S∙ newΔ) upB
  with regA ← inst-⊢r inst
  with ⟨ preA , uppA ⟩ ← ⊢r-◀-↑ty-surjective regA newΓ = ⟹∙S (inst-strengthen= inst newΓ newΔ uppA) (↑ty-comm1 upB up1 uppA)
inst-strengthen= {k = #S k} {#S X} (⟹=S inst up1 regB) (◀S= newΓ x) (◀S= newΔ x₁) upB
  with refl ← ↑ty-unique-inver x x₁
  with regA ← inst-⊢r inst
  with ⟨ preA , uppA ⟩ ← ⊢r-◀-↑ty-surjective regA newΓ = ⟹=S (inst-strengthen= inst newΓ newΔ uppA) (↑ty-comm1 upB up1 uppA) (⊢r-strengthen= regB newΓ x₁)
-}

postulate
  ss-strengthen= : Γ ⊢ A' ⌞ ≤ ⌝ B' ⊣ Δ
               → Γ ◀ k =⇘ Γ'
               → Δ ◀ k =⇘ Δ'
               → A ↑ty k ⇘ A'
               → B ↑ty k ⇘ B'
               → Γ' ⊢ A ⌞ ≤ ⌝ B ⊣ Δ'
{-
ss-strengthen= (s-int regΓ) newΓ newΔ ↑ty-int ↑ty-int
   with refl ← ◀=-unique newΓ newΔ = s-int (sregular-strengthen= regΓ newΓ)
ss-strengthen= {B = ‶ X} (s-var-∙ regΓ x) newΓ newΔ ↑ty-var upB
  with refl ← ↑ty-var-inv upB refl
  with refl ← ◀=-unique newΓ newΔ
  = s-var-∙ (sregular-strengthen= regΓ newΓ) (∋∙-strengthen= x newΓ)
ss-strengthen= (s-ex-l^ inst) newΓ newΔ ↑ty-var upB = s-ex-l^ (inst-strengthen= inst newΓ newΔ upB)
ss-strengthen= (s-ex-r^ inst) newΓ newΔ upA ↑ty-var = s-ex-r^ (inst-strengthen= inst newΓ newΔ upA)
ss-strengthen= (s-ex-l= regΓ x-in) newΓ newΔ ↑ty-var upB
  with refl ← ◀=-unique newΓ newΔ = s-ex-l= (sregular-strengthen= regΓ newΓ) (∋:=-strengthen=-reg regΓ x-in newΔ upB)
ss-strengthen= (s-ex-r= regΓ x-in) newΓ newΔ upA ↑ty-var
  with refl ← ◀=-unique newΓ newΔ = s-ex-r= (sregular-strengthen= regΓ newΓ) (∋:=-strengthen=-reg regΓ x-in newΔ upA)
ss-strengthen= (s-arr ss ss₁) newΓ newΔ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  with ⟨ Ω , newΩ ⟩ ← ◀=-⊆-total (ss-⊆ ss) newΓ
  = s-arr (ss-strengthen= ss newΓ newΩ upB upA) (ss-strengthen= ss₁ newΩ newΔ upA₁ upB₁)
ss-strengthen= (s-∀ ss) newΓ newΔ (↑ty-∀ upA) (↑ty-∀ upB) = s-∀ (ss-strengthen= ss (◀S∙ newΓ) (◀S∙ newΔ) upA upB)

◀=-𝕣 : Γ ◀ k =⇘ Γ'
     → 𝕣 Γ ◀ k =⇘ 𝕣 Γ'
◀=-𝕣 ◀Z = ◀Z
◀=-𝕣 (◀S, newΓ up) = ◀S, (◀=-𝕣 newΓ) up
◀=-𝕣 (◀S^ newΓ) = ◀S^ (◀=-𝕣 newΓ)
◀=-𝕣 (◀S∙ newΓ) = ◀S∙ (◀=-𝕣 newΓ)
◀=-𝕣 (◀S= newΓ x) = ◀S= (◀=-𝕣 newΓ) x
◀=-𝕣 (◀S⋈ newΓ) = newΓ
-}

postulate
  t-strengthen= : Γ ⊢ Σ' ⇒ e' ⇒ A'
              → Γ ◀ k =⇘ Γ'
              → A ↑ty k ⇘ A'
              → e ↑tyᵉ k ⇘ e'
              → Σ ↑tyᶜ k ⇘ Σ'
              → Γ' ⊢ Σ ⇒ e ⇒ A

  s-strengthen= : Γ ⊢ A' ≤⁺ Σ' ⊣ Δ ↪ B'
              → Γ ◀ k =⇘ Γ'
              → Δ ◀ k =⇘ Δ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → Σ ↑tyᶜ k ⇘ Σ'
              → Γ' ⊢ A ≤⁺ Σ ⊣ Δ' ↪ B
{-
t-strengthen= (⊢lit regΓ) newΓ ↑ty-int ↑tyᵉ-lit ↑tyᶜ-□ = ⊢lit (tregular-strengthen= regΓ newΓ)
t-strengthen= (⊢var regΓ x∈Γ) newΓ upA ↑tyᵉ-var ↑tyᶜ-□ = ⊢var (tregular-strengthen= regΓ newΓ) (∋⦂-strengthen= x∈Γ regΓ newΓ upA)
t-strengthen= (⊢ann ⊢e) newΓ upA (↑tyᵉ-⦂ upe up) ↑tyᶜ-□
  with regB ← t-⊢r ⊢e
  with ⟨ _ , uppB ⟩ ← ⊢r-◀-↑ty-surjective regB newΓ
  with refl ← ↑ty-unique-inver upA up
  = ⊢ann (t-strengthen= ⊢e newΓ uppB upe (↑tyᶜ-τ upA))
t-strengthen= (⊢app ⊢e) newΓ upA (↑tyᵉ-app upe upe₁) upΣ
  with ⊢r-arr regA regA₁ ← t-⊢r ⊢e
  with ⟨ _ , uppA ⟩ ← ⊢r-◀-↑ty-surjective regA newΓ
  = ⊢app (t-strengthen= ⊢e newΓ (↑ty-arr uppA upA) upe (↑tyᶜ-e upe₁ upΣ))
t-strengthen= (⊢lam₁ ⊢e) newΓ (↑ty-arr upA upA₁) (↑tyᵉ-ƛ upe) (↑tyᶜ-τ (↑ty-arr up-t up-t₁))
  with refl ← ↑ty-unique-inver upA up-t
  = ⊢lam₁ (t-strengthen= ⊢e (◀S, newΓ upA) upA₁ upe (↑tyᶜ-τ up-t₁))
t-strengthen= (⊢lam₂ ⊢e up-c ⊢e₁) newΓ (↑ty-arr upA upA₁) (↑tyᵉ-ƛ upe) (↑tyᶜ-e {Σ = Σ} up-e upΣ)
  with ⟨ Σ' , upΣ' ⟩ ← ↑tmᶜ0-total Σ
  = ⊢lam₂ (t-strengthen= ⊢e newΓ upA up-e ↑tyᶜ-□) upΣ'
          (t-strengthen= ⊢e₁ (◀S, newΓ upA) upA₁ upe (↑tmᶜ-↑tyᶜ-comm' upΣ' upΣ up-c))
t-strengthen= (⊢sub ⊢e ne gc s) newΓ upA upe upΣ
  with regA ← t-⊢r ⊢e
  with ⟨ pA , uppA ⟩ ← ⊢r-◀-↑ty-surjective regA newΓ
  = ⊢sub (t-strengthen= ⊢e newΓ uppA upe ↑tyᶜ-□) (nonempty-↑tyᶜ ne upΣ) (↑ty-gc' gc upe)
                                                        (s-strengthen= s (◀S⋈ newΓ) (◀S⋈ newΓ) uppA upA upΣ)
t-strengthen= (⊢tabs ⊢e) newΓ (↑ty-∀ upA) (↑tyᵉ-Λ upe) ↑tyᶜ-□ = ⊢tabs (t-strengthen= ⊢e (◀S∙ newΓ) upA upe ↑tyᶜ-□)


s-strengthen= (s-empty regΓ cloA x) newΓ newΔ upA upB ↑tyᶜ-□
  with refl ← ◀=-unique newΓ newΔ = s-empty (sregular-strengthen= regΓ newΓ) (⊢c-strengthen= cloA newΓ upA) (≫-strengthen= x regΓ newΔ upA upB)
s-strengthen= (s-type ss) newΓ newΔ upA upB (↑tyᶜ-τ up-t)
  with refl ← ↑ty-unique-inver upB up-t = s-type (ss-strengthen= ss newΓ newΔ upA up-t)
s-strengthen= (s-term-c cloA ap ⊢e s) newΓ newΔ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyᶜ-e up-e upΣ)
  with refl ← ⊢id0 ⊢e
  = s-term-c (⊢c-strengthen= cloA newΓ upA)
             (≫-strengthen= ap (s-env-in s) newΓ upA upB)
             (t-strengthen= ⊢e (◀=-𝕣 newΓ) upB up-e (↑tyᶜ-τ upB))
             (s-strengthen= s newΓ newΔ upA₁ upB₁ upΣ)
s-strengthen= (s-term-o opnA ⊢e ss s) newΓ newΔ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyᶜ-e up-e upΣ)
  with ⟨ Ω' , newΩ ⟩ ← ◀=-⊆-total (ss-⊆ ss) newΓ
  = s-term-o (⊢o-strengthen= opnA newΓ upA)
             (t-strengthen= ⊢e (◀=-𝕣 newΓ) upB up-e ↑tyᶜ-□)
             (ss-strengthen= ss newΓ newΩ upB upA)
             (s-strengthen= s newΩ newΔ upA₁ upB₁ upΣ)
s-strengthen= (s-∀l s upᶜ upᵉ upC upD) newΓ newΔ (↑ty-∀ upA) (↑ty-arr {A = A} {B = B} upB upB₁) (↑tyᶜ-e {e = e} {Σ = Σ} up-e upΣ)
  with reg-S= regΔ regB ← s-env-out s
  with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
  with ⟨ Σ' , upΣ' ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ A' , upA' ⟩ ← ↑ty0-total A
  with ⟨ B' , upB' ⟩ ← ↑ty0-total B
  with ⟨ pB , uppB ⟩ ← ⊢r-◀-↑ty-surjective regB newΔ
  = s-∀l (s-strengthen= s (◀S^ newΓ) (◀S= newΔ uppB) upA
                        (↑ty-arr (↑ty-comm0' upB upC upA') (↑ty-comm0' upB₁ upD upB'))
                        (↑tyᶜ-e (↑tyᵉ-comm0' up-e upᵉ upe) (↑tyᶜ-comm0' upΣ upᶜ upΣ')))
         upΣ' upe upA' upB'
-}

-- corollaries
s-strengthen=0 : Γ ,= T ⊢ A' ≤⁺ Σ' ⊣ Δ ,= T ↪ B'
                 → ↑ty0 B ⇘ B'
                 → ↑ty0 A ⇘ A'
                 → ↑tyᶜ0 Σ ⇘ Σ'
                 → Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
s-strengthen=0 s upB upA upΣ = s-strengthen= s ◀Z ◀Z upA upB upΣ
