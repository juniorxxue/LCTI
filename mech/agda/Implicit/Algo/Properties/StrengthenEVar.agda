module Implicit.Algo.Properties.StrengthenEVar where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.Regularity

abstract
  ◀^-unique : Γ ◀ k ^⇘ Γ'
            → Γ ◀ k ^⇘ Δ'
            → Γ' ≡ Δ'
  ◀^-unique ◀Z ◀Z = refl
  ◀^-unique (◀S, new1 x) (◀S, new2 x₁) with refl ← ◀^-unique new1 new2
                                       with refl ← ↑ty-unique-inver x x₁ = refl
  ◀^-unique (◀S^ new1) (◀S^ new2) with refl ← ◀^-unique new1 new2 = refl
  ◀^-unique (◀S∙ new1) (◀S∙ new2) with refl ← ◀^-unique new1 new2 = refl
  ◀^-unique (◀S= new1 x) (◀S= new2 x₁) with refl ← ◀^-unique new1 new2
                                       with refl ← ↑ty-unique-inver x x₁ = refl
  ◀^-unique (◀S⋈ new1) (◀S⋈   new2) with refl ← ◀^-unique new1 new2 = refl


  ◀^-⊆-total : Γ ⊆ Ω
             → Ω ⊆ Δ
             → Γ ◀ k ^⇘ Γ'
             → Δ ◀ k ^⇘ Δ'
             → ∃[ Ω' ](Ω ◀ k ^⇘ Ω')
  ◀^-⊆-total (uvar ext1) (uvar ext2) (◀S∙ new1) (◀S∙ new2) = ⟨ ◀^-⊆-total ext1 ext2 new1 new2 .proj₁ ,∙ ,
                                                              ◀S∙ (◀^-⊆-total ext1 ext2 new1 new2 .proj₂) ⟩
  ◀^-⊆-total (evar {Δ = Δ} ext1) (evar ext2) ◀Z ◀Z = ⟨ Δ , ◀Z ⟩
  ◀^-⊆-total (evar ext1) (evar ext2) (◀S^ new1) (◀S^ new2) = ⟨ ◀^-⊆-total ext1 ext2 new1 new2 .proj₁ ,^ ,
                                                              ◀S^ (◀^-⊆-total ext1 ext2 new1 new2 .proj₂) ⟩
  ◀^-⊆-total (evar ext1) (evar-sol ext2 regA) (◀S^ new1) (◀S= new2 x) = ⟨ ◀^-⊆-total ext1 ext2 new1 new2 .proj₁ ,^ ,
                                                                         ◀S^ (◀^-⊆-total ext1 ext2 new1 new2 .proj₂) ⟩
  ◀^-⊆-total (evar-sol ext1 regA) (svar ext2 regA₁) (◀S^ new1) (◀S= {A = A} new2 x) = ⟨ ◀^-⊆-total ext1 ext2 new1 new2 .proj₁ ,= A ,
                                                                               ◀S= (◀^-⊆-total ext1 ext2 new1 new2 .proj₂) x ⟩
  ◀^-⊆-total (svar ext1 regA) (svar ext2 regA₁) (◀S= new1 x) (◀S= {A = A} new2 x₁) = ⟨ ◀^-⊆-total ext1 ext2 new1 new2 .proj₁ ,= A ,
                                                                              ◀S= (◀^-⊆-total ext1 ext2 new1 new2 .proj₂) x₁ ⟩
  ◀^-⊆-total (mark regΓ) (mark regΓ₁) (◀S⋈ {Γ' = Γ'} new1) (◀S⋈ new2) = ⟨ Γ' ⋈ , ◀S⋈ new1 ⟩


  inst-strengthen^ : [ B' / punchIn k X ] Γ ⟹ Δ
                   → Γ ◀ k ^⇘ Γ'
                   → Δ ◀ k ^⇘ Δ'
                   → B ↑ty k ⇘ B'
                   → [ B / X ] Γ' ⟹ Δ'
  inst-strengthen^ {k = #0} {#0} (⟹^S inst up1) ◀Z ◀Z upB
    with refl ← ↑ty-unique-inver up1 upB = inst
  inst-strengthen^ {k = #0} {#S X} (⟹^S inst up1) ◀Z ◀Z upB
    with refl ← ↑ty-unique-inver up1 upB = inst
  inst-strengthen^ {k = #S k} {#0} (⟹^0 up regA env) (◀S^ newΓ) (◀S= newΔ x) upB
    with refl ← ◀^-unique newΓ newΔ = ⟹^0 (↑ty-comm1 upB up x) (⊢r-strengthen^ regA newΓ x) (sregular-strengthen^ env newΓ)
  inst-strengthen^ {k = #S k} {#S X} (⟹^S inst up1) (◀S^ newΓ) (◀S^ newΔ) upB
    with regA ← inst-⊢r inst
    with ⟨ preA , uppA ⟩ ← ⊢r-◀^-↑ty-surjective regA newΓ = ⟹^S (inst-strengthen^ inst newΓ newΔ uppA) (↑ty-comm1 upB up1 uppA)
  inst-strengthen^ {k = #S k} {#S X} (⟹∙S inst up1) (◀S∙ newΓ) (◀S∙ newΔ) upB
    with regA ← inst-⊢r inst
    with ⟨ preA , uppA ⟩ ← ⊢r-◀^-↑ty-surjective regA newΓ = ⟹∙S (inst-strengthen^ inst newΓ newΔ uppA) (↑ty-comm1 upB up1 uppA)
  inst-strengthen^ {k = #S k} {#S X} (⟹=S inst up1 regB) (◀S= newΓ x) (◀S= newΔ x₁) upB
    with refl ← ↑ty-unique-inver x x₁
    with regA ← inst-⊢r inst
    with ⟨ preA , uppA ⟩ ← ⊢r-◀^-↑ty-surjective regA newΓ = ⟹=S (inst-strengthen^ inst newΓ newΔ uppA) (↑ty-comm1 upB up1 uppA) (⊢r-strengthen^ regB newΓ x₁)


  ss-strengthen^ : Γ ⊢ A' ⌞ ≤ ⌝ B' ⊣ Δ
                 → Γ ◀ k ^⇘ Γ'
                 → Δ ◀ k ^⇘ Δ'
                 → A ↑ty k ⇘ A'
                 → B ↑ty k ⇘ B'
                 → Γ' ⊢ A ⌞ ≤ ⌝ B ⊣ Δ'
  ss-strengthen^ (s-int regΓ) newΓ newΔ ↑ty-int ↑ty-int
    with refl ← ◀^-unique newΓ newΔ = s-int (sregular-strengthen^ regΓ newΓ)
  ss-strengthen^ {B = ‶ X} (s-var-∙ regΓ x) newΓ newΔ ↑ty-var upB
    with refl ← ↑ty-var-inv upB refl
    with refl ← ◀^-unique newΓ newΔ = s-var-∙ (sregular-strengthen^ regΓ newΓ) (∋∙-strengthen^ x newΓ)
  ss-strengthen^ (s-ex-l^ inst) newΓ newΔ ↑ty-var upB = s-ex-l^ (inst-strengthen^ inst newΓ newΔ upB)
  ss-strengthen^ (s-ex-r^ inst) newΓ newΔ upA ↑ty-var = s-ex-r^ (inst-strengthen^ inst newΓ newΔ upA)
  ss-strengthen^ (s-ex-l= regΓ x-in) newΓ newΔ ↑ty-var upB
    with refl ← ◀^-unique newΓ newΔ = s-ex-l= (sregular-strengthen^ regΓ newΓ) (∋:=-strengthen^-reg regΓ x-in newΔ upB)
  ss-strengthen^ (s-ex-r= regΓ x-in) newΓ newΔ upA ↑ty-var
    with refl ← ◀^-unique newΓ newΔ = s-ex-r= (sregular-strengthen^ regΓ newΓ) (∋:=-strengthen^-reg regΓ x-in newΔ upA)
  ss-strengthen^ (s-arr s s₁) newΓ newΔ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
    with ⟨ Ω , newΩ ⟩ ← ◀^-⊆-total (ss-⊆ s) (ss-⊆ s₁) newΓ newΔ = s-arr (ss-strengthen^ s newΓ newΩ upB upA) (ss-strengthen^ s₁ newΩ newΔ upA₁ upB₁)
  ss-strengthen^ (s-∀ s) newΓ newΔ (↑ty-∀ upA) (↑ty-∀ upB) = s-∀ (ss-strengthen^ s (◀S∙ newΓ) (◀S∙ newΔ) upA upB)

  ◀^-𝕣 : Γ ◀ k ^⇘ Γ'
       → 𝕣 Γ ◀ k ^⇘ 𝕣 Γ'
  ◀^-𝕣 ◀Z = ◀Z
  ◀^-𝕣 (◀S, new x) = ◀S, (◀^-𝕣 new) x
  ◀^-𝕣 (◀S^ new) = ◀S^ (◀^-𝕣 new)
  ◀^-𝕣 (◀S∙ new) = ◀S∙ (◀^-𝕣 new)
  ◀^-𝕣 (◀S= new x) = ◀S= (◀^-𝕣 new) x
  ◀^-𝕣 (◀S⋈ new) = new


  t-strengthen^ : Γ ⊢ Σ' ⇒ e' ⇒ A'
                → Γ ◀ k ^⇘ Γ'
                → A ↑ty k ⇘ A'
                → e ↑tyᵉ k ⇘ e'
                → Σ ↑tyᶜ k ⇘ Σ'
                → Γ' ⊢ Σ ⇒ e ⇒ A

  infs-strengthen^ : Γ ⊨ Σ' ⟹ A'
                   → Γ ◀ k ^⇘ Γ'
                   → A ↑ty k ⇘ A'
                   → Σ ↑tyᶜ k ⇘ Σ'
                   → Γ' ⊨ Σ ⟹ A
  infs-strengthen^ (infs-z regΓ regA) newΓ upA (↑tyᶜ-τ up-t)
    with refl ← ↑ty-unique-inver upA up-t = infs-z (tregular-strengthen^ regΓ newΓ) (⊢r-strengthen^ regA newΓ up-t)
  infs-strengthen^ (infs-s ⊢e infs) newΓ (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) =
    infs-s (t-strengthen^ ⊢e newΓ upA up-e ↑tyᶜ-□) (infs-strengthen^ infs newΓ upA₁ upΣ)


  s-strengthen^ : Γ ⊢ A' ≤⁺ Σ' ⊣ Δ ↪ B'
                → Γ ◀ k ^⇘ Γ'
                → Δ ◀ k ^⇘ Δ'
                → A ↑ty k ⇘ A'
                → B ↑ty k ⇘ B'
                → Σ ↑tyᶜ k ⇘ Σ'
                → Γ' ⊢ A ≤⁺ Σ ⊣ Δ' ↪ B

  t-strengthen^ (⊢lit regΓ) new ↑ty-int ↑tyᵉ-lit ↑tyᶜ-□ = ⊢lit (tregular-strengthen^ regΓ new)
  t-strengthen^ (⊢var regΓ x∈Γ) new upA ↑tyᵉ-var ↑tyᶜ-□ = ⊢var (tregular-strengthen^ regΓ new) (∋⦂-strengthen^ x∈Γ regΓ new upA)
  t-strengthen^ (⊢ann ⊢e) newΓ upA (↑tyᵉ-⦂ upe up) ↑tyᶜ-□
    with regB ← t-⊢r ⊢e
    with ⟨ _ , uppB ⟩ ← ⊢r-◀^-↑ty-surjective regB newΓ
    with refl ← ↑ty-unique-inver upA up = ⊢ann (t-strengthen^ ⊢e newΓ uppB upe (↑tyᶜ-τ upA))
  t-strengthen^ (⊢app ⊢e) new upA (↑tyᵉ-app upe upe₁) upΣ
    with ⊢r-arr regA regA₁ ← t-⊢r ⊢e
    with ⟨ _ , uppA ⟩ ← ⊢r-◀^-↑ty-surjective regA new = ⊢app (t-strengthen^ ⊢e new (↑ty-arr uppA upA) upe (↑tyᶜ-e upe₁ upΣ))
  t-strengthen^ (⊢lam₁ ⊢e) new (↑ty-arr upA upA₁) (↑tyᵉ-ƛ upe) (↑tyᶜ-τ (↑ty-arr up-t up-t₁))
    with refl ← ↑ty-unique-inver upA up-t = ⊢lam₁ (t-strengthen^ ⊢e (◀S, new up-t) upA₁ upe (↑tyᶜ-τ up-t₁))
  t-strengthen^ (⊢lam₂ ⊢e up-c ⊢e₁) new (↑ty-arr upA upA₁) (↑tyᵉ-ƛ upe) (↑tyᶜ-e {Σ = Σ} up-e upΣ)
    with ⟨ Σ' , upΣ' ⟩ ← ↑tmᶜ0-total Σ = ⊢lam₂ (t-strengthen^ ⊢e new upA up-e ↑tyᶜ-□)
                                               upΣ'
                                               (t-strengthen^ ⊢e₁ (◀S, new upA) upA₁ upe (↑tmᶜ-↑tyᶜ-comm' upΣ' upΣ up-c))
  t-strengthen^ (⊢sub ⊢e ne gc s) new upA upe upΣ
    with regA ← t-⊢r ⊢e
    with ⟨ pA , uppA ⟩ ← ⊢r-◀^-↑ty-surjective regA new
    = ⊢sub (t-strengthen^ ⊢e new uppA upe ↑tyᶜ-□) (nonempty-↑tyᶜ ne upΣ) (↑ty-gc' gc upe) (s-strengthen^ s (◀S⋈ new) (◀S⋈ new) uppA upA upΣ)
  t-strengthen^ (⊢tabs ⊢e) new (↑ty-∀ upA) (↑tyᵉ-Λ upe) ↑tyᶜ-□ = ⊢tabs (t-strengthen^ ⊢e (◀S∙ new) upA upe ↑tyᶜ-□)
  t-strengthen^ (⊢tabs-τ ⊢e) new (↑ty-∀ upA) (↑tyᵉ-Λ upe) (↑tyᶜ-τ (↑ty-∀ upA'))
    = ⊢tabs-τ (t-strengthen^ ⊢e (◀S∙ new) upA upe (↑tyᶜ-τ upA'))
  t-strengthen^ (⊢tapp ⊢e regA st s) newΓ upA (↑tyᵉ-⓪ upe upA₁) upΣ
    with regA' ← t-⊢r ⊢e
    with ⟨ pA , ↑ty-∀ uppA ⟩ ← ⊢r-◀^-↑ty-surjective regA' newΓ
    with ⟨ pB ,  uppB ⟩ ← ⊢r-◀^-↑ty-surjective (st0-⊢r regA' st regA) newΓ
    = ⊢tapp (t-strengthen^ ⊢e newΓ (↑ty-∀ uppA) upe ↑tyᶜ-□) (↑ty-st-comm0'' regA upA₁ uppA uppB)
            (⊢r-strengthen^ st newΓ upA₁) (s-strengthen^ s (◀S⋈ newΓ) (◀S⋈ newΓ) uppB upA upΣ)

  s-strengthen^ (s-empty regΓ cloA grd) newΓ newΔ upA upB ↑tyᶜ-□
    with refl ← ◀^-unique newΓ newΔ  = s-empty (sregular-strengthen^ regΓ newΓ) (⊢c-strengthen^ cloA newΓ upA) (≫-strengthen^ grd regΓ newΔ upA upB)
  s-strengthen^ (s-type ss) newΓ newΔ upA upB (↑tyᶜ-τ up-t)
    with refl ← ↑ty-unique-inver upB up-t = s-type (ss-strengthen^ ss newΓ newΔ upA up-t)
  s-strengthen^ (s-term-c cloA ap ⊢e s) newΓ newΔ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyᶜ-e up-e upΣ)
    with refl ← ⊢id0 ⊢e
    = s-term-c (⊢c-strengthen^ cloA newΓ upA)
               (≫-strengthen^ ap (s-env-in s) newΓ upA upB)
               (t-strengthen^ ⊢e (◀^-𝕣 newΓ) upB up-e (↑tyᶜ-τ upB))
               (s-strengthen^ s newΓ newΔ upA₁ upB₁ upΣ)
  s-strengthen^ (s-term-o opnA ⊢e ss s) newΓ newΔ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyᶜ-e up-e upΣ)
    with ⟨ Ω' , newΩ ⟩ ← ◀^-⊆-total (ss-⊆ ss) (s-⊆ s) newΓ newΔ
    = s-term-o (⊢o-strengthen^ opnA newΓ upA)
               (t-strengthen^ ⊢e (◀^-𝕣 newΓ) upB up-e ↑tyᶜ-□)
               (ss-strengthen^ ss newΓ newΩ upB upA)
               (s-strengthen^ s newΩ newΔ upA₁ upB₁ upΣ)
  s-strengthen^ (s-∀l s upᶜ upᵉ upC upD) newΓ newΔ (↑ty-∀ upA) (↑ty-arr {A = A} {B = B} upB upB₁) (↑tyᶜ-e {e = e} {Σ = Σ} up-e upΣ)
    with reg-S= regΔ regB ← s-env-out s
    with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
    with ⟨ Σ' , upΣ' ⟩ ← ↑tyᶜ0-total Σ
    with ⟨ A' , upA' ⟩ ← ↑ty0-total A
    with ⟨ B' , upB' ⟩ ← ↑ty0-total B
    with ⟨ pB , uppB ⟩ ← ⊢r-◀^-↑ty-surjective regB newΔ
    = s-∀l (s-strengthen^ s (◀S^ newΓ) (◀S= newΔ uppB) upA
                          (↑ty-arr (↑ty-comm0' upB upC upA') (↑ty-comm0' upB₁ upD upB'))
                          (↑tyᶜ-e (↑tyᵉ-comm0' up-e upᵉ upe) (↑tyᶜ-comm0' upΣ upᶜ upΣ')))
           upΣ' upe upA' upB'
  s-strengthen^ (s-∀l-no s upᶜ upᵉ upC upD) newΓ newΔ (↑ty-∀ upA) (↑ty-arr {A = A} {B = B} upB upB₁) (↑tyᶜ-e {e = e} {Σ = Σ} up-e upΣ)
    with reg-S^ regΓ ← s-env-out s
    with ⟨ e' , upe ⟩ ← ↑tyᵉ0-total e
    with ⟨ Σ' , upΣ' ⟩ ← ↑tyᶜ0-total Σ
    with ⟨ A' , upA' ⟩ ← ↑ty0-total A
    with ⟨ B' , upB' ⟩ ← ↑ty0-total B
    = s-∀l-no (s-strengthen^ s (◀S^ newΓ) (◀S^ newΔ) upA
                          (↑ty-arr (↑ty-comm0' upB upC upA') (↑ty-comm0' upB₁ upD upB'))
                          (↑tyᶜ-e (↑tyᵉ-comm0' up-e upᵉ upe) (↑tyᶜ-comm0' upΣ upᶜ upΣ')))
           upΣ' upe upA' upB'
  s-strengthen^ (s-svar-term inΓ s) newΓ newΔ ↑ty-var (↑ty-arr upB upB₁) (↑tyᶜ-e up-e upΣ)
    with refl ← ◀^-unique newΓ newΔ
    with regA ← ∋:=-⊢r (s-env-in s) inΓ
    with ⟨ pA , uppA ⟩ ← ⊢r-◀^-↑ty-surjective regA newΔ
    = s-svar-term (∋:=-strengthen^-reg (s-env-in s) inΓ newΓ uppA) (s-strengthen^ s newΓ newΓ uppA (↑ty-arr upB upB₁) (↑tyᶜ-e up-e upΣ))
  s-strengthen^ (s-evar-infers infs inst) newΓ newΔ ↑ty-var upB (↑tyᶜ-e up-e upΣ)
    = s-evar-infers (infs-strengthen^ infs (◀^-𝕣 newΓ) upB (↑tyᶜ-e up-e upΣ)) (inst-strengthen^ inst newΓ newΔ upB)

  s-strengthen^0 : Γ ,^ ⊢ A' ≤⁺ Σ' ⊣ Δ ,^ ↪ B'
                   → ↑ty0 B ⇘ B'
                   → ↑ty0 A ⇘ A'
                   → ↑tyᶜ0 Σ ⇘ Σ'
                   → Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
  s-strengthen^0 s upB upA upΣ = s-strengthen^ s ◀Z ◀Z upA upB upΣ
